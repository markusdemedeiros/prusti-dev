// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    borrow::Cow,
    fmt::{Debug, Display, Formatter, Result},
};

use derive_more::{Deref, DerefMut};
use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowData,
        consumers::{BorrowIndex, OutlivesConstraint, RichLocation},
    },
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    dataflow::fmt::DebugWithContext,
    index::{bit_set::BitSet, IndexVec},
    middle::{
        mir::{
            interpret::{ConstValue, GlobalAlloc, Scalar},
            visit::Visitor, BorrowKind,
            BasicBlock, ConstraintCategory, Local, Location, Operand, Place as MirPlace, Rvalue,
            Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE, ConstantKind,
        },
        ty::{GenericArgKind, RegionVid, TyKind, ParamEnv},
    },
};

use crate::{
    coupling_graph::{region_info::map::{RegionKind, Promote}, CgContext, coupling::{CouplingOp, Block}},
    free_pcs::{
        engine::FreePlaceCapabilitySummary, CapabilityLocal, CapabilityProjections, RepackOp, CapabilityKind,
    },
    utils::{r#const::ConstEval, Place, PlaceRepacker},
};

use super::{
    engine::{BorrowDelta, CouplingGraph},
    graph::{Graph, Node},
};

#[derive(Clone)]
pub struct Cg<'a, 'tcx> {
    pub id: Option<Location>,
    pub is_pre: bool,
    pub cgx: &'a CgContext<'a, 'tcx>,

    pub(crate) live: BitSet<BorrowIndex>,
    pub version: FxHashMap<BasicBlock, usize>,
    pub dot_node_filter: fn(&RegionKind<'_>) -> bool,
    pub dot_edge_filter: fn(&RegionKind<'_>, &RegionKind<'_>) -> bool,
    pub top_crates: bool,

    pub graph: Graph<'tcx>,

    pub couplings: Vec<CouplingOp>,
    pub touched: FxHashSet<RegionVid>,
}

impl Debug for Cg<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_struct("Graph")
            .field("id", &self.id)
            .field("version", &self.version)
            // .field("nodes", &self.graph)
            .finish()
    }
}

impl PartialEq for Cg<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.graph == other.graph
    }
}
impl Eq for Cg<'_, '_> {}

impl<'a, 'tcx> DebugWithContext<CouplingGraph<'a, 'tcx>> for Cg<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        _ctxt: &CouplingGraph<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        for op in &self.couplings {
            writeln!(f, "{op}")?;
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a> Cg<'a, 'tcx> {
    pub fn static_region(&self) -> RegionVid {
        self.cgx.region_info.static_region
    }
    pub fn function_region(&self) -> RegionVid {
        self.cgx.region_info.function_region
    }

    #[tracing::instrument(name = "Cg::new", level = "trace", skip_all)]
    pub fn new(cgx: &'a CgContext<'a, 'tcx>, top_crates: bool) -> Self {
        let graph = Graph {
            nodes: IndexVec::from_elem_n(Node::new(), cgx.region_info.map.region_len()),
            static_regions: FxHashSet::from_iter([cgx.region_info.static_region]),
        };

        let live = BitSet::new_empty(cgx.facts2.borrow_set.location_map.len());
        Self {
            id: None,
            is_pre: true,
            cgx,
            live,
            version: FxHashMap::default(),
            dot_node_filter: |_| true,
            dot_edge_filter: |_, _| true,
            top_crates,
            graph,
            couplings: Vec::new(),
            touched: FxHashSet::default(),
        }
    }
    pub fn initialize_start_block(&mut self) {
        for c in &self.cgx.outlives_info.local_constraints {
            self.outlives(*c);
        }
        for c in &self.cgx.outlives_info.universal_local_constraints {
            self.outlives(*c);
        }
        for &(sup, sub) in &self.cgx.outlives_info.universal_constraints {
            self.outlives_placeholder(sup, sub);
        }
        for &const_region in self.cgx.region_info.map.const_regions() {
            self.outlives_static(const_region);
        }
        // Remove all locals without capabilities from the initial graph
        self.kill_shared_borrows_on_place(None, RETURN_PLACE.into());
        for local in self.cgx.rp.body().vars_and_temps_iter() {
            self.kill_shared_borrows_on_place(None, local.into());
        }
    }
    pub fn max_version(&self) -> usize {
        self.version.values().copied().max().unwrap_or_default()
    }

    pub(crate) fn outlives(&mut self, c: OutlivesConstraint<'tcx>) {
        let new = self.graph.outlives(c);
        self.outlives_op(new)
    }
    pub(crate) fn outlives_static(&mut self, r: RegionVid) {
        let static_region = self.static_region();
        if r == static_region {
            return;
        }
        self.outlives_placeholder(r, static_region)
    }
    pub(crate) fn outlives_placeholder(&mut self, r: RegionVid, placeholder: RegionVid) {
        let new = self.graph.outlives_placeholder(r, placeholder);
        self.outlives_op(new)
    }
    #[tracing::instrument(name = "Cg::outlives_op", level = "trace", skip(self))]
    fn outlives_op(&mut self, op: Option<(RegionVid, RegionVid)>) {
        if let Some(block) = op.and_then(|c| self.outlives_to_block(c)) {
            self.couplings.push(CouplingOp::Add(block));
        }
    }

    // TODO: remove
    pub(crate) fn outlives_to_block(&self, op: (RegionVid, RegionVid)) -> Option<Block> {
        let (sup, sub) = op;
        let (sup_info, sub_info) = (self.cgx.region_info.map.get(sup), self.cgx.region_info.map.get(sub));
        if sub_info.is_borrow() || (sub_info.universal() && sup_info.local()) {
            None
        } else {
            Some(Block { sup, sub, })
        }
    }
    #[tracing::instrument(name = "Cg::remove", level = "trace", skip(self))]
    pub(crate) fn remove(&mut self, r: RegionVid, l: Option<Location>) {
        let remove = self.graph.remove(r);
        if let Some((removed, rejoins)) = remove {
            let rejoins = rejoins.into_iter().flat_map(|c| self.outlives_to_block(c)).collect();
            self.couplings.push(CouplingOp::Remove(removed, rejoins));
        }
    }
    #[tracing::instrument(name = "Cg::kill_borrow", level = "trace", skip(self))]
    pub(crate) fn kill_borrow(&mut self, data: &BorrowData<'tcx>) {
        let remove = self.graph.kill_borrow(data);
        for removed in remove.into_iter().rev() {
            self.couplings.push(CouplingOp::Remove(removed, Vec::new()));
        }
    }
    pub (crate) fn reset_ops(&mut self) {
        for c in self.couplings.drain(..) {
            self.touched.extend(c.regions());
        }
    }

    #[tracing::instrument(name = "get_associated_place", level = "trace", skip(self), ret)]
    pub(crate) fn get_kind(&self, r: RegionVid) -> &RegionKind<'tcx> {
        self.cgx.region_info.map.get(r)
    }
    #[tracing::instrument(name = "is_unknown_local", level = "trace", skip(self), ret)]
    pub(crate) fn is_unknown_local(&self, r: RegionVid) -> bool {
        self.get_kind(r).is_unknown_local()
    }

    #[tracing::instrument(name = "handle_kills", level = "debug", skip(self))]
    pub fn handle_kills(
        &mut self,
        delta: &BorrowDelta,
        oos: Option<&Vec<BorrowIndex>>,
        location: Location,
    ) {
        let input_facts = self.cgx.facts.input_facts.borrow();
        let input_facts = input_facts.as_ref().unwrap();
        let location_table = self.cgx.facts.location_table.borrow();
        let location_table = location_table.as_ref().unwrap();

        for bi in delta.cleared.iter() {
            let data = &self.cgx.facts2.borrow_set[bi];
            // println!("killed: {r:?} {killed:?} {l:?}");
            if oos.map(|oos| oos.contains(&bi)).unwrap_or_default() {
                if self.graph.static_regions.contains(&data.region) {
                    self.output_to_dot("log/coupling/kill.dot", true);
                }
                assert!(
                    !self.graph.static_regions.contains(&data.region),
                    "{data:?} {location:?} {:?}",
                    self.graph.static_regions
                );
                self.kill_borrow(data);
            } else {
                self.remove(data.region, Some(location));
            }

            // // TODO: is this necessary?
            // let local = data.borrowed_place.local;
            // for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
            //     // println!("killed region: {region:?}");
            //     state.output_to_dot("log/coupling/kill.dot");
            //     let removed = state.remove(region, location, true, false);
            //     // assert!(!removed, "killed region: {region:?} at {location:?} (local: {local:?})");
            // }
        }

        if let Some(oos) = oos {
            for &bi in oos {
                // What is the difference between the two (oos)? It's that `delta.cleared` may kill it earlier than `oos`
                // imo we want to completely disregard `oos`. (TODO)
                // assert!(delta.cleared.contains(bi), "Cleared borrow not in out of scope: {:?} vs {:?} (@ {location:?})", delta.cleared, oos);
                if delta.cleared.contains(bi) {
                    continue;
                }

                let data = &self.cgx.facts2.borrow_set[bi];
                self.kill_borrow(data);

                // // TODO: is this necessary?
                // let local = data.assigned_place.local;
                // for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
                //     // println!("IHUBJ local: {local:?} region: {region:?}");
                //     let removed = state.remove(region, location, true, false);
                //     assert!(!removed);
                // }
            }
        }
    }

    #[tracing::instrument(name = "handle_outlives", level = "debug", skip(self))]
    pub fn handle_outlives(&mut self, location: Location, assigns_to: Option<MirPlace<'tcx>>) {
        let local = assigns_to.map(|a| a.local);
        for &c in self
            .cgx
            .outlives_info
            .pre_constraints(location, local, &self.cgx.region_info)
        {
            self.outlives(c);
        }
        if let Some(place) = assigns_to {
            self.kill_shared_borrows_on_place(Some(location), place);
        }
        for &c in self
            .cgx
            .outlives_info
            .post_constraints(location, local, &self.cgx.region_info)
        {
            self.outlives(c);
        }
    }

    #[tracing::instrument(name = "kill_shared_borrows_on_place", level = "debug", skip(self))]
    pub fn kill_shared_borrows_on_place(&mut self, location: Option<Location>, place: MirPlace<'tcx>) {
        let Some(local) = place.as_local() else {
            // Only remove nodes if assigned to the entire local (this is what rustc allows too)
            return;
        };
        for region in self.cgx.region_info.map.all_regions() {
            if self.cgx.region_info.map.for_local(region, local) {
                self.remove(region, location);
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for Cg<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        match operand {
            Operand::Copy(_) => (),
            &Operand::Move(place) => {
                self.kill_shared_borrows_on_place(Some(location), place);
            }
            Operand::Constant(_) => (),
        }
    }
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);
        match &statement.kind {
            StatementKind::AscribeUserType(box (p, _), _) => {
                for &c in self
                    .cgx
                    .outlives_info
                    .type_ascription_constraints
                    .iter()
                    .filter(|c| {
                        self.cgx.region_info.map.for_local(c.sup, p.local)
                            || self.cgx.region_info.map.for_local(c.sub, p.local)
                    })
                {
                    self.outlives(c);
                }
            }
            _ => (),
        }
    }
}

impl<'tcx> Cg<'_, 'tcx> {
    #[tracing::instrument(name = "Regions::merge_for_return", level = "trace")]
    pub fn merge_for_return(&mut self, location: Location) {
        let regions: Vec<_> = self.graph.all_nodes().map(|(r, _)| r).collect();
        for r in regions {
            let kind = self.cgx.region_info.map.get(r);
            match kind {
                RegionKind::Static
                | RegionKind::Param(_)
                | RegionKind::UnknownUniversal
                | RegionKind::Function => continue,
                RegionKind::Place { local, promoted: Promote::NotPromoted, .. } => {
                    if local.index() > self.cgx.rp.body().arg_count {
                        self.output_to_dot("log/coupling/error.dot", true);
                        panic!("{r:?} ({location:?}) {:?}", self.graph.nodes[r]);
                    }
                }
                RegionKind::Borrow(_, Promote::NotPromoted) => {
                    // Should not have borrows left
                    self.output_to_dot("log/coupling/error.dot", true);
                    panic!("{r:?} {:?}", self.graph.nodes[r]);
                }
                // Ignore (and thus delete) early/late bound (mostly fn call) regions
                RegionKind::UnusedReturnBug(..) => unreachable!(),
                RegionKind::Place { promoted: Promote::Promoted(..), .. } => (),
                RegionKind::Borrow(_, Promote::Promoted(..)) => (),
                RegionKind::ConstRef(..) => (),
                RegionKind::EarlyBound(..) => (),
                RegionKind::LateBound { .. } => (),
                RegionKind::Placeholder(..) => (),
                RegionKind::MiscLocal => (),
                RegionKind::ProjectionAnnotation(..) => (),
                RegionKind::OtherAnnotation(..) => (),
                // Skip unknown empty nodes, we may want to figure out how to deal with them in the future
                RegionKind::UnknownLocal => (),
            }
            self.remove(r, None);
        }
    }
    pub fn output_to_dot<P: AsRef<std::path::Path>>(&self, path: P, error: bool) {
        if cfg!(debug_assertions) && (!self.top_crates || error) {
            std::fs::create_dir_all("log/coupling/individual").unwrap();
            let mut f = std::fs::File::create(path).unwrap();
            dot::render(self, &mut f).unwrap();
        }
    }
}

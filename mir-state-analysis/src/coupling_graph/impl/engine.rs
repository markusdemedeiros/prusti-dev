// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cell::RefCell;

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    data_structures::fx::{FxIndexMap, FxHashSet},
    borrowck::{
        borrow_set::{BorrowData, TwoPhaseActivation},
        consumers::{Borrows, BorrowIndex, RichLocation, OutlivesConstraint, PlaceConflictBias, places_conflict, calculate_borrows_out_of_scope_at_location},
    },
    dataflow::{Analysis, AnalysisDomain, ResultsCursor},
    index::{bit_set::{BitSet, HybridBitSet}, Idx},
    middle::{
        mir::{
            TerminatorKind, Operand, ConstantKind, StatementKind, Rvalue,
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Place, Location, Statement, Terminator, TerminatorEdges, RETURN_PLACE,
        },
        ty::{RegionVid, TyCtxt},
    },
};

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, Fpcs},
    utils::PlaceRepacker, coupling_graph::cg::{Graph, Node},
};

use super::{cg::{EdgeInfo}, shared_borrow_set::SharedBorrowSet, CgContext};

#[tracing::instrument(name = "draw_dots", level = "debug", skip(c))]
pub(crate) fn draw_dots<'tcx, 'a>(mut c: ResultsCursor<'_, 'tcx, CoupligGraph<'a, 'tcx>>) {
    let mut graph = Vec::new();
    let body = c.body();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        c.seek_to_block_start(block);
        let mut g = c.get().clone();
        g.id = Some(format!("{block:?}_pre"));
        dot::render(&g, &mut graph).unwrap();
        for statement_index in 0..body.terminator_loc(block).statement_index+1 {
            c.seek_after_primary_effect(Location { block, statement_index });
            g = c.get().clone();
            g.id = Some(format!("{block:?}_{statement_index}"));
            dot::render(&g, &mut graph).unwrap();
        }
        if let TerminatorKind::Return = data.terminator().kind {
            g.skip_empty_nodes = true;
            g.id = Some(format!("{block:?}_ret"));
            dot::render(&g, &mut graph).unwrap();
        }
    }
    let combined = std::str::from_utf8(graph.as_slice()).unwrap().to_string();

    let regex = regex::Regex::new(r"digraph (([^ ])+) \{").unwrap();
    let combined = regex.replace_all(&combined, "subgraph cluster_$1 {\n    label = \"$1\"");

    std::fs::write("log/coupling/all.dot", format!("digraph root {{\n{combined}}}")).expect("Unable to write file");
}

pub(crate) struct CoupligGraph<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
    pub(crate) facts: &'a BorrowckFacts,
    pub(crate) facts2: &'a BorrowckFacts2<'tcx>,
    pub(crate) flow_borrows: RefCell<ResultsCursor<'a, 'tcx, Borrows<'a, 'tcx>>>,
    pub(crate) out_of_scope: FxIndexMap<Location, Vec<BorrowIndex>>,
    pub(crate) printed_dot: FxHashSet<String>,
    pub(crate) cgx: &'a CgContext<'a, 'tcx>,
}
impl<'a, 'tcx> CoupligGraph<'a, 'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, facts: &'a BorrowckFacts, facts2: &'a BorrowckFacts2<'tcx>, cgx: &'a CgContext<'a, 'tcx>) -> Self {
        if cfg!(debug_assertions) {
            std::fs::remove_dir_all("log/coupling").ok();
            std::fs::create_dir_all("log/coupling/individual").unwrap();
        }

        let repacker = PlaceRepacker::new(body, tcx);
        let regioncx = &*facts2.region_inference_context;
        let borrow_set = &*facts2.borrow_set;
        let out_of_scope = calculate_borrows_out_of_scope_at_location(body, regioncx, borrow_set);
        let flow_borrows = Borrows::new(tcx, body, regioncx, borrow_set)
            .into_engine(tcx, body)
            .pass_name("borrowck")
            .iterate_to_fixpoint()
            .into_results_cursor(body);
        let printed_dot = FxHashSet::default();
        CoupligGraph { repacker, facts, facts2, flow_borrows: RefCell::new(flow_borrows), out_of_scope, printed_dot, cgx }
    }

    #[tracing::instrument(name = "handle_kills", level = "debug", skip(self))]
    fn handle_kills(&self, state: &mut Graph<'_, 'tcx>, delta: &BorrowDelta, location: Location) {
        let input_facts = self.facts.input_facts.borrow();
        let input_facts = input_facts.as_ref().unwrap();
        let location_table = self.facts.location_table.borrow();
        let location_table = location_table.as_ref().unwrap();

        // let input_facts = self.facts2.region_inference_context.borrow();

        let oos = self.out_of_scope.get(&location);

        for bi in delta.cleared.iter() {
            let data = &self.facts2.borrow_set[bi];
            // TODO: remove if the asserts below pass:
            let (r, _, l) = input_facts.loan_issued_at.iter().find(
                |(_, b, _)| bi == *b
            ).copied().unwrap();
            let l = rich_to_loc(location_table.to_location(l));
            assert_eq!(r, data.region);
            assert_eq!(l, data.reserve_location);

            // println!("killed: {r:?} {killed:?} {l:?}");
            if oos.map(|oos| oos.contains(&bi)).unwrap_or_default() {
                state.kill_borrow(data);
            } else {
                state.remove(data.region, location);
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
                // What is the difference between the two (oos)?
                assert!(delta.cleared.contains(bi), "Cleared borrow not in out of scope: {:?} vs {:?} (@ {location:?})", delta.cleared, oos);
                if delta.cleared.contains(bi) {
                    continue;
                }

                let data = &self.facts2.borrow_set[bi];
                // TODO: remove if the asserts below pass:
                let (r, _, l) = input_facts.loan_issued_at.iter().find(
                    |(_, b, _)| bi == *b
                ).copied().unwrap();
                let l = rich_to_loc(location_table.to_location(l));
                assert_eq!(r, data.region);
                assert_eq!(l, data.reserve_location);

                state.kill_borrow(data);

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

    fn get_constraints_for_loc(&self, location: Option<Location>) -> impl Iterator<Item = OutlivesConstraint<'tcx>> + '_ {
        self.facts2.region_inference_context.outlives_constraints().filter(
            move |c| c.locations.from_location() == location
        )
    }

    #[tracing::instrument(name = "handle_outlives", level = "debug", skip(self))]
    fn handle_outlives(&self, state: &mut Graph<'_, 'tcx>, delta: &BorrowDelta, location: Location) {
        for c in self.get_constraints_for_loc(Some(location)) {
            state.outlives(c);
        }
    }

    #[tracing::instrument(name = "kill_shared_borrows_on_place", level = "debug", skip(self))]
    fn kill_shared_borrows_on_place(&self, location: Location, state: &mut Graph<'_, 'tcx>, place: Place<'tcx>) {
        // let other_borrows_of_local = state
        //     .shared_borrows
        //     .local_map
        //     .get(&place.local)
        //     .into_iter()
        //     .flat_map(|bs| bs.iter())
        //     .copied()
        //     .map(|idx| &state.shared_borrows.location_map[idx.as_usize()]);
        // let definitely_conflicting_borrows = other_borrows_of_local.filter(|d| {
        //     places_conflict(
        //         self.repacker.tcx(),
        //         self.repacker.body(),
        //         d.borrowed_place,
        //         place,
        //         PlaceConflictBias::NoOverlap,
        //     )
        // });
        // for data in definitely_conflicting_borrows {
        //     state.remove(data.region, true);
        // }
        let Some(local) = place.as_local() else {
            // Only remove nodes if assigned to the entire local (this is what rustc allows too)
            return
        };
        // println!("Killing: {local:?}");

        // let was_shared_borrow_from = self.cgx.sbs.local_map.contains_key(&local);
        // let was_shared_borrow_to = self.cgx.sbs.location_map.values().find(|bd| bd.assigned_place.local == local);
        // if !was_shared_borrow_from && was_shared_borrow_to.is_none() {
        //     println!("early ret: {:?}", self.cgx.sbs.local_map);
        //     return;
        // }
        // println!("killing");

        // Also remove any overwritten borrows locals
        for (&region, _) in state.cgx.region_map.iter().filter(|(_, p)| p.place.local == local) {
            // println!("Killing local: {local:?}: {region:?}");

            // TODO: could set `remove_dangling_children` to true here
            state.remove(region, location);
        }
    }

    /// This is the hack we use to make a `fn foo<'a>(x: &'a _, y: &'a _, ...) -> &'a _` look like
    /// `fn foo<'a: 'c, 'b: 'c, 'c>(x: &'a _, y: &'b _, ...) -> &'c _` to the analysis.
    #[tracing::instrument(name = "ignore_outlives", level = "debug", skip(self), ret)]
    fn ignore_outlives(&self, c: OutlivesConstraint<'tcx>) -> bool {
        let arg_count = self.repacker.body().arg_count;
        let sup = self.cgx.region_map.get(&c.sup);
        let sub = self.cgx.region_map.get(&c.sub);
        match (sup, sub) {
            // If `projects_exactly_one_deref` then it must be the `'a` region of a `x: &'a ...`, rather than being nested deeper withing the local
            (_, Some(sub)) => {
                sub.place.projects_exactly_one_deref()
                    && sub.place.local.index() <= arg_count
                    && sub.place.local != RETURN_PLACE
            }
            // (Some(sup), Some(sub)) => {
            //     if !(sup.place.projects_exactly_one_deref()
            //         && sub.place.projects_exactly_one_deref()
            //         && sup.place.local.index() <= arg_count
            //         && sub.place.local.index() <= arg_count) {
            //         return false;
            //     }
            //     debug_assert_ne!(sup.place.local, sub.place.local);
            //     sub.place.local != RETURN_PLACE
            // }
            _ => false,
        }
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for CoupligGraph<'a, 'tcx> {
    type Domain = Graph<'a, 'tcx>;
    const NAME: &'static str = "coupling_graph";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        Graph::new(self.repacker, self.facts, self.facts2, self.cgx)
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        // // Sanity check (already done when creating region to place map)
        // if cfg!(debug_assertions) {
        //     let input_facts = self.facts.input_facts.borrow();
        //     let use_of_var_derefs_origin = &input_facts.as_ref().unwrap().use_of_var_derefs_origin;
        //     // Each region should only have a single associated local
        //     for (_, r) in use_of_var_derefs_origin {
        //         assert!(use_of_var_derefs_origin.iter().filter(|(_, ro)| r == ro).count() <= 1, "{use_of_var_derefs_origin:?}");
        //     }
        // }

        println!("body: {body:#?}");
        println!("\ninput_facts: {:?}", self.facts.input_facts);
        println!("output_facts: {:#?}\n", self.facts.output_facts);
        println!("location_map: {:#?}\n", self.facts2.borrow_set.location_map);
        println!("activation_map: {:#?}\n", self.facts2.borrow_set.activation_map);
        println!("local_map: {:#?}\n", self.facts2.borrow_set.local_map);
        println!("region_inference_context: {:#?}\n", self.facts2.region_inference_context.outlives_constraints().collect::<Vec<_>>());
        // println!("locals_state_at_exit: {:#?}\n", self.facts2.borrow_set.locals_state_at_exit);
        let lt = self.facts.location_table.borrow();
        let lt = lt.as_ref().unwrap();
        for pt in lt.all_points() {
            println!("{pt:?} -> {:?} ({:?})", lt.to_location(pt), ""); //, self.facts.output_facts.origins_live_at(pt));
        }
        println!("out_of_scope: {:?}", self.out_of_scope);
        println!("region_map: {:#?}\n", self.cgx.region_map);
    }
}

impl<'a, 'tcx> Analysis<'tcx> for CoupligGraph<'a, 'tcx> {
    #[tracing::instrument(name = "apply_statement_effect", level = "debug", skip(self))]
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        let l = format!("{:?}", location).replace('[', "_").replace(']', "");
        // println!("Location: {l}");
        state.id = Some(l.clone());

        if location.statement_index == 0 {
            state.version += 1;
            assert!(state.version < 10);

            // println!("\nblock: {:?}", location.block);
            if cfg!(debug_assertions) && !self.repacker.body().basic_blocks[location.block].is_cleanup {
                state.output_to_dot(format!("log/coupling/individual/{l}_v{}_start.dot", state.version));
            }
            self.flow_borrows.borrow_mut().seek_to_block_start(location.block);
            state.live = self.flow_borrows.borrow().get().clone();
        }
        self.flow_borrows.borrow_mut().seek_after_primary_effect(location);
        let other = self.flow_borrows.borrow().get().clone();
        // print!("{statement:?} ({other:?}):");
        let delta = calculate_diff(&other, &state.live);

        self.handle_kills(state, &delta, location);
        
        match statement.kind {
            StatementKind::Assign(box (assigned_place, ref lhs)) => {
                self.kill_shared_borrows_on_place(location, state, assigned_place);
                if let Rvalue::Use(Operand::Constant(c)) = lhs {
                    // println!("Checking {:?} vs {curr_loc:?}", self.facts2.region_inference_context.outlives_constraints().map(|c| format!("{:?}", c.locations)).collect::<Vec<_>>());
                    for c in self.get_constraints_for_loc(Some(location)) {
                        // println!("Got one: {c:?}");
                        state.outlives_static(c.sub, location);
                    }
                }
            }
            // If a local was only moved out of and not reborrowed, it's region is never killed officially
            StatementKind::StorageDead(local) => {
                self.kill_shared_borrows_on_place(location, state, Place::from(local));

                // let input_facts = self.facts.input_facts.borrow();
                // let input_facts = input_facts.as_ref().unwrap();
                // for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
                //     // println!("killed region manually: {region:?}");
                //     state.remove(region, true);
                // }
                // let to_rem: Vec<_> = state.shared_borrows.iter().filter(|(_, data)| data.borrowed_place.local == local).map(|(_, data)| data.region).collect();
                // for region in to_rem {
                //     // println!("killed region manually: {region:?}");
                //     state.remove(region, true);
                // }
            }
            _ => (),
        }
        // if cfg!(debug_assertions) && !self.repacker.body().basic_blocks[location.block].is_cleanup {
        //     state.output_to_dot(format!("log/coupling/individual/{l}_v{}_mid.dot", state.version));
        // }
        self.handle_outlives(state, &delta, location);
        state.live = other;
        // println!();

        if cfg!(debug_assertions) && !self.repacker.body().basic_blocks[location.block].is_cleanup {
            state.output_to_dot(format!("log/coupling/individual/{l}_v{}.dot", state.version));
        }
    }

    #[tracing::instrument(name = "apply_statement_effect", level = "debug", skip(self))]
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let l = format!("{:?}", location).replace('[', "_").replace(']', "");
        // println!("Location: {l}");
        state.id = Some(l.clone());

        if location.statement_index == 0 {
            state.version += 1;
            assert!(state.version < 10);

            // println!("\nblock: {:?}", location.block);
            if cfg!(debug_assertions) && !self.repacker.body().basic_blocks[location.block].is_cleanup {
                state.output_to_dot(format!("log/coupling/individual/{l}_v{}_start.dot", state.version));
            }
            self.flow_borrows.borrow_mut().seek_to_block_start(location.block);
            state.live = self.flow_borrows.borrow().get().clone();
        }
        self.flow_borrows.borrow_mut().seek_after_primary_effect(location);
        let other = self.flow_borrows.borrow().get().clone();
        // if let TerminatorKind::Call { func, args, destination, target, fn_span, .. } = &terminator.kind {
        //     if let Operand::Constant(c) = func {
        //         println!("user_ty: {:?}", c.user_ty);
        //         println!("call: {:?}", c.literal);
        //         if let ConstantKind::Val(cv, ty) = c.literal {
        //             println!("val: {:?}", cv);
        //             println!("ty: {:?}", ty);
        //         }
        //         println!("\n\n\ncall: {:?}", func);
        //     }
        //     for arg in args {
        //         match arg {
        //             Operand::Copy(a) => println!("copy ({arg:?}): {:?}", a),
        //             Operand::Move(b) => println!("move ({arg:?}): {:?}", b),
        //             Operand::Constant(c) => println!("const ({arg:?}): {:?}", c.literal),
        //         }
        //     }
        // }
        // print!("{terminator:?} ({other:?}):");
        let delta = calculate_diff(&other, &state.live);
        self.handle_kills(state, &delta, location);
        self.handle_outlives(state, &delta, location);
        state.live = other;
        if let TerminatorKind::Return = &terminator.kind {
            if cfg!(debug_assertions) && !self.repacker.body().basic_blocks[location.block].is_cleanup {
                state.output_to_dot(format!("log/coupling/individual/{l}_v{}_pre.dot", state.version));
            }

            // Pretend we have a storage dead for all `always_live_locals` other than the args/return
            for l in self.repacker.always_live_locals_non_args().iter() {
                self.kill_shared_borrows_on_place(location, state, l.into());
            }
            // Kill all the intermediate borrows, i.e. turn `return -> x.0 -> x` into `return -> x`
            for r in self.facts2.borrow_set.location_map.values().chain(self.cgx.sbs.location_map.values()) {
                state.remove(r.region, location);
            }

            for c in self.get_constraints_for_loc(None).filter(|c| !self.ignore_outlives(*c)) {
                state.outlives(c);
            }
            state.merge_for_return();
        }
        // println!();

        if cfg!(debug_assertions) && !self.repacker.body().basic_blocks[location.block].is_cleanup {
            state.output_to_dot(format!("log/coupling/individual/{l}_v{}.dot", state.version));
        }
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}

#[derive(Debug)]
struct BorrowDelta {
    set: HybridBitSet<BorrowIndex>,
    cleared: HybridBitSet<BorrowIndex>,
}

fn calculate_diff(curr: &BitSet<BorrowIndex>, old: &BitSet<BorrowIndex>) -> BorrowDelta {
    let size = curr.domain_size();
    assert_eq!(size, old.domain_size());

    let mut set_in_curr = HybridBitSet::new_empty(size);
    let mut cleared_in_curr = HybridBitSet::new_empty(size);

    for i in (0..size).map(BorrowIndex::new) {
        match (curr.contains(i), old.contains(i)) {
            (true, false) => set_in_curr.insert(i),
            (false, true) => cleared_in_curr.insert(i),
            _ => continue,
        };
    }
    BorrowDelta {
        set: set_in_curr,
        cleared: cleared_in_curr,
    }
}

fn rich_to_loc(l: RichLocation) -> Location {
    match l {
        RichLocation::Start(l) => l,
        RichLocation::Mid(l) => l,
    }
}

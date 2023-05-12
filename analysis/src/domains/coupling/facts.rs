// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    abstract_interpretation::AnalysisResult,
    mir_utils::{
        self, expect_mid_location, expect_start_location, get_borrowed_from_place,
        get_storage_dead, maximally_pack, mir_kind_at, Place, PlaceImpl,
    },
};
use prusti_rustc_interface::{
    borrowck::{
        consumers::{RichLocation, RustcFacts},
        BodyWithBorrowckFacts,
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{BorrowKind, Location, Operand, Rvalue, StatementKind},
        ty::TyCtxt,
    },
    polonius_engine::FactTypes,
};
use std::collections::{BTreeMap, BTreeSet};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;

/// Issue of a new loan. The assocciated region should represent a borrow temporary.
pub(crate) type LoanIssues<'tcx> = FxHashMap<Location, (Region, Place<'tcx>)>;
// pub(crate) type OriginPacking<'tcx> = FxHashMap<PointIndex, Vec<(Region, OriginLHS<'tcx>)>>;
pub(crate) type GraphOperations<'tcx> = FxHashMap<Location, Vec<IntroStatement<'tcx>>>;
pub(crate) type DeltaLeaves<'tcx> =
    FxHashMap<Location, (Vec<OriginLHS<'tcx>>, Vec<OriginLHS<'tcx>>)>; // fixme: this should be capabilities
pub(crate) type OriginContainsLoanAt = FxHashMap<PointIndex, BTreeMap<Region, BTreeSet<Loan>>>;
pub(crate) type SubsetsAt = FxHashMap<PointIndex, BTreeMap<Region, BTreeSet<Region>>>;
pub(crate) type OriginExpiresAt = FxHashMap<Location, BTreeSet<Region>>;

/// Struct containing lookups for all the Polonius facts
pub struct FactTable<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,

    /// Issue of a loan, into it's issuing origin, and a loan of a place
    pub(crate) loan_issues: LoanIssues<'tcx>,

    /// Interpretation of regions in terms of places and temporaries
    pub(crate) origins: OriginPlaces<'tcx>,

    /// Steps the graph needs to take at each point.
    /// We assume that we can repack the PCS (incl. adding graph edges) _before_ doing all
    /// the graph ops. We also assume that the Hoare triple for the statement will encompass
    /// the change in nodes in the graph.
    /// If either of these are untrue, I think we'll need to move to something like MicroMir here
    /// in order to properly interleave these effects.
    pub(crate) graph_operations: GraphOperations<'tcx>,

    /// Hoare triple associated with the change in leaves
    /// We precompute this, right now we use it to ensure we have everything packed in the right state.
    /// In the real version, this should be a dynamic check that
    ///  delta_leaves <: delta_pcs
    /// As in, all the capabilities consumed by the graph are also consumed by the statement
    /// and likewise with all capabilities released.
    pub(crate) delta_leaves: DeltaLeaves<'tcx>,

    /// Points where origins go from live to not live0
    pub(crate) origin_expires_before: OriginExpiresAt,

    /// Analouges of polonius facts
    pub(crate) origin_contains_loan_at: OriginContainsLoanAt,
    pub(crate) subsets_at: SubsetsAt,
}

impl<'tcx> FactTable<'tcx> {
    /// Default unpopulated fact table
    fn default_from_tcx(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
            loan_issues: Default::default(),
            origins: OriginPlaces {
                map: Default::default(),
                tcx,
            },
            origin_contains_loan_at: Default::default(),
            delta_leaves: Default::default(),
            origin_expires_before: Default::default(),
            graph_operations: Default::default(),
            subsets_at: Default::default(),
        }
    }

    /// New populated fact table
    pub fn new(mir: &BodyWithBorrowckFacts<'tcx>, tcx: TyCtxt<'tcx>) -> AnalysisResult<Self> {
        println!("{:#?}", mir.body.basic_blocks);
        let mut working_table = Self::default_from_tcx(tcx);
        Self::compute_loan_issues(mir, &mut working_table)?;
        Self::insert_storage_dead_kills(mir, &mut working_table);
        Self::collect_loan_killed_at(mir, &mut working_table);
        Self::characterize_subset_base(&mut working_table, mir)?;
        Self::collect_origin_contains_loan_at(mir, &mut working_table);
        Self::collect_subsets_at(mir, &mut working_table);
        Self::collect_origin_expiries(mir, &mut working_table);
        println!("[fact table]  {:#?}", working_table);
        return Ok(working_table);
    }

    /// Collect all facts due to loan issues
    /// Before computation:
    ///     - Nothing needs to be known
    ///
    /// For each loan_issued_at(issuing_origin, bwx, p):
    ///     - Assert that l is a middle location
    ///     - Assert that the statement is _ = &mut borrowed_from_place;
    ///     - Constrain the LHS of issuing_origin to be bwx
    ///     - Constrain that loan bwx is a borrow from borrowed_from_place at p
    ///
    /// After computation:
    ///     - The origin associated to all loan temporaries is known
    ///     - The borrowed-from place for all loans is known
    fn compute_loan_issues<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) -> AnalysisResult<()> {
        for (issuing_origin, loan, point) in mir.input_facts.loan_issued_at.iter() {
            // Insert facts for the new borrow temporary
            let location = expect_mid_location(mir.location_table.to_location(*point));
            let statement = mir_kind_at(&mir.body, location);
            let borrowed_from_place: mir_utils::Place<'tcx> =
                (*get_borrowed_from_place(&statement, location)?).into();

            Self::check_or_construct_origin(
                working_table,
                &mir.body as &mir::Body,
                OriginLHS::Loan(*loan),
                *issuing_origin,
            )?;
            Self::insert_loan_issue_constraint(
                working_table,
                location,
                *issuing_origin,
                borrowed_from_place,
            );
        }
        Ok(())
    }

    /// Explain the subset_base facts
    /// Before computation:
    ///     - Issuing origins must be charaterized
    ///     - Borrowed-from places must be annotated for all borrows
    ///
    /// For each point p with a collection of subset_base facts:
    ///     - (1) if the place is a loan issue:
    ///         - (1.1) there should be exactly one base superset of the issuing_origin origin
    ///             of the form (issuing_origin, assigning_origin)
    ///             and the statement is _ = &mut assigned_from_place;
    ///     fixme (markus) finish doccumenting this
    ///
    /// After computation:
    fn characterize_subset_base<'mir>(
        working_table: &mut Self,
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> AnalysisResult<()> {
        // Collect subset_base facts into a map indexed by points
        let subset_base_locations: FxHashMap<PointIndex, FxHashSet<(Region, Region)>> = mir
            .input_facts
            .subset_base
            .iter()
            .fold(FxHashMap::default(), |mut acc, (o1, o2, p)| {
                acc.entry(*p).or_default().insert((*o1, *o2));
                acc
            });

        for (point, s) in subset_base_locations.into_iter() {
            // Collect data related to this point
            // Assertion: All of our subset_base facts should take place at a Mid location
            let loc = expect_mid_location(mir.location_table.to_location(point));
            let statement = match mir_kind_at(&mir.body, loc) {
                mir_utils::StatementKinds::Stmt(smt) => smt,
                mir_utils::StatementKinds::Term(_) => {
                    unimplemented!("subset reconstruction can't translate at terminators")
                }
            };
            let issue = match mir
                .input_facts
                .loan_issued_at
                .iter()
                .filter(|p| p.2 == point)
                .collect::<Vec<_>>()[..]
            {
                [] => None,
                [x] => Some(x),
                _ => unimplemented!("subset reconstruction: can't issue multiple loans at a point"),
            };
            let s_match = &(s.iter().collect::<Vec<_>>()[..]);

            // Determine kind of point by pattern matching
            match (s_match, statement, issue) {
                // Case 1: Loan issue of owned data
                (
                    // - Exactly one subset_base fact
                    [(issuing_origin, asgn_to_origin)],
                    // - At a borrow statement
                    StatementKind::Assign(box (
                        asgn_to_place,
                        Rvalue::Ref(
                            _decl_region,
                            BorrowKind::Mut {
                                allow_two_phase_borrow: false,
                            },
                            brw_from_place,
                        ),
                    )),
                    // -  a loan issue into issuing_origin
                    Some((issuing1, bw_index, _)),
                ) if issuing_origin == issuing1 => {
                    // In the CDG, we assign to the deref of a place (not the place itself)
                    let asgn_to_place = working_table.tcx.mk_place_deref(*asgn_to_place);

                    // update the working table's origins: assigned to place
                    Self::check_or_construct_origin(
                        working_table,
                        &mir.body,
                        OriginLHS::Place(asgn_to_place.into()),
                        *asgn_to_origin,
                    )?;
                    // update the working table's origins: loan issue
                    Self::check_or_construct_origin(
                        working_table,
                        &mir.body,
                        OriginLHS::Loan(*bw_index),
                        *issuing_origin,
                    )?;

                    // Impose the semantics for borrows
                    let cur_op = working_table.graph_operations.entry(loc).or_default();
                    cur_op.push(IntroStatement::Borrow(
                        PlaceImpl::from_mir_place(*brw_from_place),
                        *bw_index,
                    ));
                    cur_op.push(IntroStatement::Assign(
                        OriginLHS::Loan(*bw_index),
                        PlaceImpl::from_mir_place(asgn_to_place),
                    ));

                    // Associated Hoare triple
                    working_table.delta_leaves.insert(
                        loc,
                        (
                            [OriginLHS::Place(PlaceImpl::from_mir_place(*brw_from_place))]
                                .into_iter()
                                .collect(),
                            [OriginLHS::Place(PlaceImpl::from_mir_place(asgn_to_place))]
                                .into_iter()
                                .collect(),
                        ),
                    );
                }

                // Case 2: Reborrow
                (
                    // - Exactly two subset_base facts that agree at issuing_origin
                    [(rb_from_origin, issuing_origin), (issuing1, asgn_to_origin)]
                    | [(issuing1, asgn_to_origin), (rb_from_origin, issuing_origin)],
                    // - At a reborrow statement
                    StatementKind::Assign(box (
                        asgn_to_place,
                        Rvalue::Ref(
                            _decl_region,
                            BorrowKind::Mut {
                                allow_two_phase_borrow: false,
                            },
                            rb_from_place,
                        ),
                    )),
                    // -  a loan issue into issuing_origin
                    Some((issuing2, bw_index, _)),
                ) if issuing_origin == issuing1 && issuing_origin == issuing2 => {
                    // In the CDG, we assign to the deref of a place (not the place itself)
                    let asgn_to_place = working_table.tcx.mk_place_deref(*asgn_to_place);
                    let rb_from_place = *rb_from_place;

                    // update the working table's origins: assigned-to place
                    Self::check_or_construct_origin(
                        working_table,
                        &mir.body,
                        OriginLHS::Place(asgn_to_place.into()),
                        *asgn_to_origin,
                    )?;
                    // update the working table's origins: loan issue
                    Self::check_or_construct_origin(
                        working_table,
                        &mir.body,
                        OriginLHS::Loan(*bw_index),
                        *issuing_origin,
                    )?;
                    // // update the working table's origins: reborrowed-from place
                    // Actually we don't want to do this... because we might reborrow from a subplace
                    // Self::check_or_construct_origin(
                    //     working_table,
                    //     &mir.body,
                    //     OriginLHS::Place((*rb_from_place).into()),
                    //     *rb_from_origin,
                    // )?;

                    // Impose the semantics for reborrows
                    let cur_op = working_table.graph_operations.entry(loc).or_default();
                    cur_op.push(IntroStatement::Reborrow(
                        PlaceImpl::from_mir_place(rb_from_place),
                        *bw_index,
                        *rb_from_origin,
                    ));
                    cur_op.push(IntroStatement::Assign(
                        OriginLHS::Loan(*bw_index),
                        PlaceImpl::from_mir_place(asgn_to_place),
                    ));

                    // Associated Hoare triple
                    working_table.delta_leaves.insert(
                        loc,
                        (
                            [OriginLHS::Place(PlaceImpl::from_mir_place(rb_from_place))]
                                .into_iter()
                                .collect(),
                            [OriginLHS::Place(PlaceImpl::from_mir_place(asgn_to_place))]
                                .into_iter()
                                .collect(),
                        ),
                    );
                }

                // Case 3: Move
                //  - at an assignment statement
                (
                    //  - only one subset
                    [(_mv_from_origin, mv_to_origin)],
                    // - an assignment statement
                    StatementKind::Assign(box (
                        mv_to_place,
                        Rvalue::Use(Operand::Move(mv_from_place)),
                    )),
                    None,
                ) => {
                    // In the CDG, we assign to the deref of a place (not the place itself)
                    let mv_from_place = working_table.tcx.mk_place_deref(*mv_from_place);
                    let mv_to_place = working_table.tcx.mk_place_deref(*mv_to_place);

                    // update the working table's origins: assigned-to place
                    Self::check_or_construct_origin(
                        working_table,
                        &mir.body,
                        OriginLHS::Place(mv_to_place.into()),
                        *mv_to_origin,
                    )?;
                    // // update the working table's origins: moved-from place
                    // Actually we don't want to do this... because we might move from a subplace
                    // Self::check_or_construct_origin(
                    //     working_table,
                    //     &mir.body,
                    //     OriginLHS::Place((*mv_from_place).into()),
                    //     *mv_from_origin,
                    // )?;

                    // Impose the semantics for moves
                    let cur_op = working_table.graph_operations.entry(loc).or_default();
                    cur_op.push(IntroStatement::Kill(OriginLHS::Place(
                        PlaceImpl::from_mir_place(mv_to_place),
                    )));

                    cur_op.push(IntroStatement::Assign(
                        OriginLHS::Place(PlaceImpl::from_mir_place(mv_from_place)),
                        PlaceImpl::from_mir_place(mv_to_place),
                    ));

                    // Associated Hoare triple
                    working_table.delta_leaves.insert(
                        loc,
                        (
                            [OriginLHS::Place(PlaceImpl::from_mir_place(mv_from_place))]
                                .into_iter()
                                .collect(),
                            [OriginLHS::Place(PlaceImpl::from_mir_place(mv_to_place))]
                                .into_iter()
                                .collect(),
                        ),
                    );
                }

                // Otherwise, not sure how to interpret the origins.
                _ => unimplemented!(
                    "subset reconstruction unhandled case at {:#?}\n{:#?}\n{:#?}\n",
                    s,
                    statement,
                    issue
                ),
            }
        }
        Ok(())
    }

    /// Lift Polonius facts
    fn collect_origin_contains_loan_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) {
        for (k, v) in mir.output_facts.origin_contains_loan_at.iter() {
            working_table
                .origin_contains_loan_at
                .insert(*k, (*v).to_owned());
        }
    }

    /// For all points, if an origin is in the origin_contains_loan_at fact at that point and not at the next,
    /// it expires. Do we use origin_live_on_entry maybe?
    /// Whatever I'm doing ocla for now.
    fn collect_origin_expiries<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) {
        for (loc_ix, ocla_map) in mir.output_facts.origin_contains_loan_at.iter() {
            if let RichLocation::Start(_) = mir.location_table.to_location(*loc_ix) {
                continue;
            }

            // fixme: really idiotic way to do this. Precompute the successors-- there's probably a MIR helper for this.
            for (_, next_loc_ix) in mir.input_facts.cfg_edge.iter().filter(|(x, _)| x == loc_ix) {
                let next_loc = expect_start_location(mir.location_table.to_location(*next_loc_ix));
                let origin_expiry_entry = working_table
                    .origin_expires_before
                    .entry(next_loc)
                    .or_default();
                let next_live_origins = match mir
                    .output_facts
                    .origin_contains_loan_at
                    .get(next_loc_ix)
                    .map(|x| x.keys().collect::<Vec<_>>())
                {
                    Some(z) => z,
                    None => Vec::default(),
                };
                for origin in ocla_map.keys() {
                    // Check to see if origin is in next_live_origins or not.
                    // If it dies, mark that at the start of the next statement
                    if !next_live_origins.contains(&origin) {
                        origin_expiry_entry.insert(origin.clone());
                    }
                }
            }
        }
    }

    /// Lift Polonius facts
    fn collect_subsets_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) {
        for (l, m) in mir.output_facts.subset.iter() {
            working_table.subsets_at.insert(*l, (*m).to_owned());
        }
    }

    /// Turn all loan_killed_at facts into actual kills in the semantics.
    fn collect_loan_killed_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) {
        // println!("loan_killed_at: {:?}", mir.input_facts.loan_killed_at);
        // Assert that the loan is killed at a Mid only.
        for (l, p) in mir.input_facts.loan_killed_at.iter() {
            let location = expect_mid_location(mir.location_table.to_location(*p));
            let cur_op = working_table.graph_operations.entry(location).or_default();
            cur_op.push(IntroStatement::Kill(OriginLHS::Loan(*l)));
        }
    }

    fn insert_storage_dead_kills<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) {
        for (block, bb_data) in mir.body.basic_blocks.iter_enumerated() {
            for (statement_index, stmt) in bb_data.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                if let StatementKind::StorageDead(l) = stmt.kind {
                    let cur_op = working_table.graph_operations.entry(location).or_default();
                    cur_op.push(IntroStatement::Kill(OriginLHS::Place(l.into())));
                }
            }
        }
    }

    /// Constrain an origin to have a particular LHS, or panic if the constraint conflicts with
    /// an existing origin.
    /// Model: All origins must have a unique cannonical LHS.
    fn check_or_construct_origin<'mir>(
        working_table: &mut Self,
        mir: &mir::Body<'tcx>,
        lhs: OriginLHS<'tcx>,
        origin: Region,
    ) -> AnalysisResult<()> {
        if let Some(real_origin) = working_table.origins.get_origin(mir, lhs.to_owned()) {
            assert_eq!(real_origin, origin);
        } else {
            working_table.origins.new_constraint(mir, origin, lhs);
        }
        Ok(())
    }

    /// Access the origins refered to by the origin_contains_loan_at fact at a point
    /// Model: In calculating at p, all origins_at(p) must be given a signature
    pub fn origins_at(&self, p: &PointIndex) -> AnalysisResult<BTreeSet<Region>> {
        match self.origin_contains_loan_at.get(p) {
            None => panic!("accessing location outside MIR"),
            Some(s) => Ok(s.keys().cloned().collect::<_>()),
        }
    }

    /// Get the storage_dead facts at a location
    /// Model: All get_storage_dead_at(_, p) must be killed between p and successor(p).
    /// Model: Places are only killed between Start and Mid locations
    pub fn get_storage_dead_at<'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        location: PointIndex,
    ) -> Option<Place<'tcx>>
    where
        'tcx: 'mir,
    {
        let rich_location = mir.location_table.to_location(location);
        match rich_location {
            RichLocation::Start(loc) => get_storage_dead(&mir_kind_at(&mir.body, loc), loc),
            RichLocation::Mid(_) => None,
        }
    }

    /// Get the subsets associated with a move at each point
    /// Model: For each (from, to) subset, from is is a subset of to, and to is killed.
    // pub fn get_move_origins_at(&self, location: &PointIndex) -> Vec<(Region, Region)> {
    //     match self.structural_edge.get(location) {
    //         Some(v) => v
    //             .iter()
    //             .filter(|(kind, _, _)| {
    //                 (*kind == SubsetBaseKind::Move) || (*kind == SubsetBaseKind::LoanIssue)
    //             })
    //             .map(|(_, from, to)| (*from, *to))
    //             .collect::<_>(),
    //         None => Vec::default(),
    //     }
    // }

    /// Add a loan_issue constraint to the table
    fn insert_loan_issue_constraint(
        working_table: &mut Self,
        point: Location,
        origin: Region,
        borrowed_from_place: Place<'tcx>,
    ) {
        working_table
            .loan_issues
            .insert(point, (origin, borrowed_from_place));
    }

    // Constrain an origin to be repacked in to include (not equal) a set of permissions at a point
    // fn insert_packing_constraint(
    //     working_table: &mut Self,
    //     point: PointIndex,
    //     origin: Region,
    //     packing: OriginLHS<'tcx>,
    // ) {
    //     let constraints = working_table.origin_packing_at.entry(point).or_default();
    //     constraints.push((origin, packing));
    // }
}

impl<'tcx> std::fmt::Debug for FactTable<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FactTable")
            .field("loan_issues", &self.loan_issues)
            .field("origins", &self.origins)
            .field("graph_ops", &self.graph_operations)
            .field("delta_leaves", &self.delta_leaves)
            .field("origin_expires_before", &self.origin_expires_before)
            .finish()
    }
}

/// Cannonical permissions associated with an origin
/// Precise relationship between these two are yet unconfirmed by the Polonius team
pub(crate) struct OriginPlaces<'tcx> {
    pub(crate) map: FxHashMap<Region, OriginLHS<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> OriginPlaces<'tcx> {
    /// Attempt to add a new constraint to the origin mapping
    /// Panic if the constraint conflicts with an existing constraint
    pub fn new_constraint(&mut self, mir: &mir::Body<'tcx>, r: Region, c: OriginLHS<'tcx>) {
        let normalized_c = self.normalize_origin_lhs(mir, c);
        if let Some(old_lhs) = self.map.insert(r, normalized_c.clone()) {
            assert_eq!(
                old_lhs, normalized_c,
                "[failure] new OriginPlaces constratint normalization: {:?} /= {:?}",
                old_lhs, normalized_c
            );
        }
    }

    /// Rewrite into a cannonical form for key equality
    /// eg. normalize_origin_lhs(unpack(x)) == normalize_origin_lhs(x)
    /// fixme: this is currently broken
    fn normalize_origin_lhs(&self, mir: &mir::Body<'tcx>, c: OriginLHS<'tcx>) -> OriginLHS<'tcx> {
        match c {
            OriginLHS::Place(p) => {
                let p1 = maximally_pack(mir, self.tcx, p);
                OriginLHS::Place(p1)
            }
            OriginLHS::Loan(_) => c,
        }
    }

    /// Attempt to obtain the origin associated with an OriginLHS
    /// This fails with None if no origin exists
    pub fn get_origin(&self, mir: &mir::Body<'tcx>, c: OriginLHS<'tcx>) -> Option<Region> {
        let normalized_c = self.normalize_origin_lhs(mir, c);
        self.map
            .iter()
            .find(|(_, v)| **v == normalized_c)
            .map(|(k, _)| *k)
    }
}

impl<'tcx> std::fmt::Debug for OriginPlaces<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:#?}", self.map))
    }
}

/// Model: Possible interpretations of an origin as permissions
///     Every origin is either:
///         - A temporary value associated with a loan
///         - A maximally packed (canonical) place
#[derive(PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum OriginLHS<'tcx> {
    Place(Place<'tcx>),
    Loan(Loan),
}

impl<'tcx> std::fmt::Debug for OriginLHS<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Place(p) => f.write_fmt(format_args!("Place({:?})", p)),
            Self::Loan(l) => f.write_fmt(format_args!("Loan({:?})", l)),
        }
    }
}

// Fixme: these should be capabilities, not places!
// For exclusive borrows, this doesn't matter since every place has the same capability, though.
#[derive(Debug)]
pub(crate) enum IntroStatement<'tcx> {
    // Kill all nodes of a certain kind in the graph
    Kill(OriginLHS<'tcx>),

    // Insert a "move" edge into the graph.
    // Belongs to the origin associated to "Place"
    // Assigns from the first argument into the second.
    Assign(OriginLHS<'tcx>, Place<'tcx>),

    // Like a borrow, but Place is in the LHS of Region.
    // Unlike Borrow, Reborrow might need to internally repack the graph. For example
    // in the graph
    //   ... -shared reborrow-> {x} -...->
    // it is legal to also shared reborrow a field x.f. We might need to rewrite
    //   ... -shared reborrow-> {x} -unpack-> {x.f, x.g} -pack-> {x} -...->
    // before doing the borrow
    //   ... -shared reborrow-> {x} -unpack-> {x.f, x.g} -pack-> {x} -...->
    //   ... ---------shared reborrow-----------^
    // or something like that. Idk. Either way, reborrows are clearly a different case than regular borrows.
    Reborrow(Place<'tcx>, Loan, Region),

    // Insert a "borrow" edge in the graph.
    // Belongs to the origin associated to "Loan"
    // Takes a loan from the place, into Loan.
    // If Place is in the coupling graph, this is a reborrow.
    Borrow(Place<'tcx>, Loan),
}

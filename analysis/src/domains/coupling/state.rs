// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use log::info;

use crate::{
    abstract_interpretation::{AbstractState, AnalysisResult},
    mir_utils::{self, expand, expand_struct_place, is_prefix, Place},
};
use prusti_rustc_interface::{
    borrowck::{consumers::RustcFacts, BodyWithBorrowckFacts},
    middle::{mir, mir::Location, ty::TyCtxt},
    polonius_engine::FactTypes,
};
use serde::{
    ser::{SerializeMap, SerializeStruct},
    Serialize, Serializer,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use super::{btree_replace, FactTable, IntroStatement, OriginLHS};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

/// Index into arena-allocated coupled borrows.
pub type CoupledBorrowIndex = usize;

#[derive(PartialEq, Eq, Hash, Clone, PartialOrd, Ord, Debug)]
pub struct Tagged<Data, Tag> {
    pub data: Data,
    pub tag: Option<Tag>,
}

impl<Data, Tag> Tagged<Data, Tag> {
    // Tag a place if it is not already tagged
    fn tag(&mut self, t: Tag) {
        if self.tag.is_none() {
            self.tag = Some(t);
        }
    }

    fn untagged(data: Data) -> Self {
        Self { data, tag: None }
    }
}

/// A CDGNode represents a permission (a node in the coupling graph)
/// A CDGNode is one of
///     - A Place: a mir_utils::Place, tagged by a point
///     - A Borrow: a Loan, tagged by a point
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CDGNode<'tcx> {
    Place(Tagged<Place<'tcx>, PointIndex>),
    Borrow(Tagged<Loan, PointIndex>),
}

impl<'tcx> CDGNode<'tcx> {
    /// Tags a node at a point, if it isn't already untagged
    pub fn kill(mut self, l: &PointIndex) -> Self {
        match &mut self {
            CDGNode::Place(p) => p.tag(*l),
            CDGNode::Borrow(b) => b.tag(*l),
        }
        self
    }

    /// Determine if a kill should tag the current place:
    ///     - A borrow should be tagged only if it is untagged, and equal to to_kill
    ///     - A place should be tagged only if it is untagged, and to_kill is its prefix
    fn should_tag(&self, to_kill: &CDGNode<'tcx>) -> bool {
        match (self, to_kill) {
            (CDGNode::Place(p_self), CDGNode::Place(p_kill)) => {
                p_self.tag.is_none() && p_kill.tag.is_none() && is_prefix(p_self.data, p_kill.data)
            }
            (l0 @ CDGNode::Borrow(_), l1 @ CDGNode::Borrow(_)) => l0 == l1,
            _ => false,
        }
    }
}

impl<'tcx> Into<CDGNode<'tcx>> for OriginLHS<'tcx> {
    /// Turn an OriginLHS into a CDGNode by creating a new untagged node
    fn into(self) -> CDGNode<'tcx> {
        match self {
            OriginLHS::Place(p) => CDGNode::Place(Tagged::untagged(p)),
            OriginLHS::Loan(l) => CDGNode::Borrow(Tagged::untagged(l)),
        }
    }
}

impl<'tcx> fmt::Debug for CDGNode<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CDGNode::Place(tp) => {
                if let Some(tag) = tp.tag {
                    write!(f, "{:?}@{:?}", tp.data, tag.index())
                } else {
                    write!(f, "{:?}", tp.data)
                }
            }
            CDGNode::Borrow(tb) => {
                if let Some(tag) = tb.tag {
                    write!(f, "{:?}@{:?}", tb.data, tag.index())
                } else {
                    write!(f, "{:?}", tb.data)
                }
            }
        }
    }
}

/// The smallest amount of metadata needed to calculate the coupling graph
#[derive(Clone, PartialEq, Eq)]
pub enum SignatureKind {
    Shared(Region),
    Coupled(CoupledBorrowIndex),
    Owned,
}

/// A data structure representing an abstract exchange of capabilities
/// associated to the expiry of an origin.
#[derive(Clone, PartialEq, Eq)]
pub struct OriginSignature<'tcx> {
    leaves: BTreeSet<CDGNode<'tcx>>,
    roots: BTreeSet<CDGNode<'tcx>>,
    kind: SignatureKind,
}

impl<'tcx> OriginSignature<'tcx> {
    pub fn add_edge(
        &mut self,
        remove_leaves: BTreeSet<CDGNode<'tcx>>,
        add_leaves: BTreeSet<CDGNode<'tcx>>,
    ) {
        // Possibly repack an edge to change its signature.
        // (since we want the leaves and roots to be disjoint)
        // Only ever do repacks to add to a single edge. We don't care about matching repacks between edges.
        todo!("add edge");
    }

    /// Tags all untagged places which have to_tag as a prefix in a set of nodes
    fn tag_in_set(
        set: &mut BTreeSet<CDGNode<'tcx>>,
        location: &PointIndex,
        to_tag: &CDGNode<'tcx>,
    ) {
        let mut to_replace: Vec<CDGNode<'tcx>> = vec![];
        for node in set.iter() {
            if node.should_tag(to_tag) {
                to_replace.push((*node).clone())
            }
        }
        for node in to_replace.iter() {
            btree_replace(set, node, node.clone().kill(location));
        }
    }

    /// Tags all untagged places which have to_tag as a prefix
    pub fn tag(&mut self, location: &PointIndex, to_tag: &CDGNode<'tcx>) {
        Self::tag_in_set(&mut self.roots, location, to_tag);
        Self::tag_in_set(&mut self.leaves, location, to_tag);
    }
}

impl<'tcx> fmt::Debug for OriginSignature<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?} --* {:?}: ",
            self.leaves.iter().collect::<Vec<_>>(),
            self.roots.iter().collect::<Vec<_>>()
        )?;
        Ok(())
    }
}

#[derive(Clone, Default, PartialEq, Eq)]
pub struct OriginMap<'tcx> {
    map: BTreeMap<Region, OriginSignature<'tcx>>,
    // leaves: BTreeSet<OriginLHS<'tcx>>,
}

impl<'tcx> fmt::Debug for OriginMap<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (k, v) in self.map.iter() {
            writeln!(f, "{:?}: {:?}", k, v)?;
        }
        Ok(())
    }
}

impl<'tcx> OriginMap<'tcx> {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    // pub fn leaves(&self) -> &BTreeSet<OriginLHS<'tcx>> {
    //     &self.leaves
    // }
}

/*
    /// Kill a node in all graphs at a location
    fn kill_node(&mut self, location: &PointIndex, node: &CDGNode<'tcx>) -> AnalysisResult<()> {
        for cdg_origin_map in self.origins.iter_mut() {
            for cdg_origin in cdg_origin_map.values_mut() {
                cdg_origin.tag(location, node);
            }
        }
        Ok(())
    }

    /// Check that two CouplingOrigins have the same LHS's for each origin they both have
    fn cohere_lhs(&mut self, other: &CouplingOrigins<'tcx>) {
        // Join the two by appending the origins together

        // Now we must ensure the two sets of origin mappings cohere, that is they
        //  have the same LHS for each non-empty origin.
        // fixme: right now we just panic if they are incoherent, but in reality we should
        // probably fix them by repacking.

        // naive hack solution: iterate over all tuples
        for origin_map in self.origins.iter() {
            for (origin, cdgo) in origin_map.iter() {
                for other_origin_map in self.origins.iter() {
                    if let Some(other_cdgo) = other_origin_map.get(origin) {
                        assert_eq!(cdgo.leaves, other_cdgo.leaves);
                    }
                }
            }
        }
    }

    /// Kill all leaves that are the LHS of a region
    pub fn kill_leaves(&mut self, origin: &Region, location: &PointIndex) -> AnalysisResult<()> {
        for leaf in self.get_leaves(origin) {
            self.kill_node(location, &leaf)?;
        }
        Ok(())
    }
}
*/

// A coupling graph
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct CDG<'tcx> {
    pub origins: OriginMap<'tcx>,
    // Also include: a structure that translates CoupledBrorrowIndicies
    pub origin_contains_loan_at_invariant: bool,
}

impl<'tcx> CDG<'tcx> {}

/// CouplingState consists of
///     - A CouplingGraph, representing the current
///     - References to the context mir and fact_table
#[derive(Clone)]
pub struct CouplingState<'facts, 'mir: 'facts, 'tcx: 'mir> {
    pub coupling_graph: CDG<'tcx>,
    // also include: annotations at this location:
    // Also include: invariant checks?
    pub(crate) mir: &'mir BodyWithBorrowckFacts<'tcx>,
    pub(crate) fact_table: &'facts FactTable<'tcx>,
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> CouplingState<'facts, 'mir, 'tcx> {
    pub(crate) fn new_empty(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        fact_table: &'facts FactTable<'tcx>,
    ) -> Self {
        Self {
            coupling_graph: Default::default(),
            fact_table,
            mir,
        }
    }

    pub(crate) fn new_bottom(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        fact_table: &'facts FactTable<'tcx>,
    ) -> Self {
        Self {
            coupling_graph: Default::default(),
            fact_table,
            mir,
        }
    }
    pub(crate) fn apply_terminator_effect(
        &self,
        location: Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self)>> {
        let mut new_state = self.clone();
        new_state.cdg_step(location)?;
        let terminator = self.mir.body[location.block].terminator();
        Ok(terminator
            .successors()
            .into_iter()
            .map(|bb| (bb, new_state.clone()))
            .collect())
    }

    pub(crate) fn apply_statement_effect(&mut self, location: Location) -> AnalysisResult<()> {
        self.cdg_step(location)
    }

    /// The main interpretation of Polonius facts
    fn cdg_step(&mut self, location: Location) -> AnalysisResult<()> {
        println!("[debug@{:?}] {:?}", location, self.coupling_graph);

        // get the preconditions for the change in nodes at the location
        let (pre_leaves, _) = match self.fact_table.delta_leaves.get(&location) {
            Some(x) => x.clone(),
            None => (Vec::new(), Vec::new()),
        };

        // add repack edges to ensure thre preconditions are met
        self.ensure_contains_leaves_for(&pre_leaves);

        // apply the rewrite steps to the coupling graph
        self.apply_rewrite(&location);

        // look ahead to see the expiring origins & expire them
        // (recording the necessary changes in leaves as consume and expire statements)
        self.apply_origins(&location);

        Ok(())
    }

    // fixme: For now we're just going to assume we never get contradictory packing requirements, and won't check that.
    fn ensure_contains_leaves_for(&mut self, to_ensure: &Vec<OriginLHS<'tcx>>) {
        for req in to_ensure.iter() {
            let matching_origin = self
                .fact_table
                .origins
                .get_origin(&self.mir.body, req.clone())
                .unwrap();
            let matching_leaves = self
                .coupling_graph
                .origins
                .map
                .get(&matching_origin)
                .unwrap()
                .leaves
                .clone();

            // I'm also going to leave actual unpacking completely unimplemented (lol).
            // Check that the corresponding CDGNode associate to req is contained in the matching_leaves.
            assert!(matching_leaves.contains(&Into::<CDGNode<'tcx>>::into(req.clone())));
        }
    }

    fn apply_rewrite(&mut self, location: &Location) {
        for x in self.fact_table.graph_operations.get(location).iter() {
            for s in x.iter() {
                match s {
                    IntroStatement::Kill(_) => todo!(),
                    IntroStatement::Assign(_, _) => todo!(),
                    IntroStatement::Reborrow(_, _, _) => todo!(),
                    IntroStatement::Borrow(_, _) => todo!(),
                }
            }
        }
    }

    /// Expire non-live origins, and add new live origins
    fn apply_origins(&mut self, location: &Location) -> AnalysisResult<()> {
        // Get the set of origins at a point from the origin_contains_loan_at fact
        todo!("apply origins");
        // let origin_set = match self.fact_table.origin_contains_loan_at.get(location) {
        //     Some(ocla_set) => ocla_set.keys().cloned().collect::<BTreeSet<_>>(),
        //     None => BTreeSet::default(),
        // };

        // for origin_map in self.coupling_graph.origins.map.iter_mut() {
        //     // (expiries) Remove all origins which are not in that set
        //     //  todo: calculate and log the FPCS effects at this point
        //     origin_map.retain(|k, _| origin_set.contains(k));

        //     // (issues) Include empty origins for each new origin
        //     for origin in origin_set.iter() {
        //         origin_map.entry(*origin).or_default();
        //     }

        //     // Sanity check
        //     assert_eq!(
        //         origin_map.keys().cloned().collect::<BTreeSet<_>>(),
        //         origin_set
        //     );
        // }
        Ok(())
    }
}

/*
    fn apply_loan_moves(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        for (from, to) in self.fact_table.get_move_origins_at(location) {
            // Kill every place in the to-origins's cannonical LHS (fixme: is this right? I want to kill the assigned-to place)
            if let OriginLHS::Place(mir_place) = self.fact_table.origins.map.get(&to).unwrap() {
                let node_to_kill = CDGNode::Place(Tagged::untagged(*mir_place));
                self.coupling_graph
                    .origins
                    .kill_node(location, &node_to_kill)?;
            };

            let mut nodes_to_kill: Vec<_> = Default::default();
            for origin_map in self.coupling_graph.origins.origins.iter_mut() {
                // Kill every place that is a prefix of this set:
                let from_origin_current_lhs = origin_map.get(&from).unwrap().leaves.clone();
                for origin_lhs in from_origin_current_lhs.iter() {
                    if let node @ CDGNode::Place(_) = origin_lhs {
                        // Kill origin_lhs in all places in the graph
                        nodes_to_kill.push(node.clone());
                    }
                }
            }

            for node in nodes_to_kill.into_iter() {
                self.coupling_graph.origins.kill_node(location, &node)?;
            }

            for origin_map in self.coupling_graph.origins.origins.iter_mut() {
                // Get the to-origin's LHS (this is already repacked to be the LHS of the assignment)
                let to_origin_assigning_lhs: BTreeSet<CDGNode<'tcx>> =
                    BTreeSet::from([(*self.fact_table.origins.map.get(&to).unwrap())
                        .clone()
                        .into()]);

                // Get the from-origin's new LHS (these should be killed, now)
                let from_origin_current_lhs = origin_map.get(&from).unwrap().leaves.clone();

                // Add an edge from the to-origins's assigning LHS (a set of untagged places) to the LHS of the from-origin (a set of tagged places)
                origin_map
                    .get_mut(&to)
                    .unwrap()
                    .insert_edge(CDGEdge::move_edge(
                        to_origin_assigning_lhs,
                        from_origin_current_lhs,
                    ));
            }
        }
        Ok(())
    }
}
 */
impl<'facts, 'mir: 'facts, 'tcx: 'mir> Serialize for CouplingState<'facts, 'mir, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut s = serializer.serialize_struct("[coupling state]", 1)?;
        s.serialize_field("[cdg]", &self.coupling_graph)?;
        s.end()
    }
}

impl<'tcx> Serialize for CDG<'tcx> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let map = serializer.serialize_map(None)?;
        // fixme: stub
        map.end()
    }
}

impl fmt::Debug for CouplingState<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[coupling state] {}",
            serde_json::to_string_pretty(&self).unwrap()
        )
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> PartialEq for CouplingState<'facts, 'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.coupling_graph == other.coupling_graph
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> Eq for CouplingState<'facts, 'mir, 'tcx> {}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> AbstractState for CouplingState<'facts, 'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        self.coupling_graph.origins.map.is_empty()
    }

    // Invariant: bottom join X is X
    fn join(&mut self, other: &Self) {
        todo!("implement joins");

        /*
              if !self.to_kill.is_empty() || !other.to_kill.is_empty() {
                  unreachable!("(fixable) model assumes terminators do not kill places on exit");
              }
              println!("[join 1] {:?}", self.coupling_graph);
              println!("[join 2] {:?}", other.coupling_graph);

              self.coupling_graph
                  .origins
                  .cohere_lhs(&other.coupling_graph.origins);

              println!("[join coherent 1] {:?}", self.coupling_graph);
              println!("[join coherent 2] {:?}", other.coupling_graph);

              if self.coupling_graph != other.coupling_graph {
                  if other.coupling_graph.origins.origins.is_empty() {
                      // Nothing to do
                  } else if self.coupling_graph.origins.origins.is_empty() {
                      self.coupling_graph
                          .origins
                          .origins
                          .append(&mut other.coupling_graph.origins.origins.clone());
                  } else {
                      // fixme: this assumes no nested coupling (yet).

                      // Look for (and couple) no-equal origins which have the same signature
                      // good god... you need a origin lookup API at the coupling graph level
                      let mut reborrows: BTreeSet<Region> = Default::default();
                      for group in self.coupling_graph.origins.origins.iter() {
                          for (region, cdgo) in group.iter() {
                              for group1 in other.coupling_graph.origins.origins.iter() {
                                  for (region1, cdgo1) in group1.iter() {
                                      if (region == region1)
                                          && (cdgo.leaves == cdgo1.leaves)
                                          && (cdgo.roots == cdgo1.roots)
                                          && (cdgo != cdgo1)
                                      {
                                          reborrows.insert(*region);
                                      }
                                  }
                              }
                          }
                      }
                      // fixme: ambiguous decision when groups differ
                      for region in reborrows.into_iter() {
                          // fixme: this should do a root-first traversal for common structure
                          // fixme: it should also refer to the subsets at the point to decide which to simplify first. For example,
                          //      #1 : _3 -> _2 -> _1
                          //      #2 : _2 -> _1
                          //      #1 : _3 -> ... -> _3@p -> _2 -> _1
                          //      #2 : _2 -> _1
                          //  should not simplify #1 all together like
                          //      #1 : _3 --* _1
                          //  instead, since their downstream graphs are equal, we should get
                          //      #1 : _3 --* _2 -> _1
                          //      #2 : _2 -> _1

                          // Also, in the process of simplifying a edge of the form _3 -> ... -> _3@?
                          // we know that the last killed _3 is old(3). Can we unpick equality assertions from this?
                          if (self.coupling_graph.origins.origins.len() != 1)
                              || (other.coupling_graph.origins.origins.len() != 1)
                          {
                              unimplemented!("deferred joins of reborrows");
                          }

                          let other_cdgo = self.coupling_graph.origins.origins[0]
                              .get_mut(&region)
                              .unwrap()
                              .to_owned();
                          let self_cdgo = self.coupling_graph.origins.origins[0]
                              .get_mut(&region)
                              .unwrap();

                          if self_cdgo.remove_if_subset(&other_cdgo) {
                              // if self_cdgo can be decomposed as [current_self_cdgo] --> [other_cdgo]
                              // set the borrow to be the other_cdgo
                              // use difference to infer other aspects of the invariant

                              // get the loans contained in other_cdgo
                              let mut loans: BTreeSet<Loan> = Default::default();
                              for e in other_cdgo.edges.iter() {
                                  for l in e.lhs.iter() {
                                      if let CDGNode::Borrow(bw) = l {
                                          if bw.tag == None {
                                              loans.insert(bw.data);
                                          }
                                      }
                                  }
                              }

                              *self_cdgo = CDGOrigin::new_coupling(
                                  other_cdgo.leaves.clone(),
                                  other_cdgo.roots.clone(),
                                  loans,
                              );
                          } else {
                              unimplemented!("reborrow that isn't structural subset");
                          }
                      }

                      // fixme: this assume the RHS are not in different packing states?

                      // Couple origins which are possibly aliases
                      //  Note that the origins are coherent so their LHS are equal
                      //  - Partition origins by their RHS, in both sides.
                      //  - If a RHS has only one origin, check that they are equal (or panic)
                      //  - If a RHS has more than one origin, couple the LHS/RHS's of all the origins together.

                      let mut couples: BTreeMap<BTreeSet<CDGNode<'tcx>>, BTreeSet<Region>> =
                          Default::default();

                      for group in self.coupling_graph.origins.origins.iter() {
                          for (region, cdgo) in group.iter() {
                              (couples.entry(cdgo.roots.clone()).or_default()).insert(*region);
                          }
                      }
                      for group in other.coupling_graph.origins.origins.iter() {
                          for (region, cdgo) in group.iter() {
                              (couples.entry(cdgo.roots.clone()).or_default()).insert(*region);
                          }
                      }

                      println!("[coupling map I] {:?}", couples);

                      let mut coupled_edges: BTreeMap<BTreeSet<Region>, BTreeSet<CDGNode>> =
                          Default::default();
                      for (nodes, regions) in couples.into_iter() {
                          if let Some(node_set) = coupled_edges.get_mut(&regions) {
                              // Insert all nodes into node_set
                              for node in nodes.into_iter() {
                                  node_set.insert(node);
                              }
                          } else {
                              coupled_edges.insert(regions, nodes);
                          }
                      }

                      println!("[coupling map II] {:?}", coupled_edges);

                      let mut new_coupling_edges: BTreeMap<Region, CDGEdge<'tcx>> = Default::default();

                      // Remove all singly coupled data and construct new coupling edges
                      for (regions, rhs) in coupled_edges.into_iter() {
                          if regions.len() == 1 {
                              continue;
                          }

                          // Set of loans contained in any region of regions in any graph of self or other
                          let mut region_contains_loans: BTreeSet<Loan> = Default::default();

                          // fixme: do this in a less stupid way

                          for r in regions.iter() {
                              // For each region r in the set of coupled regions...
                              for group in self
                                  .coupling_graph
                                  .origins
                                  .origins
                                  .iter()
                                  .chain(other.coupling_graph.origins.origins.iter())
                              {
                                  // ... for each group in the two branches...
                                  for e in group.get(r).unwrap().edges.iter() {
                                      // ... for each loan in the LHS of an edge in the graph for r in the group...
                                      for loan in e
                                          .lhs
                                          .iter()
                                          .filter_map(|n| match n {
                                              CDGNode::Place(_) => None,
                                              CDGNode::Borrow(l) => {
                                                  if l.tag.is_none() {
                                                      Some(l.data.clone())
                                                  } else {
                                                      None
                                                  }
                                              }
                                          })
                                          .collect::<Vec<_>>()
                                      {
                                          // ... add that loan to the set.
                                          region_contains_loans.insert(loan);
                                      }
                                  }
                              }
                          }

                          // // LHS of the edge is the union of all coupled edges
                          // let mut lhs: BTreeSet<CDGNode<'tcx>> = Default::default();
                          // for r in regions.iter() {
                          //     for n in self.coupling_graph.origins.origins[0]
                          //         .get(r)
                          //         .unwrap()
                          //         .leaves
                          //         .iter()
                          //     {
                          //         lhs.insert((*n).clone());
                          //     }
                          // }

                          // For each group in Self,
                          for r in regions.iter() {
                              for group in self.coupling_graph.origins.origins.iter_mut() {
                                  let lhs: BTreeSet<CDGNode<'tcx>> = group.get(r).unwrap().leaves.clone();
                                  group.insert(
                                      *r,
                                      CDGOrigin::new_coupling(
                                          lhs.clone(),
                                          rhs.clone(),
                                          region_contains_loans.clone(),
                                      ),
                                  );
                              }
                          }
                      }

                      println!("[coupling complete] {:?}", self.coupling_graph);
                  }
              }
        */
    }

    fn widen(&mut self, _: &Self) {
        unreachable!("widening is not possible in this model")
    }
}

// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use analysis::mir_utils::{self, PlaceImpl};
use prusti_interface::environment::borrowck::facts;
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty::TyCtxt},
};

struct Graph<'tcx> {
    edges: Vec<GraphEdge<'tcx>>,
    leaves: FxHashSet<GraphNode<'tcx>>,
}

impl<'tcx> Graph<'tcx> {
    pub fn new() -> Self {
        Self {
            edges: Vec::new(),
            leaves: FxHashSet::default(),
        }
    }

    pub fn unpack(
        &mut self,
        node: GraphNode<'tcx>, // TODO: maybe place instead (same for pack too)?
        mir: &mir::Body<'tcx>, // TODO: should these be parameters?
        tcx: TyCtxt<'tcx>,
    ) {
        let places = mir_utils::expand_struct_place(node.0.place, mir, tcx, None)
            .iter()
            .map(|p| {
                GraphNode(TaggedPlace {
                    place: p.to_mir_place(),
                    location: node.0.location,
                })
            })
            .collect::<Vec<_>>();

        self.leaves.remove(&node);
        for place in places.iter() {
            self.leaves.insert(*place);
        }

        self.edges.push(GraphEdge::Pack {
            from: places,
            to: node,
        });
    }

    // TODO: is this return needed?
    fn pack(&mut self, node: GraphNode<'tcx>) -> Annotation<'tcx> {
        let edge = self.take_edge(|edge| matches!(edge, GraphEdge::Pack { to, .. } if to == &node));

        if let GraphEdge::Pack { from: places, .. } = edge {
            self.leaves.insert(node);
            for place in places.iter() {
                self.leaves.remove(place);
            }

            Annotation::Pack(node.0)
        } else {
            panic!("should have found a pack edge")
        }
    }

    pub fn mutable_borrow(
        &mut self,
        from: GraphNode<'tcx>,
        loan: facts::Loan,
        to: GraphNode<'tcx>,
    ) {
        self.leaves.remove(&to);
        self.leaves.insert(from);

        self.edges.push(GraphEdge::Borrow {
            from,
            loans: vec![loan],
            to,
        });
    }

    pub fn package(&mut self, from: GraphNode<'tcx>, to: GraphNode<'tcx>) -> Vec<Annotation<'tcx>> {
        let mut curr_node = from;
        let mut final_loans = Vec::new();
        let mut final_annotations = Vec::new();

        while curr_node != to {
            let curr_edge = self.take_edge(|edge| edge.comes_from(&curr_node));
            curr_node = *curr_edge.to();

            match curr_edge {
                GraphEdge::Borrow { mut loans, .. } => final_loans.append(&mut loans),
                GraphEdge::Pack { to, .. } => final_annotations.push(Annotation::Pack(to.0)),
                GraphEdge::Abstract {
                    from,
                    mut loans,
                    to,
                } => {
                    final_loans.append(&mut loans);
                    final_annotations.push(Annotation::Restore { from, to });
                }
                GraphEdge::Collapsed {
                    mut loans,
                    mut annotations,
                    ..
                } => {
                    final_loans.append(&mut loans);
                    final_annotations.append(&mut annotations);
                }
            }
        }

        self.edges.push(GraphEdge::Abstract {
            from,
            loans: final_loans,
            to,
        });
        final_annotations
    }

    fn restore(&mut self, node: GraphNode<'tcx>) -> Annotation<'tcx> {
        let edge =
            self.take_edge(|edge| matches!(edge, GraphEdge::Abstract { to, .. } if to == &node));

        if let GraphEdge::Abstract { from, to, .. } = edge {
            self.leaves.insert(node);
            self.leaves.remove(&from);

            Annotation::Restore { from, to }
        } else {
            panic!("should have found an abstract edge")
        }
    }

    pub fn collapse(&mut self, node: GraphNode<'tcx>) {
        let mut final_loans = Vec::new();
        let mut final_annotations = Vec::new();

        let from_edge = self.take_edge(|edge| edge.to() == &node);
        let from = match from_edge {
            GraphEdge::Borrow { from, .. }
            | GraphEdge::Abstract { from, .. }
            | GraphEdge::Collapsed { from, .. } => from,
            GraphEdge::Pack { .. } => panic!("collapsing a pack edge is unsupported"),
        };

        let to_edge = self.take_edge(|edge| edge.comes_from(&node));
        let to = *to_edge.to();

        for edge in [from_edge, to_edge] {
            match edge {
                GraphEdge::Borrow { mut loans, .. } => final_loans.append(&mut loans),
                GraphEdge::Pack { .. } => panic!("collapsing a pack edge is unsupported"),
                GraphEdge::Abstract {
                    from,
                    mut loans,
                    to,
                } => {
                    final_loans.append(&mut loans);
                    final_annotations.push(Annotation::Restore { from, to });
                }
                GraphEdge::Collapsed {
                    mut loans,
                    mut annotations,
                    ..
                } => {
                    final_loans.append(&mut loans);
                    final_annotations.append(&mut annotations);
                }
            }
        }

        self.edges.push(GraphEdge::Collapsed {
            from,
            loans: final_loans,
            annotations: final_annotations,
            to,
        });
    }

    pub fn unwind(&mut self, killed_loans: FxHashSet<facts::Loan>) -> GraphResult<'tcx> {
        for edge in &mut self.edges {
            match edge {
                GraphEdge::Borrow { loans, .. }
                | GraphEdge::Abstract { loans, .. }
                | GraphEdge::Collapsed { loans, .. } => {
                    loans.retain(|loan| !killed_loans.contains(loan));
                }
                GraphEdge::Pack { .. } => {}
            }
        }

        let mut annotations = Vec::new();
        let leaves = self.leaves.clone();
        for leaf in leaves {
            annotations.append(&mut self.unwind_node(leaf));
        }

        (annotations, self.leaves.clone())
    }

    fn unwind_node(&mut self, node: GraphNode<'tcx>) -> Vec<Annotation<'tcx>> {
        let mut final_annotations = Vec::new();
        let mut curr = node;

        loop {
            if let Some(edge) = self.edges.iter().find(|edge| edge.comes_from(&curr)) {
                curr = *edge.to();

                // TODO: consume edge helper that updates annotations, loans, leaves?
                match edge {
                    GraphEdge::Borrow { from, loans, to } if loans.is_empty() => {
                        self.leaves.remove(from);
                        self.leaves.insert(*to);
                        // TODO: duplicated, there should be an easier way
                        self.take_edge(|edge| edge.comes_from(&curr));
                    }
                    GraphEdge::Pack { to, .. } => {
                        let annotation = self.pack(*to);
                        final_annotations.push(annotation);
                    }
                    GraphEdge::Abstract { loans, to, .. } if loans.is_empty() => {
                        let annotation = self.restore(*to);
                        final_annotations.push(annotation);
                    }
                    GraphEdge::Collapsed {
                        from,
                        loans,
                        annotations,
                        to,
                    } if loans.is_empty() => {
                        self.leaves.remove(from);
                        self.leaves.insert(*to);
                        // TODO: append instead?
                        for annotation in annotations {
                            final_annotations.push(*annotation);
                        }
                        self.take_edge(|edge| edge.comes_from(&curr));
                    }
                    _ => return final_annotations,
                }
            } else {
                return final_annotations;
            }
        }
    }

    fn take_edge<F>(&mut self, pred: F) -> GraphEdge<'tcx>
    where
        F: FnMut(&mut GraphEdge<'tcx>) -> bool,
    {
        self.edges
            .drain_filter(pred)
            .next()
            .expect("target node to be found")
    }
}

#[derive(Eq, Hash, PartialEq)]
enum GraphEdge<'tcx> {
    Borrow {
        from: GraphNode<'tcx>,
        loans: Vec<facts::Loan>, // TODO: does this have to be a vec?
        to: GraphNode<'tcx>,
    },
    Pack {
        from: Vec<GraphNode<'tcx>>, // TODO: this should be a known size since its the fields, maybe something like a smallvec instead
        to: GraphNode<'tcx>,
    },
    Abstract {
        from: GraphNode<'tcx>,
        loans: Vec<facts::Loan>,
        to: GraphNode<'tcx>,
    },
    Collapsed {
        from: GraphNode<'tcx>,
        loans: Vec<facts::Loan>,
        annotations: Vec<Annotation<'tcx>>,
        to: GraphNode<'tcx>,
    },
}

impl<'tcx> GraphEdge<'tcx> {
    fn comes_from(&self, node: &GraphNode<'tcx>) -> bool {
        match self {
            GraphEdge::Borrow { from, .. }
            | GraphEdge::Abstract { from, .. }
            | GraphEdge::Collapsed { from, .. } => from == node,
            GraphEdge::Pack { from, .. } => from.contains(node),
        }
    }

    fn to(&self) -> &GraphNode<'tcx> {
        match self {
            GraphEdge::Borrow { to, .. }
            | GraphEdge::Abstract { to, .. }
            | GraphEdge::Collapsed { to, .. }
            | GraphEdge::Pack { to, .. } => to,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GraphNode<'tcx>(TaggedPlace<'tcx>);

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
enum Annotation<'tcx> {
    Pack(TaggedPlace<'tcx>),
    Restore {
        from: GraphNode<'tcx>,
        to: GraphNode<'tcx>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct TaggedPlace<'tcx> {
    place: mir::Place<'tcx>,
    location: mir::Location,
}

type GraphResult<'tcx> = (Vec<Annotation<'tcx>>, FxHashSet<GraphNode<'tcx>>);
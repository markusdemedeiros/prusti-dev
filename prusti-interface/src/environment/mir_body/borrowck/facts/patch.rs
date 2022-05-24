use super::{AllInputFacts, BorrowckFacts, LocationTable, Point, RichLocation};
use crate::environment::mir_body::patch::MirPatch;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir;

pub fn apply_patch_to_borrowck<'tcx>(
    borrowck_input_facts: &mut AllInputFacts,
    location_table: &mut LocationTable,
    patch: &MirPatch<'tcx>,
    body: &mir::Body<'tcx>,
) {
    let mut lt_patcher = LocationTablePatcher::new(location_table);

    let mut cfg_edges = FxHashMap::<_, Vec<_>>::default();
    for (from, to) in std::mem::take(&mut borrowck_input_facts.cfg_edge) {
        cfg_edges.entry(from).or_default().push(to);
    }

    // Create cfg_edge facts for the new basic blocks.
    let bb_base = body.basic_blocks().len();
    for (offset, block) in patch.new_blocks.iter().enumerate() {
        // +1 is for terminator.
        let mut statement_indices = 0usize..block.statements.len() + 1;
        if let Some(first) = statement_indices.next() {
            cfg_edges.insert(
                lt_patcher.next_start_point(bb_base + offset, first),
                vec![lt_patcher.next_mid_point(bb_base + offset, first)],
            );
        }
        for statement_index in statement_indices {
            cfg_edges.insert(
                lt_patcher.next_start_point(bb_base + offset, statement_index),
                vec![lt_patcher.next_mid_point(bb_base + offset, statement_index)],
            );
            cfg_edges.insert(
                lt_patcher.next_mid_point(bb_base + offset, statement_index - 1),
                vec![lt_patcher.next_start_point(bb_base + offset, statement_index)],
            );
        }
    }

    // Patch cfg_edge facts for the replaced terminators.
    for (src, patch) in patch.patch_map.iter_enumerated() {
        if let Some(patch) = patch {
            match patch {
                mir::TerminatorKind::Goto { target } => {
                    assert!(cfg_edges
                        .insert(
                            lt_patcher.mid_point(src.index(), body[src].statements.len()),
                            vec![lt_patcher.start_point(target.index(), 0),]
                        )
                        .is_some());
                }
                mir::TerminatorKind::Drop { target, unwind, .. } => {
                    assert!(cfg_edges
                        .insert(
                            lt_patcher.mid_point(src.index(), body[src].statements.len()),
                            vec![lt_patcher.start_point(target.index(), 0),]
                        )
                        .is_some());
                    if let Some(unwind) = unwind {
                        assert!(cfg_edges
                            .insert(
                                lt_patcher.mid_point(src.index(), body[src].statements.len()),
                                vec![lt_patcher.start_point(unwind.index(), 0),]
                            )
                            .is_some());
                    }
                }
                _ => unreachable!("patch: {:?}", patch),
            }
        }
    }

    // Patch cfg_edge facts for the inserted statements.
    let predecessors = body.predecessors();
    let mut new_statements = patch.new_statements.clone();
    new_statements.sort_by_key(|s| s.0);
    let mut delta = 0;
    let mut last_bb = mir::START_BLOCK;
    for (mut loc, stmt) in new_statements {
        if loc.block != last_bb {
            delta = 0;
            last_bb = loc.block;
        }
        loc.statement_index += delta;

        // Shift all points by one statement down.
        lt_patcher.insert_statement_at(loc, body[loc.block].statements.len());

        let statement_start_point = lt_patcher.start_point(loc.block.index(), loc.statement_index);
        let statement_mid_point = lt_patcher.mid_point(loc.block.index(), loc.statement_index);
        let next_statement_start_point =
            lt_patcher.start_point(loc.block.index(), loc.statement_index + 1);
        if loc.statement_index == 0 {
            for predecessor in &predecessors[loc.block] {
                let terminator_mid_point =
                    lt_patcher.mid_point(predecessor.index(), body[*predecessor].statements.len());
                assert!(cfg_edges
                    .insert(terminator_mid_point, vec![statement_start_point])
                    .is_some());
            }
        } else {
            // Insert the statement and patch the links with the previous and following statements.
            let previous_statement_mid_point =
                lt_patcher.mid_point(loc.block.index(), loc.statement_index - 1);
            assert!(cfg_edges
                .insert(previous_statement_mid_point, vec![statement_start_point])
                .is_some());
        }
        assert!(cfg_edges
            .insert(statement_start_point, vec![statement_mid_point])
            .is_none());
        assert!(cfg_edges
            .insert(statement_mid_point, vec![next_statement_start_point])
            .is_none());

        delta += 1;
    }

    borrowck_input_facts.cfg_edge = cfg_edges
        .into_iter()
        .flat_map(|(from, targets)| targets.into_iter().map(move |target| (from, target)))
        .collect();
}

struct LocationTablePatcher<'a> {
    location_table: &'a mut LocationTable,
    next_point: usize,
}

impl<'a> LocationTablePatcher<'a> {
    fn new(location_table: &'a mut LocationTable) -> Self {
        let next_point = location_table
            .locations
            .keys()
            .max()
            .map(|point| point.index())
            .unwrap_or(1usize)
            + 1;
        Self {
            location_table,
            next_point,
        }
    }

    fn point(&self, location: RichLocation) -> Point {
        self.location_table.points[&location]
    }

    fn start_point(&mut self, block: usize, statement_index: usize) -> Point {
        self.point(RichLocation::Start(mir::Location {
            block: block.into(),
            statement_index,
        }))
    }

    fn mid_point(&mut self, block: usize, statement_index: usize) -> Point {
        self.point(RichLocation::Mid(mir::Location {
            block: block.into(),
            statement_index,
        }))
    }

    fn fresh_point(&mut self) -> Point {
        let point = self.next_point.into();
        self.next_point += 1;
        point
    }

    fn next_point(&mut self, location: RichLocation) -> Point {
        if let Some(point) = self.location_table.points.get(&location) {
            *point
        } else {
            let point = self.fresh_point();
            self.location_table.locations.insert(point, location);
            self.location_table.points.insert(location, point);
            point
        }
    }

    fn next_start_point(&mut self, block: usize, statement_index: usize) -> Point {
        self.next_point(RichLocation::Start(mir::Location {
            block: block.into(),
            statement_index,
        }))
    }

    fn next_mid_point(&mut self, block: usize, statement_index: usize) -> Point {
        self.next_point(RichLocation::Mid(mir::Location {
            block: block.into(),
            statement_index,
        }))
    }

    /// Shift locations of all statements by 1 and insert the provided point at that location.
    fn insert_statement_at(&mut self, location: mir::Location, statement_count: usize) {
        // Shift all the statements by one.
        let mut target_statement_index = statement_count + 1; // +1 for terminator;
        while target_statement_index > location.statement_index {
            let statement_index = target_statement_index - 1;
            let old_start_location = RichLocation::start(location.block, statement_index);
            let old_mid_location = RichLocation::mid(location.block, statement_index);
            let old_start_point = self.location_table.points[&old_start_location];
            let old_mid_point = self.location_table.points[&old_mid_location];
            let start_location = RichLocation::start(location.block, target_statement_index);
            let mid_location = RichLocation::mid(location.block, target_statement_index);
            self.location_table
                .locations
                .insert(old_start_point, start_location);
            self.location_table
                .points
                .insert(start_location, old_start_point);
            self.location_table
                .locations
                .insert(old_mid_point, mid_location);
            self.location_table
                .points
                .insert(mid_location, old_mid_point);
            target_statement_index = statement_index;
        }

        // Insert.
        let start_point = self.fresh_point();
        let mid_point = self.fresh_point();
        let start_location = RichLocation::start(location.block, target_statement_index);
        let mid_location = RichLocation::mid(location.block, target_statement_index);
        self.location_table
            .locations
            .insert(start_point, start_location);
        self.location_table
            .points
            .insert(start_location, start_point);
        self.location_table
            .locations
            .insert(mid_point, mid_location);
        self.location_table.points.insert(mid_location, mid_point);
    }
}

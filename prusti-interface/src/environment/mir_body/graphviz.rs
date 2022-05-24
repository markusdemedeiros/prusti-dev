use super::borrowck::{
    facts::{AllInputFacts, LocationTable, RichLocation},
    lifetimes::{Lifetimes, LifetimesGraphviz},
};
use crate::environment::{
    mir_dump::graphviz::{
        to_text::{loan_containment_to_text, loans_to_text},
        ToText,
    },
    Environment, Procedure,
};
use rustc_middle::mir;
use rustc_span::def_id::DefId;
use vir::common::graphviz::{Graph, NodeBuilder};

pub fn to_graphviz<'tcx>(
    borrowck_input_facts: &AllInputFacts,
    location_table: &LocationTable,
    mir: &mir::Body<'tcx>,
) -> Graph {
    let lifetimes = Lifetimes::new(borrowck_input_facts.clone(), location_table.clone());

    let mut graph = Graph::with_columns(&[
        "location",
        "statement",
        "subset_base",
        "subset",
        "origin_live_on_entry",
        "original lifetimes",
        "derived lifetimes",
    ]);

    let mut opaque_lifetimes_table = graph.create_table("Opaque lifetimes", &["lifetime"]);
    for lifetime in lifetimes.get_opaque_lifetimes_with_inclusions() {
        opaque_lifetimes_table.add_row(vec![lifetime.to_text()]);
    }
    opaque_lifetimes_table.build();

    let mut original_lifetimes_table = graph.create_table("Original lifetimes", &["lifetime"]);
    for lifetime in lifetimes.get_original_lifetimes() {
        original_lifetimes_table.add_row(vec![lifetime.to_text()]);
    }
    original_lifetimes_table.build();

    let mut parameters_table = graph.create_table("Function parameters", &["parameter", "type"]);
    for parameter in mir.args_iter() {
        parameters_table.add_row(vec![
            parameter.to_text(),
            mir.local_decls[parameter].ty.to_text(),
        ]);
    }
    parameters_table.add_row(vec!["result".to_text(), mir.return_ty().to_text()]);
    parameters_table.build();

    let mut locals_table = graph.create_table("Function locals", &["local", "type"]);
    for local in mir.vars_and_temps_iter() {
        locals_table.add_row(vec![local.to_text(), mir.local_decls[local].ty.to_text()]);
    }
    locals_table.build();

    visit_body(&mut graph, mir, &lifetimes);

    graph
}

fn visit_body(graph: &mut Graph, mir: &mir::Body<'_>, lifetimes: &Lifetimes) {
    for bb in mir.basic_blocks().indices() {
        visit_basic_block(graph, mir, bb, lifetimes);
    }
}

fn visit_basic_block(
    graph: &mut Graph,
    mir: &mir::Body<'_>,
    bb: mir::BasicBlock,
    lifetimes: &Lifetimes,
) {
    let mut node_builder = graph.create_node(bb.to_text());
    let mir::BasicBlockData {
        statements,
        terminator,
        ..
    } = &mir[bb];
    let mut location = mir::Location {
        block: bb,
        statement_index: 0,
    };
    let terminator_index = statements.len();
    while location.statement_index < terminator_index {
        visit_statement(
            &mut node_builder,
            location,
            &statements[location.statement_index],
            lifetimes,
        );
        location.statement_index += 1;
    }
    if let Some(terminator) = terminator {
        node_builder.add_row_single(terminator.to_text());
    }
    node_builder.build();
    if let Some(terminator) = terminator {
        visit_terminator(graph, bb, terminator);
    }
}

fn visit_statement(
    node_builder: &mut NodeBuilder,
    location: mir::Location,
    statement: &mir::Statement<'_>,
    lifetimes: &Lifetimes,
) {
    let subset_base_start = lifetimes.get_subset_base(RichLocation::Start(location));
    let subset_base_mid = lifetimes.get_subset_base(RichLocation::Mid(location));
    let subset_start = lifetimes.get_subset(RichLocation::Start(location));
    let subset_mid = lifetimes.get_subset(RichLocation::Mid(location));
    let origin_live_on_entry_start =
        lifetimes.get_origin_live_on_entry(RichLocation::Start(location));
    let origin_live_on_entry_mid = lifetimes.get_origin_live_on_entry(RichLocation::Mid(location));
    let loan_live_at_start = lifetimes.get_loan_live_at(RichLocation::Start(location));
    let loan_live_at_mid = lifetimes.get_loan_live_at(RichLocation::Mid(location));
    let origin_contains_loan_at_start =
        lifetimes.get_origin_contains_loan_at(RichLocation::Start(location));
    let origin_contains_loan_at_mid =
        lifetimes.get_origin_contains_loan_at(RichLocation::Mid(location));

    let mut row_builder_start = node_builder.create_row();
    row_builder_start.set("location", location.to_text());
    row_builder_start.set("statement", statement.to_text());
    row_builder_start.set("subset_base", subset_base_start.to_text());
    row_builder_start.set("subset", subset_start.to_text());
    row_builder_start.set("origin_live_on_entry", origin_live_on_entry_start.to_text());
    row_builder_start.set("original lifetimes", loans_to_text(&loan_live_at_start));
    row_builder_start.set(
        "derived lifetimes",
        loan_containment_to_text(&origin_contains_loan_at_start),
    );
    row_builder_start.build();

    let mut row_builder_end = node_builder.create_row();
    row_builder_end.set("location", "".to_text());
    row_builder_end.set("statement", "".to_text());
    row_builder_end.set("subset_base", subset_base_mid.to_text());
    row_builder_end.set("subset", subset_mid.to_text());
    row_builder_end.set("origin_live_on_entry", origin_live_on_entry_mid.to_text());
    row_builder_end.set("original lifetimes", loans_to_text(&loan_live_at_mid));
    row_builder_end.set(
        "derived lifetimes",
        loan_containment_to_text(&origin_contains_loan_at_mid),
    );
    row_builder_end.build();
}

fn visit_terminator(graph: &mut Graph, bb: mir::BasicBlock, terminator: &mir::Terminator<'_>) {
    use rustc_middle::mir::TerminatorKind;
    let bb = &bb;
    match &terminator.kind {
        TerminatorKind::Goto { target } => {
            graph.add_regular_edge(bb.to_text(), target.to_text());
        }
        TerminatorKind::SwitchInt { ref targets, .. } => {
            for target in targets.all_targets() {
                graph.add_regular_edge(bb.to_text(), target.to_text());
            }
        }
        TerminatorKind::Resume => {
            graph.add_exit_edge(bb.to_text(), "resume".to_text());
        }
        TerminatorKind::Abort => {
            graph.add_exit_edge(bb.to_text(), "abort".to_text());
        }
        TerminatorKind::Return => {
            graph.add_exit_edge(bb.to_text(), "return".to_text());
        }
        TerminatorKind::Unreachable => {
            graph.add_exit_edge(bb.to_text(), "unreachable".to_text());
        }
        TerminatorKind::DropAndReplace { target, unwind, .. }
        | TerminatorKind::Drop { target, unwind, .. } => {
            graph.add_regular_edge(bb.to_text(), target.to_text());
            if let Some(target) = unwind {
                graph.add_unwind_edge(bb.to_text(), target.to_text());
            }
        }
        TerminatorKind::Call {
            ref destination,
            cleanup,
            ..
        } => {
            if let Some((_, target)) = destination {
                graph.add_regular_edge(bb.to_text(), target.to_text());
            }
            if let Some(target) = cleanup {
                graph.add_unwind_edge(bb.to_text(), target.to_text());
            }
        }
        TerminatorKind::Assert {
            target, cleanup, ..
        } => {
            graph.add_regular_edge(bb.to_text(), target.to_text());
            if let Some(target) = cleanup {
                graph.add_unwind_edge(bb.to_text(), target.to_text());
            }
        }
        TerminatorKind::Yield { .. } => {
            graph.add_exit_edge(bb.to_text(), "yield".to_text());
        }
        TerminatorKind::GeneratorDrop => {
            graph.add_exit_edge(bb.to_text(), "generator_drop".to_text());
        }
        TerminatorKind::FalseEdge {
            real_target,
            imaginary_target,
        } => {
            graph.add_regular_edge(bb.to_text(), real_target.to_text());
            graph.add_imaginary_edge(bb.to_text(), imaginary_target.to_text());
        }
        TerminatorKind::FalseUnwind {
            real_target,
            unwind,
        } => {
            graph.add_regular_edge(bb.to_text(), real_target.to_text());
            if let Some(imaginary_target) = unwind {
                graph.add_imaginary_edge(bb.to_text(), imaginary_target.to_text());
            }
        }
        TerminatorKind::InlineAsm { .. } => {
            graph.add_exit_edge(bb.to_text(), "inline_asm".to_text());
        }
    };
}

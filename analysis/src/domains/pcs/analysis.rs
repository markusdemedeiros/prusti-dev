use crate::{abstract_interpretation::AnalysisResult, domains::PCSState, PointwiseState};
use rustc_borrowck::BodyWithBorrowckFacts;
use rustc_middle::{
    mir::{Rvalue::*, Statement, StatementKind::*},
    ty::TyCtxt,
};
use rustc_span::def_id::DefId;
extern crate rustc_mir_dataflow;
use rustc_mir_dataflow::{
    impls::{DefinitelyInitializedPlaces, MaybeInitializedPlaces},
    move_paths::MoveData,
    MoveDataParamEnv,
};
extern crate rustc_index;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::Location;
use rustc_mir_dataflow::move_paths::MovePathIndex;

use rustc_mir_dataflow::{lattice::Dual, Analysis};
pub struct PCSAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'mir, 'tcx: 'mir> PCSAnalysis<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> Self {
        PCSAnalysis {
            tcx,
            def_id,
            body_with_facts,
        }
    }

    pub fn run_analysis(&self) -> AnalysisResult<PointwiseState<'mir, 'tcx, PCSState<'mir, 'tcx>>> {
        todo!();
    }

    pub fn pprint_cfg(&self) {
        println!("{:#?}", self.body_with_facts.input_facts.var_dropped_at);
    }

    pub fn print_body_verbose(&self) {
        let basic_blocks = self.body_with_facts.body.basic_blocks();

        for (bbno, bb) in (&basic_blocks).iter_enumerated() {
            println!("\n{:#?}", bbno);
            for stmt in bb.statements.iter() {
                self.pprint_stmt(stmt);
            }
            if let Some(term) = &bb.terminator {
                println!("\t{:#?}", term.kind);
            }
        }
    }

    pub fn pprint_rust_init_analysis(&self) {
        /* mdpe construction diuplicated from prusti-viper/src/encoder/mir/procedures/encoder */
        let param_env = self.tcx.param_env_reveal_all_normalized(self.def_id);
        let move_data =
            match MoveData::gather_moves(&self.body_with_facts.body, self.tcx, param_env) {
                Ok(move_data) => move_data,
                Err((_, _)) => {
                    unreachable!();
                }
            };
        let mdpe: MoveDataParamEnv<'tcx> = MoveDataParamEnv {
            move_data,
            param_env,
        };

        let mut def_init_places_results =
            DefinitelyInitializedPlaces::new(self.tcx, &self.body_with_facts.body, &mdpe)
                .into_engine(self.tcx, &self.body_with_facts.body)
                .iterate_to_fixpoint()
                .into_results_cursor(&self.body_with_facts.body);

        let mut maybe_init_places_results =
            MaybeInitializedPlaces::new(self.tcx, &self.body_with_facts.body, &mdpe)
                .into_engine(self.tcx, &self.body_with_facts.body)
                .iterate_to_fixpoint()
                .into_results_cursor(&self.body_with_facts.body);

        let basic_blocks = self.body_with_facts.body.basic_blocks();
        let mut loc: Location;

        for (bbno, bbdata) in (&basic_blocks).iter_enumerated() {
            println!("\n--------------- {:#?} ---------------", bbno);
            def_init_places_results.seek_to_block_start(bbno);
            maybe_init_places_results.seek_to_block_start(bbno);
            loc = Location {
                block: bbno,
                statement_index: 0,
            };

            for stmt in bbdata.statements.iter() {
                print!("\t (PRE EFFECT) Definitely Initialized Places:  ");
                def_init_places_results.seek_before_primary_effect(loc);
                let def_init_places: &Dual<BitSet<MovePathIndex>> = def_init_places_results.get();
                let def_mpi_iter = &mut def_init_places.0.iter();
                while let Some(mpi) = def_mpi_iter.next() {
                    print!("{:#?}, ", mdpe.move_data.move_paths[mpi].place);
                }
                print!("\n");

                print!("\t (PRE EFFECT) Maybe Initialized Places:       ");
                maybe_init_places_results.seek_before_primary_effect(loc);
                let maybe_init_places: &Dual<BitSet<MovePathIndex>> = def_init_places_results.get();
                let maybe_mpi_iter = &mut maybe_init_places.0.iter();
                while let Some(mpi) = maybe_mpi_iter.next() {
                    print!("{:#?}, ", mdpe.move_data.move_paths[mpi].place);
                }
                print!("\n");

                println!("{:#?}", stmt);

                print!("\t (POST EFFECT) Definitely Initialized Places: ");
                def_init_places_results.seek_after_primary_effect(loc);
                let def_init_places: &Dual<BitSet<MovePathIndex>> = def_init_places_results.get();
                let def_mpi_iter = &mut def_init_places.0.iter();
                while let Some(mpi) = def_mpi_iter.next() {
                    print!("{:#?}, ", mdpe.move_data.move_paths[mpi].place);
                }
                print!("\n");

                print!("\t (POST EFFECT) Maybe Initialized Places:      ");
                maybe_init_places_results.seek_after_primary_effect(loc);
                let maybe_init_places: &Dual<BitSet<MovePathIndex>> = def_init_places_results.get();
                let maybe_mpi_iter = &mut maybe_init_places.0.iter();
                while let Some(mpi) = maybe_mpi_iter.next() {
                    print!("{:#?}, ", mdpe.move_data.move_paths[mpi].place);
                }
                print!("\n");
                print!("\n");

                loc.statement_index += 1;
            }

            println!("TERMINATOR: {:#?}", bbdata.terminator().kind);
        }
    }

    fn pprint_stmt(&self, stmt: &Statement) {
        match &(stmt).kind {
            Assign(bv) => {
                match &(**bv) {
                    (place, rv) => {
                        print!("\t{:#?} :: ", place);
                        match &rv {
                            Use(_op) => {
                                println!("USE");
                            }
                            Repeat(_op, _const) => {
                                println!("REPEAT");
                            }
                            Ref(_a, _b, _c) => {
                                println!("REF");
                            }
                            ThreadLocalRef(_d) => {
                                println!("THREDLOCALREF");
                            }
                            AddressOf(_m, _p) => {
                                println!("ADDRESOF");
                            }
                            Len(_p) => {
                                println!("LEN");
                            }
                            Cast(_ck, _op, _ty) => {
                                println!("CAST");
                            }
                            BinaryOp(_bop, _bo) => {
                                println!("BINARYOP");
                            }
                            CheckedBinaryOp(_bo, _box) => {
                                println!("CHECKBINARYOP");
                            }
                            NullaryOp(_nulop, _ty) => {
                                println!("NULLARYOP");
                            }
                            UnaryOp(_unop, _op) => {
                                println!("UNARYOP");
                            }
                            Discriminant(_d) => {
                                println!("DISCRIMINANT");
                            }
                            Aggregate(_bo, _vc) => {
                                println!("AGGREGATE");
                            }
                            ShallowInitBox(_o, _v) => {
                                println!("SHALLOWINITBOX");
                            }
                        }
                    }
                }
                println!("\t\t{:#?}", stmt);
            }
            _ => {
                println!("\t{:#?}", stmt);
            }
        }
    }
}

/*
pub(super) fn create_move_data_param_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    def_id: DefId,
) -> MoveDataParamEnv<'tcx> {
}


 */

use crate::mid::opt::block_threading::BlockThreadingPass;
use crate::mid::opt::cond_prop::CondPropPass;
use crate::mid::opt::dce::DcePass;
use crate::mid::opt::flow_simplify::FlowSimplifyPass;
use crate::mid::opt::gvn::GvnPass;
use crate::mid::opt::inline::InlinePass;
use crate::mid::opt::instr_simplify::InstrSimplifyPass;
use crate::mid::opt::mem_forwarding::MemForwardingPass;
use crate::mid::opt::param_combine::ParamCombinePass;
use crate::mid::opt::runner::ProgramPass;
use crate::mid::opt::sccp::SccpPass;
use crate::mid::opt::slot_to_param::SlotToParamPass;

pub mod runner;

pub mod gc;
pub mod slot_to_param;
pub mod sccp;
pub mod flow_simplify;
pub mod inline;
pub mod dce;
pub mod param_combine;
pub mod phi_pushing;
pub mod mem_forwarding;
pub mod block_threading;
pub mod instr_simplify;
pub mod gvn;
pub mod cond_prop;

pub const DEFAULT_PASSES: &[&dyn ProgramPass] = &[
    &SlotToParamPass,
    &InlinePass,
    &SccpPass,
    &CondPropPass,
    &InstrSimplifyPass,
    &ParamCombinePass,
    &GvnPass,
    &DcePass,
    &FlowSimplifyPass,
    &BlockThreadingPass,
    // &PhiPushingPass, // TOOD get this working properly
    &MemForwardingPass,
];

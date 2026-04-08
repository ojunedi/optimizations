use crate::ana::Nil;
use crate::ast::BoundProg;
use crate::frontend::Resolver;
use crate::identifiers::VarName;
use crate::middle_end::Lowerer;
use crate::parser::ProgParser;
use crate::ssa::Program;
use crate::txt::FileInfo;

/// compiler pipeline
pub fn compile(s: &str) -> Result<String, String> {
    let (resolver, resolved_ast) = frontend(s)?;
    let (lowerer, ssa) = middle_end(resolver, resolved_ast)?;
    let asm = backend(lowerer, ssa);
    Ok(asm)
}

/// Frontend, parsing and validation
pub fn frontend(s: &str) -> Result<(Resolver, BoundProg), String> {
    let file_info = FileInfo::new(s);
    let raw_ast =
        ProgParser::new().parse(s).map_err(|e| format!("Error parsing program: {}", e))?;
    let mut resolver = Resolver::new();
    let resolved_ast = resolver
        .resolve_prog(raw_ast)
        .map_err(|e| format!("Error resolving ast: {}", file_info.report_error(e)))?;
    Ok((resolver, resolved_ast))
}

/// Middle-end, lambda lifting and SSA construction
pub fn middle_end(
    resolver: Resolver, resolved_ast: BoundProg,
) -> Result<(Lowerer, Program<VarName, Nil>), String> {
    use crate::middle_end::{AssertionRemover, CopyPropagator};
    let mut lowerer = Lowerer::from(resolver);
    let ssa = lowerer.lower_prog(resolved_ast);
    let ssa = CopyPropagator::new().run(ssa);
    let ssa = AssertionRemover::new(&ssa).optimize(ssa);
    Ok((lowerer, ssa))
}

/// Backend, code generation
pub fn backend(_lowerer: Lowerer, ssa: Program<VarName, Nil>) -> String {
    use crate::asm::{Reg, instrs_to_string};
    use crate::backend::{
        ConflictAnalysis, Emitter, LivenessAnalyzer, RegisterAllocator, UnusedRemover,
    };
    let ssa = {
        // an iterative approach of removing unused variables and parameters
        let mut fixed = ssa;
        loop {
            let live = LivenessAnalyzer::new(&fixed).analyze(fixed);
            let mut remover = UnusedRemover::new();
            fixed = remover.run(live);
            match remover.progress() {
                None => {
                    break fixed;
                }
                Some(_) => {}
            }
        }
    };
    let ssa = LivenessAnalyzer::new(&ssa).analyze(ssa);
    // register allocation
    let conflicts = ConflictAnalysis::new(&ssa);
    let registers = Reg::ALLOCATABLE;
    let mut allocator = RegisterAllocator::new();
    allocator.graph_color(conflicts, &registers, false);
    // code generation
    let mut emitter = Emitter::from(allocator);
    emitter.emit_prog(&ssa);
    let asm = emitter.to_asm();
    let txt = instrs_to_string(&asm);
    txt
}

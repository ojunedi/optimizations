use clap::{ArgAction, Parser};
use snake_optimizations::{
    asm::{Reg, instrs_to_string},
    backend::{ConflictAnalysis, Emitter, LivenessAnalyzer, RegisterAllocator, UnusedRemover},
    cli::*,
    frontend::Resolver,
    interp,
    middle_end::{AssertionRemover, CopyPropagator, Lowerer},
    parser::ProgParser,
    runner::*,
    txt::FileInfo,
};
use std::path::{Path, PathBuf};

#[derive(Parser, Debug)]
#[command(about, long_about = None)]
struct Cli {
    /// File containing the input program; defaults to stdin
    input_file: Option<String>,

    /// Optional target type; defaults to asm
    #[arg(value_enum, short, long, value_name = "target")]
    target: Option<Target>,

    /// Optional output file.
    /// For target exe, defaults to runtime/stub.exe, otherwise if not present prints to stdout
    #[arg(short, long, value_name = "output")]
    output: Option<PathBuf>,

    /// Apply specified optional optimizations; defaults to apply no optimizations
    /// To apply all optimizations, use "all"
    /// Format: [<optimization>, ...]
    /// Example:
    ///  - "-O": apply no optimization
    ///  - "-O=cp,ar": apply only copy propagation and assertion removal
    ///  - "-O=all": apply all optimizations
    #[arg(short = 'O', long, alias = "opts", value_name = "optimization", num_args = 0..)]
    optimizations: Option<OptimizationCollection>,

    /// If set, generates the interference graph in svg format to a file
    #[arg(long, value_name = "interference")]
    interference: Option<PathBuf>,

    /// Specify the set of allocatable registers
    /// Format: <collection>[+reg1][-reg2] ...
    /// Example: -R=volatile+rbx-r9
    ///
    /// The register selection starts with a base collection:
    /// - all: All allocatable registers (default)
    /// - volatile: Only volatile registers
    /// - non-volatile: Only non-volatile registers
    /// - none: No registers
    ///
    /// You can then modify this set by adding or removing specific registers:
    /// - +reg: Add a register (e.g., +r8)
    /// - -reg: Remove a register (e.g., -r9)
    ///
    /// Examples:
    /// - "all": Use all allocatable registers
    /// - "non-volatile+r8": Use non-volatile registers plus r8
    /// - "all-r9-r10": Use all allocatable registers except r9 and r10
    #[arg(short = 'R', long, alias = "regs", value_name = "register")]
    registers: Option<RegisterSelection>,

    /// If set, executes the output program, rather than displaying it.
    /// For asm or exe, executes the binary; for other targets, runs an interpreter
    #[arg(short = 'x', long, value_name = "execute", allow_hyphen_values = true, num_args = 0..)]
    execute: Option<Vec<String>>,

    /// Optional runtime file; defaults to runtime/stub.rs
    #[arg(short, long, value_name = "runtime")]
    runtime: Option<PathBuf>,

    /// If set, prints verbose output. Can be repeated (e.g. -vv) for more verbosity
    #[arg(short, long, action = ArgAction::Count)]
    verbose: u8,
}

fn run_cli(cli: &Cli) -> Result<(), String> {
    let conf = {
        let conf = CompilerConf::new(
            cli.optimizations.clone().into_iter().flatten(),
            match cli.verbose {
                0 => Verbosity::Minimalistic,
                1 => Verbosity::Moderate,
                2 => Verbosity::Mouthful,
                _ => {
                    eprintln!("It's a bit too verbose, don't you think?");
                    Verbosity::Mouthful
                }
            },
        );
        conf
    };

    // frontend: parse
    let inp = match &cli.input_file {
        Some(file) => {
            read_file(Path::new(file)).map_err(|e| format!("Error reading file: {}", e))?
        }
        None => std::io::read_to_string(&mut std::io::stdin())
            .map_err(|e| format!("Error reading stdin: {}", e))?,
    };
    let file_info = FileInfo::new(&inp);
    let raw_ast =
        ProgParser::new().parse(&inp).map_err(|e| format!("Error parsing program: {}", e))?;
    match cli.target {
        Some(AST) => {
            if let Some(ref args) = cli.execute {
                let value = interp::ast::Machine::run(&raw_ast, args)
                    .map_err(|e| format!("Error interpreting program: {}", e))?;
                println!("{}", value);
            } else {
                println!("{}", raw_ast);
            }
            return Ok(());
        }
        _ => {}
    }

    // frontend: resolve
    let mut resolver = Resolver::new();
    let resolved_ast = resolver
        .resolve_prog(raw_ast)
        .map_err(|e| format!("Error resolving ast: {}", file_info.report_error(e)))?;

    match cli.target {
        Some(ResolvedAST) => {
            if let Some(ref args) = cli.execute {
                let value = interp::ast::Machine::run(&resolved_ast, args)
                    .map_err(|e| format!("Error interpreting program: {}", e))?;
                println!("{}", value);
            } else {
                println!("{}", resolved_ast);
            }
            return Ok(());
        }
        _ => {}
    }

    // middle-end: lower to SSA
    let mut lowerer = Lowerer::from(resolver);
    let ssa = lowerer.lower_prog(resolved_ast);

    // middle-end: optimizations on SSA
    let ssa = {
        let mut fixed = ssa;
        if conf.verbose >= Verbosity::Moderate {
            println!("[[lowering]]");
            println!("{}", fixed);
        }
        if conf.optimizations.contains(&Optimization::CopyPropagation) {
            fixed = CopyPropagator::new().run(fixed);
            if conf.verbose >= Verbosity::Moderate {
                println!("[[copy propagation]]");
                println!("{}", fixed);
            }
        }
        if conf.optimizations.contains(&Optimization::AssertionRemoval) {
            fixed = AssertionRemover::new(&fixed).optimize(fixed);
            if conf.verbose >= Verbosity::Moderate {
                println!("[[assertion removal]]");
                println!("{}", fixed);
            }
        }
        fixed
    };

    match cli.target {
        Some(SSA) => {
            if let Some(ref args) = cli.execute {
                let mut interp = interp::ssa::Interp::new();
                let value = interp
                    .run(&ssa, args)
                    .map_err(|e| format!("Error interpreting program: {}", e))?;
                println!("{}", value);
            } else {
                // only print SSA if not printed above under higher verbosity
                if conf.verbose < Verbosity::Moderate {
                    println!("{}", ssa);
                }
            }
            return Ok(());
        }
        _ => {}
    }

    // backend: analysis: liveness analysis (initial)
    // from this step on, the correct liveness analysis result is always attached to ssa
    let ssa = LivenessAnalyzer::new(&ssa).analyze(ssa);

    // backend: optimization: dead code elimination
    let ssa = {
        // an iterative approach of removing unused variables and parameters
        let mut live = ssa;

        if conf.optimizations.contains(&Optimization::DeadCodeElimination) {
            let mut round = 0;
            loop {
                let mut remover = UnusedRemover::new();
                let ssa = remover.run(live);
                live = LivenessAnalyzer::new(&ssa).analyze(ssa);

                match remover.progress() {
                    None => {
                        if conf.verbose >= Verbosity::Moderate {
                            println!("[[remover made no progress, finalizing]]");
                            println!();
                        }
                        break;
                    }
                    Some((params, vars)) => {
                        round += 1;
                        if conf.verbose >= Verbosity::Moderate {
                            println!("[[removing unused params]]");
                            println!("{}", params);
                            println!();
                            println!("[[removing unused vars]]");
                            println!("{}", vars);
                            println!();
                            println!("[[remover made progress, reiterating (round {})]]", round);
                            println!();
                        }
                        if conf.verbose >= Verbosity::Mouthful {
                            println!("[[liveness analysis (round {})]]", round);
                            println!("{:?}", live);
                        }
                    }
                }
            }
        }

        live
    };
    // backend: analysis: liveness analysis (final)
    if conf.verbose >= Verbosity::Moderate {
        println!("[[liveness analysis (final)]]");
        println!("{:?}", ssa);
    }

    // backend: optimization: register allocation
    let conflicts = ConflictAnalysis::new(&ssa);
    if let Some(ref path) = cli.interference {
        conflicts.interference.dot(path);
    }
    match cli.target {
        Some(Graph) => {
            // backend: optimization: register allocation - interference graph
            if conf.verbose >= Verbosity::Moderate {
                println!("[[interference graph]]");
            }
            println!("{}", conflicts.interference);
            return Ok(());
        }
        Some(ElimOrder) => {
            // backend: optimization: register allocation - perfect elimination order
            if conf.verbose >= Verbosity::Moderate {
                println!("[[perfect elimination order]]");
            }
            println!("{}", conflicts.order);
            return Ok(());
        }
        _ => {}
    }
    if conf.verbose >= Verbosity::Moderate {
        println!("[[interference graph]]");
        if conf.verbose >= Verbosity::Mouthful {
            println!("{}", conflicts.interference);
        } else {
            println!("(omitted)");
            println!();
        }
    }
    if conf.verbose >= Verbosity::Moderate {
        println!("[[perfect elimination order]]");
        println!("{}", conflicts.order);
        println!();
    }

    // backend: optimization: register allocation - registers available
    let registers = match &cli.registers {
        Some(selection) => selection.to_registers(),
        None => Reg::ALLOCATABLE.to_vec(),
    };
    if conf.verbose >= Verbosity::Moderate {
        println!("[[registers available]]");
        if registers.is_empty() {
            println!("(none)");
            println!();
        } else {
            println!("{}", registers.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(", "));
            println!();
        }
    }

    // backend: optimization: register allocation - graph coloring
    let mut allocator = RegisterAllocator::new();
    if conf.verbose >= Verbosity::Mouthful {
        println!("[[coloring trace]]");
    }
    allocator.graph_color(
        conflicts,
        &registers,
        matches!(cli.target, Some(Coloring)) || conf.verbose >= Verbosity::Mouthful,
    );
    match cli.target {
        Some(Coloring) => {
            println!();
            if conf.verbose >= Verbosity::Moderate {
                println!("[[coloring]]");
            }
            println!("{}", allocator.assignment);
            return Ok(());
        }
        _ => {}
    }
    if conf.verbose >= Verbosity::Moderate {
        println!();
        println!("[[coloring]]");
        println!("{}", allocator.assignment);
    }

    // backend: code generation
    let mut emitter = Emitter::from(allocator);
    emitter.emit_prog(&ssa);
    let asm = emitter.to_asm();
    let txt = instrs_to_string(&asm);

    match (cli.target, &cli.execute) {
        // Assembly and not execute
        (Some(Asm) | None, None) => {
            println!("{}", txt);
            return Ok(());
        }
        _ => {}
    }
    // if the target is assembly and execute is true, we treat it the same as executable execute.

    // target is executable
    if conf.verbose >= Verbosity::Moderate {
        println!("ASM:\n{}", txt);
    }
    let rt = cli.runtime.clone().unwrap_or(PathBuf::from("runtime/stub.rs"));
    let o_dir = PathBuf::from("runtime");
    let exe_fname = cli.output.clone().unwrap_or(PathBuf::from("runtime/stub.exe"));
    link(&txt, &rt, &o_dir, &exe_fname)?;
    // if execute is set, run the executable
    if let Some(ref args) = cli.execute {
        run(&exe_fname, args, &mut std::io::stdout())?;
    }
    Ok(())
}
fn main() {
    let cli = Cli::parse();

    match run_cli(&cli) {
        Ok(()) => {}
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    };
}

#![allow(unused)]

macro_rules! mk_test {
    ($test_name:ident, $file_name:expr, $input:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_file($file_name, $input, $expected_output)
        }
    };
}

macro_rules! mk_frontend_test {
    ($test_name:ident, $file_name:expr, $input:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_frontend($file_name, $input, $expected_output)
        }
    };
}

macro_rules! mk_middle_end_test {
    ($test_name:ident, $file_name:expr, $input:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_middle_end($file_name, $input, $expected_output)
        }
    };
}

macro_rules! mk_fail_test {
    ($test_name:ident, $file_name:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_fail($file_name, [], $expected_output)
        }
    };
}

macro_rules! mk_dyn_fail_test {
    ($test_name:ident, $file_name:expr, $input:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_fail($file_name, $input, $expected_output)
        }
    };
}

/*
 * YOUR TESTS GO HERE
 */

mod public_adder {
    use super::*;
    /* The following defines a test named "test1" that compiles and runs the file
     * examples/add1.dbk and I expect it to return 43 with input 42
     */
    mk_test!(test1, "add1.dbk", ["42"], "43");

    /* The following test is similar to test1, but instead of using the
     * full compiler pipeline, it runs the frontend and then tests that
     * the interpreter outputs the desired result
     */
    mk_frontend_test!(test1_frontend, "add1.dbk", ["42"], "43");

    /* Similarly, the following test uses your frontend followed by your
     * middleend, then runs the SSA interpreter on the resulting
     * intermediate representation.
     */
    mk_middle_end_test!(test1_middleend, "add1.dbk", ["42"], "43");

    /*
     * The following test checks that when run on exmaples/free.dbk, the
     * compiler produces an error containing the substring "variable z unbound".
     */
    mk_fail_test!(free, "free.dbk", "variable \"z\" unbound");

    mk_fail_test!(let_dupe, "let_dupe.dbk", "\"x\" defined twice in let-expression");
}

/* ----------------------- Public Cobra Tests ---------------------- */
mod public_cobra {
    use super::*;
    // one regression test for tail recursion
    mk_test!(test_tail_recursive_constant_space_3, "peano.dbk", ["100000000"], "100000001");
    // one for testing extern with few arguments
    mk_test!(test_print_3, "print.dbk", ["0"], "1\n2\n3\n4\n24");
    // one for testing extern with many arguments
    mk_test!(
        test_big_extern_nine_3,
        "extern_big_nine.dbk",
        ["0"],
        "x1: -1
x2: -2
x3: -3
x4: -4
x5: -5
x6: -6
x7: -7
x8: -8
x9: -9
-46
"
    );
    // one for testing internal call with few arguments
    mk_test!(test_simple_non_tail_call_1_3, "local_non_tail_call.dbk", ["1"], "3");
    // one for testing internal call with many arguments
    mk_test!(test_big_local_3, "local_big_eight.dbk", ["1"], "40319");
    // one for testing internal call with recursion
    mk_test!(test_non_tail_recursion_3, "non_tail_factorial.dbk", ["5"], "120");
    // one for testing recursive internal call with capture
    mk_test!(test_rec_call_capture_3, "pow.dbk", ["2"], "256");
}

mod public_diamondback {
    use super::*;
    mk_dyn_fail_test!(test_out_of_bounds, "out_of_bounds.dbk", [], "index 4 out of bounds");
    mk_dyn_fail_test!(test_overflow_3_2, "overflow3.dbk", [], "arithmetic operation overflowed");
    mk_test!(test_array_empty_2, "array_empty.dbk", ["483"], "[[], 483, []]");
    mk_test!(
        test_array_cyclic_tree,
        "array_cyclic_tree.dbk",
        ["0", "0", "0"],
        "[[395, 476, 1453, <loop>], 0, [[], <loop>, <loop>, [395, 476, 1453, <loop>], <loop>, []]]"
    );
}

mod ana;
mod graph_parser;
mod public_optimizations {
    use super::*;
    use graph_parser::*;
    use snake_optimizations::{
        backend::*, frontend::*, middle_end::*, parser::*, runner::*, txt::*,
    };

    mod assertion_removal {
        use super::*;

        fn test(
            src_file: impl Into<PathBuf>, expected_ssa_file: impl Into<PathBuf>,
        ) -> Result<(), String> {
            let inp =
                read_file(&src_file.into()).map_err(|e| format!("Error reading file: {}", e))?;
            let file_info = FileInfo::new(&inp);
            let raw_ast = ProgParser::new()
                .parse(&inp)
                .map_err(|e| format!("Error parsing program: {}", e))?;

            let mut resolver = Resolver::new();
            let resolved_ast = resolver
                .resolve_prog(raw_ast)
                .map_err(|e| format!("Error resolving ast: {}", file_info.report_error(e)))?;

            let mut lowerer = Lowerer::from(resolver);
            let ssa = lowerer.lower_prog(resolved_ast);
            let ssa = AssertionRemover::new(&ssa).optimize(ssa);

            let ssa_str = format!("{}", ssa);
            let expected_ssa_str = read_file(&expected_ssa_file.into())
                .map_err(|e| format!("Error reading file: {}", e))?;

            assert_eq!(ssa_str.trim(), expected_ssa_str.trim());
            Ok(())
        }

        #[test]
        fn simple_add_3() -> Result<(), String> {
            test("examples/assertions/simple_add.dbk", "examples/assertions/simple_add.ssa")
        }
        #[test]
        fn loop1_3() -> Result<(), String> {
            test("examples/assertions/loop1.dbk", "examples/assertions/loop1.ssa")
        }
        #[test]
        fn extern0_3() -> Result<(), String> {
            test("examples/assertions/extern0.dbk", "examples/assertions/extern0.ssa")
        }
    }

    mod liveness_and_conflict_analyses {
        use super::*;

        fn test(
            src_file: impl Into<PathBuf>, graph_file: impl Into<PathBuf>,
        ) -> Result<(), String> {
            let inp =
                read_file(&src_file.into()).map_err(|e| format!("Error reading file: {}", e))?;
            let file_info = FileInfo::new(&inp);

            let raw_ast = ProgParser::new()
                .parse(&inp)
                .map_err(|e| format!("Error parsing program: {}", e))?;

            let mut resolver = Resolver::new();
            let resolved_ast = resolver
                .resolve_prog(raw_ast)
                .map_err(|e| format!("Error resolving ast: {}", file_info.report_error(e)))?;

            let mut lowerer = Lowerer::from(resolver);
            let ssa = lowerer.lower_prog(resolved_ast);
            let ssa = CopyPropagator::new().run(ssa);

            let live_ssa = LivenessAnalyzer::new(&ssa).analyze(ssa);
            let conflicts = ConflictAnalysis::new(&live_ssa);

            let graph = GraphParser::new()
                .parse(&format!("graph {}", conflicts.interference))
                .map_err(|e| format!("Error parsing graph: {}", e))?;
            let expected_graph = GraphParser::new()
                .parse(&format!(
                    "graph {}",
                    read_file(&graph_file.into())
                        .map_err(|e| format!("Error reading file: {}", e))?
                ))
                .map_err(|e| format!("Error parsing graph: {}", e))?;

            ana::should_be_same_graph(&graph, &expected_graph)?;
            Ok(())
        }

        #[test]
        fn chain_1() -> Result<(), String> {
            test("examples/graphs/chain.dbk", "examples/graphs/chain.graph")
        }

        #[test]
        fn itail_reuse_test_1() -> Result<(), String> {
            test("examples/graphs/itail_reuse.dbk", "examples/graphs/itail_reuse.graph")
        }
        #[test]
        fn if_test_1() -> Result<(), String> {
            test("examples/graphs/if.dbk", "examples/graphs/if.graph")
        }
        #[test]
        fn param_test_1() -> Result<(), String> {
            test("examples/graphs/param.dbk", "examples/graphs/param.graph")
        }
    }

    mod graph_coloring {
        use super::*;

        const NO_REG: &'static str = "none";
        const ONE_REG: &'static str = "none+r8";
        const TWO_REGS: &'static str = "none+r8+r9";
        const THREE_REGS: &'static str = "none+r8+r9+r10";
        const FOUR_REGS: &'static str = "none+r8+r9+r10+r11";
        const FIVE_REGS: &'static str = "none+r8+r9+r10+r11+r12";

        fn test(
            regs: &'static str, allow_spills: bool, src_file: impl Into<PathBuf>,
            expected_graph_file: impl Into<PathBuf>,
        ) -> Result<(), String> {
            use snake_optimizations::cli::RegisterSelection;
            use std::str::FromStr;
            let inp =
                read_file(&src_file.into()).map_err(|e| format!("Error reading file: {}", e))?;
            let file_info = FileInfo::new(&inp);

            let raw_ast = ProgParser::new()
                .parse(&inp)
                .map_err(|e| format!("Error parsing program: {}", e))?;

            let mut resolver = Resolver::new();
            let resolved_ast = resolver
                .resolve_prog(raw_ast)
                .map_err(|e| format!("Error resolving ast: {}", file_info.report_error(e)))?;

            let mut lowerer = Lowerer::from(resolver);
            let ssa = lowerer.lower_prog(resolved_ast);
            let ssa = CopyPropagator::new().run(ssa);

            let live_ssa = LivenessAnalyzer::new(&ssa).analyze(ssa);
            let conflicts = ConflictAnalysis::new(&live_ssa);

            let mut allocator = RegisterAllocator::new();
            allocator.graph_color(
                conflicts,
                &RegisterSelection::from_str(regs).unwrap().to_registers(),
                false,
            );
            let coloring =
                allocator.assignment.iter().map(|(k, v)| (k.to_string(), v.to_owned())).collect();
            let graph = GraphParser::new()
                .parse(&format!(
                    "graph {}",
                    read_file(&expected_graph_file.into())
                        .map_err(|e| format!("Error reading file: {}", e))?
                ))
                .map_err(|e| format!("Error parsing graph: {}", e))?;

            let () = crate::ana::valid_coloring(&graph, &coloring)?;
            assert!(
                allow_spills || (crate::ana::count_spills(&coloring) == 0),
                "You spilled when you didn't need to"
            );

            Ok(())
        }

        #[test]
        fn chain_1() -> Result<(), String> {
            test(THREE_REGS, false, "examples/graphs/chain.dbk", "examples/graphs/chain.graph")
        }

        #[test]
        fn chain_spill_1() -> Result<(), String> {
            test(TWO_REGS, true, "examples/graphs/chain.dbk", "examples/graphs/chain.graph")
        }

        #[test]
        fn chain_spill_all_1() -> Result<(), String> {
            test(NO_REG, true, "examples/graphs/chain.dbk", "examples/graphs/chain.graph")
        }

        #[test]
        fn if_1() -> Result<(), String> {
            test(THREE_REGS, false, "examples/graphs/if.dbk", "examples/graphs/if.graph")
        }

        #[test]
        fn itail_reuse_1() -> Result<(), String> {
            test(
                ONE_REG,
                false,
                "examples/graphs/itail_reuse.dbk",
                "examples/graphs/itail_reuse.graph",
            )
        }

        #[test]
        fn itail_reuse_spill_all_1() -> Result<(), String> {
            test(
                NO_REG,
                true,
                "examples/graphs/itail_reuse.dbk",
                "examples/graphs/itail_reuse.graph",
            )
        }

        #[test]
        fn param_1() -> Result<(), String> {
            test(TWO_REGS, false, "examples/graphs/param.dbk", "examples/graphs/param.graph")
        }

        #[test]
        fn param_spill_1() -> Result<(), String> {
            test(ONE_REG, true, "examples/graphs/param.dbk", "examples/graphs/param.graph")
        }
    }
}
/*
 * YOUR TESTS END HERE
 */

/* ----------------------- Test Implementation Details ---------------------- */

use snake_optimizations::{interp, runner};
use std::path::{Path, PathBuf};

fn test_example_file(
    f: &str, args: impl IntoIterator<Item = &'static str>, expected: &str,
) -> std::io::Result<()> {
    let tmp_dir = tempfile::TempDir::new()?;
    let mut buf = Vec::new();
    match runner::compile_and_run_file(
        &Path::new(&format!("examples/{}", f)),
        tmp_dir.path(),
        args,
        &mut buf,
    ) {
        Ok(()) => {
            assert_eq!(String::from_utf8_lossy(&buf).trim(), expected.trim())
        }
        Err(e) => {
            assert!(false, "Expected {}, got an error: {}", expected, e)
        }
    }
    Ok(())
}

#[allow(unused)]
fn test_example_frontend(
    f: &str, args: impl IntoIterator<Item = &'static str>, expected: &str,
) -> std::io::Result<()> {
    let res = runner::emit_ast(&Path::new(&format!("examples/{}", f)))
        .and_then(|(_, ast)| interp::ast::Machine::run(&ast, args).map_err(|e| format!("{}", e)));
    match res {
        Ok(v) => assert_eq!(v.to_string(), expected),
        Err(e) => assert!(false, "Expected {}, got an error: {}", expected, e),
    }
    Ok(())
}

#[allow(unused)]
fn test_example_middle_end(
    f: &str, args: impl IntoIterator<Item = &'static str>, expected: &str,
) -> std::io::Result<()> {
    let res = runner::emit_ssa(&Path::new(&format!("examples/{}", f))).and_then(|(_, ssa)| {
        let mut interp = interp::ssa::Interp::new();
        interp.run(&ssa, args).map_err(|e| format!("{}", e))
    });
    match res {
        Ok(v) => assert_eq!(v.to_string(), expected),
        Err(e) => assert!(false, "Expected {}, got an error: {}", expected, e),
    }
    Ok(())
}

fn test_example_fail(
    f: &str, args: impl IntoIterator<Item = &'static str>, includes: &str,
) -> std::io::Result<()> {
    let tmp_dir = tempfile::TempDir::new()?;
    let mut buf = Vec::new();
    match runner::compile_and_run_file(
        &Path::new(&format!("examples/{}", f)),
        tmp_dir.path(),
        args,
        &mut buf,
    ) {
        Ok(()) => {
            assert!(false, "Expected a failure but got: {}", String::from_utf8_lossy(&buf).trim())
        }
        Err(e) => {
            let msg = format!("{}", e);
            assert!(
                msg.contains(includes),
                "Expected error message to include the string \"{}\" but got the error: {}",
                includes,
                msg
            )
        }
    }
    Ok(())
}

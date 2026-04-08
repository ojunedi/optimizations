//! The backend of our compiler translates our intermediate
//! representation into assembly code, mapping intermediate
//! representation variables into concrete memory locations (registers
//! or stack locations).

use crate::ana::*;
use crate::asm::*;
use crate::identifiers::*;
use crate::ssa::*;
use crate::types::*;
use std::collections::BTreeSet;
use std::collections::{HashMap, HashSet};

/// Liveness analysis is a simple iterative data flow analysis that determines
/// which variables are live at a given point in the program.
///
/// It's a backwards dataflow analysis, meaning that the information
/// flows in the reverse of the execution order.
pub struct LivenessAnalyzer {
    /// The live variables at the start of each block, in previous iteration.
    /// Initially, this maps all BlockNames to the empty set
    previous: HashMap<BlockName, HashSet<VarName>>,
    /// The live variables at the start of each block, in current iteration.
    current: HashMap<BlockName, HashSet<VarName>>,
}

impl LivenessAnalyzer {
    pub fn new<T>(prog: &Program<VarName, T>) -> Self {
        fn find_names_prog<T>(
            p: &Program<VarName, T>, blocks: &mut HashMap<BlockName, HashSet<VarName>>,
        ) {
            for block in p.blocks.iter() {
                find_names_basic_block(&block, blocks);
            }
        }
        fn find_names_block_body<T>(
            b: &BlockBody<VarName, T>, blocks: &mut HashMap<BlockName, HashSet<VarName>>,
        ) {
            use BlockBody::*;
            match b {
                Terminator(..) => {}
                Operation { next, .. }
                | AssertType { next, .. }
                | AssertLength { next, .. }
                | AssertInBounds { next, .. }
                | Store { next, .. } => find_names_block_body(next, blocks),
                SubBlocks { blocks: sub_blocks, next, .. } => {
                    for block in sub_blocks.iter() {
                        find_names_basic_block(&block, blocks);
                    }
                    find_names_block_body(next, blocks)
                }
            }
        }
        fn find_names_basic_block<T>(
            b: &BasicBlock<VarName, T>, blocks: &mut HashMap<BlockName, HashSet<VarName>>,
        ) {
            blocks.insert(b.label.clone(), HashSet::new());
            find_names_block_body(&b.body, blocks);
        }
        let mut previous = HashMap::new();
        find_names_prog(prog, &mut previous);
        Self { previous, current: HashMap::new() }
    }

    pub fn analyze<T>(mut self, prog: Program<VarName, T>) -> Program<VarName, LiveSet> {
        let mut prog = self.analyze_prog(prog);
        while self.previous != self.current {
            self.previous = std::mem::take(&mut self.current);
            prog = self.analyze_prog(prog);
        }
        prog
    }

    fn analyze_block_body<T>(&mut self, block: BlockBody<VarName, T>) -> (BlockBody<VarName, LiveSet>, LiveSet){
        match block {
            BlockBody::Terminator(terminator, _) => {
                let mut live = LiveSet::new();
                match &terminator {
                    Terminator::Return(immediate) => {
                        if let Immediate::Var(v) = immediate {
                            live.insert(v.clone());
                        }
                    }
                    Terminator::Branch(branch) => {
                        if let Some(target_live) = self.previous.get(&branch.target) {
                            live.extend(target_live.iter().cloned());
                        }
                        for arg in &branch.args {
                            if let Immediate::Var(v) = arg {
                                live.insert(v.clone());
                            }
                        }
                    },
                    Terminator::ConditionalBranch { cond, thn, els } => {
                        if let Some(live_thn) = self.previous.get(thn) {
                            live.extend(live_thn.iter().cloned());
                        }
                        if let Some(live_els) = self.previous.get(els) {
                            live.extend(live_els.iter().cloned());
                        }
                        if let Immediate::Var(v) = cond {
                            live.insert(v.clone());
                        }
                    }
                }
                (BlockBody::Terminator(terminator, live.clone()), live)
            }
            BlockBody::Operation { dest, op, next, ana: _ } => {
                let (new_next, mut live) = self.analyze_block_body(*next);
                live.remove(&dest);
                match &op {
                    Operation::Immediate(immediate) => {
                        if let Immediate::Var(v) = immediate {
                            live.insert(v.clone());
                        }
                    }
                    Operation::Prim1(_prim1, immediate) => {
                        if let Immediate::Var(v) = immediate {
                            live.insert(v.clone());
                        }
                    }
                    Operation::Prim2(_prim2, immediate, immediate1) => {
                        if let Immediate::Var(v) = immediate {
                            live.insert(v.clone());
                        }
                        if let Immediate::Var(v) = immediate1 {
                            live.insert(v.clone());
                        }
                    }
                    Operation::Call { fun: _, args } => {
                        for arg in args {
                            if let Immediate::Var(v) = arg {
                                live.insert(v.clone());
                            }
                        }
                    }
                    Operation::AllocateArray { len } => {
                        if let Immediate::Var(v) = len {
                            live.insert(v.clone());
                        }
                    }
                    Operation::Load { addr, offset } => {
                        if let Immediate::Var(v) = addr {
                            live.insert(v.clone());
                        }
                        if let Immediate::Var(v) = offset {
                            live.insert(v.clone());
                        }
                    }
                }

                (BlockBody::Operation { dest, op, next: Box::new(new_next), ana: live.clone() }, live)
            }
            BlockBody::SubBlocks { blocks, next, ana: _ } => {

                let (new_next, live) = self.analyze_block_body(*next);

                let new_blocks = blocks.into_iter().map(|block| {
                    let label = block.label.clone();
                    let params = block.params.clone();
                    let (new_body, mut live) = self.analyze_block_body(block.body);
                    // remove block params from live set
                    for p in &params {
                        live.remove(p);
                    }
                    // fixed point iteration
                    self.current.insert(label.clone(), live.iter().cloned().collect());
                    BasicBlock { label, params, body: new_body, ana: live }
                }).collect();

                (BlockBody::SubBlocks { blocks: new_blocks, next: Box::new(new_next), ana: live.clone() }, live)

            }
            BlockBody::AssertType { ty, arg, next, ana } => {
                let (new_next, mut live) = self.analyze_block_body(*next);
                if let Immediate::Var(v) = &arg {
                    live.insert(v.clone());
                }
                (BlockBody::AssertType { ty, arg, next: Box::new(new_next), ana: live.clone() }, live)

            },
            BlockBody::AssertLength { len, next, ana: _ } => {
                let (new_next, mut live) = self.analyze_block_body(*next);
                if let Immediate::Var(v) = &len {
                    live.insert(v.clone());
                }
                (BlockBody::AssertLength { len, next: Box::new(new_next), ana: live.clone() }, live)
            },
            BlockBody::AssertInBounds { bound, arg, next, ana: _ } => {
                let (new_next, mut live) = self.analyze_block_body(*next);
                if let Immediate::Var(v) = &bound {
                    live.insert(v.clone());
                }
                if let Immediate::Var(v) = &arg {
                    live.insert(v.clone());
                }
                (BlockBody::AssertInBounds { bound, arg, next: Box::new(new_next), ana: live.clone() }, live)
            },
            BlockBody::Store { addr, offset, val, next, ana: _ } => {
                let (new_next, mut live) = self.analyze_block_body(*next);
                if let Immediate::Var(v) = &addr {
                    live.insert(v.clone());
                }
                if let Immediate::Var(v) = &offset {
                    live.insert(v.clone());
                }
                if let Immediate::Var(v) = &val {
                    live.insert(v.clone());
                }
                (BlockBody::Store { addr, offset, val, next: Box::new(new_next), ana: live.clone() }, live)
            }
        }
    }

    /// Analyzes the program, filling in the live sets. Uses the
    /// information from self.previous for blocks in this round, but
    /// also sets the information in self.current for the result of
    /// this round.
    fn analyze_prog<T>(&mut self, prog: Program<VarName, T>) -> Program<VarName, LiveSet> {

        let blocks = prog.blocks.into_iter().map(|block| {
            let label = block.label.clone();
            let params = block.params.clone();
            let (new_body, mut live) = self.analyze_block_body(block.body);

            // remove block params from live set
            for p in &params {
                live.remove(p);
            }

            // fixed point iteration
            self.current.insert(label.clone(), live.iter().cloned().collect());
            BasicBlock { label, params, body: new_body, ana: live }

        }).collect();

        Program {
            externs: prog.externs,
            funs: prog.funs,
            blocks
        }

    }
}

/// Remove (directly) unused parameters and variables from the program.
///
/// This is a simple DCE (dead code elimination) pass.
/// It removes unused parameters and variables from the program using live set;
/// however, during this process, it also invalidates the live set.
///
/// Combined with further liveness analysis, we can use an iterative approach
/// to remove all unused parameters and variables.
pub struct UnusedRemover {
    /// A mapping from function names to the blocks they contain.
    fun_to_block: HashMap<FunName, BlockName>,
    /// Keeps a set of removed parameters for each block.
    params: UnusedBlockParams,
    /// Keeps a set of removed variables.
    vars: UnusedVarSet,
}

impl UnusedRemover {
    pub fn new() -> Self {
        Self {
            fun_to_block: HashMap::new(),
            params: UnusedBlockParams::new(),
            vars: UnusedVarSet::new(),
        }
    }

    pub fn progress(self) -> Option<(UnusedBlockParams, UnusedVarSet)> {
        if self.params.iter().any(|(_, removed)| !removed.is_empty()) || !self.vars.is_empty() {
            Some((self.params, self.vars))
        } else {
            None
        }
    }

    pub fn run(&mut self, prog: Program<VarName, LiveSet>) -> Program<VarName, Nil> {
        let Program { externs, funs, blocks } = prog;
        // first get all toplevel block parameters to be removed
        blocks.iter().for_each(|block| self.build_block(block));
        // then remove the parameters from the functions
        let funs = funs.into_iter().map(|fun| self.run_fun(fun)).collect();
        // finally remove proceed with the blocks,
        // knowing what to do with arguments of function calls
        let blocks = blocks.into_iter().map(|block| self.run_block(block)).collect();
        Program { externs, funs, blocks }
    }

    fn build_block(&mut self, block: &BasicBlock<VarName, LiveSet>) {
        let BasicBlock { label, params, body, .. } = block;
        let (unused, _) =
            self.trans_block_params(params.clone(), HashSet::from_iter(body.analysis()));
        self.params.insert(label.clone(), unused);
        self.build_block_body(body);
    }

    fn build_block_body(&mut self, body: &BlockBody<VarName, LiveSet>) {
        // recursively build the block body, bottom-up
        if let Some(succ) = body.successor() {
            self.build_block_body(succ)
        }
        match body {
            BlockBody::SubBlocks { blocks, .. } => {
                for block in blocks.iter() {
                    self.build_block(block);
                }
            }
            _ => {}
        }
    }

    fn trans_block_params(
        &mut self, params: impl IntoIterator<Item = VarName>, live: HashSet<&VarName>,
    ) -> (HashSet<usize>, Vec<VarName>) {
        use itertools::{Either, Itertools as _};
        params
            .into_iter()
            .enumerate()
            .map(
                |(i, param)| {
                    if live.contains(&param) { Either::Right(param) } else { Either::Left(i) }
                },
            )
            .partition_map(|x| x)
    }

    fn trans_block_args(
        &mut self, target: &BlockName, args: Vec<Immediate<VarName>>,
    ) -> Vec<Immediate<VarName>> {
        let removed = &self.params[target];
        args.into_iter()
            .enumerate()
            .filter_map(|(i, arg)| (!removed.contains(&i)).then_some(arg))
            .collect()
    }

    fn run_fun(&mut self, fun: FunBlock<VarName>) -> FunBlock<VarName> {
        let FunBlock { name, params, body: Branch { target, args }, .. } = fun;
        self.fun_to_block.insert(name.clone(), target.clone());
        let block_params = &self.params[&target];
        let params = params
            .into_iter()
            .enumerate()
            .filter_map(|(i, param)| (!block_params.contains(&i)).then_some(param))
            .collect();
        let body = Branch {
            target,
            args: args
                .into_iter()
                .enumerate()
                .filter_map(|(i, arg)| (!block_params.contains(&i)).then_some(arg))
                .collect(),
        };
        FunBlock { name, params, body, ..fun }
    }

    fn run_block(&mut self, block: BasicBlock<VarName, LiveSet>) -> BasicBlock<VarName, Nil> {
        let BasicBlock { label, params, body, .. } = block;
        let (unused, params) = self.trans_block_params(params, HashSet::from_iter(body.analysis()));
        self.params.insert(label.clone(), unused);

        let body = self.run_block_body(body);
        BasicBlock { label, params, body, ana: Nil }
    }

    fn run_block_body(&mut self, body: BlockBody<VarName, LiveSet>) -> BlockBody<VarName, Nil> {
        let live: HashSet<_> = HashSet::from_iter(
            body.successor()
                .map_or_else(HashSet::new, |succ| succ.analysis().iter().cloned().collect()),
        );
        match body {
            BlockBody::Terminator(Terminator::Branch(Branch { target, args }), ..) => {
                // check if we need to remove any arguments if it's a branch
                let args = self.trans_block_args(&target, args);
                BlockBody::Terminator(Terminator::Branch(Branch { target, args }), Nil)
            }
            BlockBody::Terminator(t, ..) => BlockBody::Terminator(t, Nil),
            BlockBody::Operation { dest, op, next, .. } => {
                // if the destination is not live, we can remove the operation
                // **unless** it's a call, which may contain **side effects**
                if !matches!(op, Operation::Call { .. }) {
                    if self.run_imms(&live, &[&Immediate::Var(dest.clone())]) {
                        return self.run_block_body(*next);
                    }
                }
                // otherwise, we need to keep the operation
                let op = match op {
                    Operation::Call { fun, args } => {
                        // check if we need to remove any arguments if it's a call
                        if let Some(block) = self.fun_to_block.get(&fun).cloned() {
                            // if the function is internal, try to remove arguments
                            let args = self.trans_block_args(&block, args);
                            Operation::Call { fun, args }
                        } else {
                            Operation::Call { fun, args }
                        }
                    }
                    op => op,
                };
                BlockBody::Operation {
                    dest,
                    op,
                    next: Box::new(self.run_block_body(*next)),
                    ana: Nil,
                }
            }
            BlockBody::SubBlocks { blocks, next, .. } => {
                let blocks: Vec<_> =
                    blocks.into_iter().map(|block| self.run_block(block)).collect();
                BlockBody::SubBlocks {
                    blocks,
                    next: Box::new(self.run_block_body(*next)),
                    ana: Nil,
                }
            }
            BlockBody::AssertType { ty, arg, next, .. } => BlockBody::AssertType {
                ty,
                arg,
                next: Box::new(self.run_block_body(*next)),
                ana: Nil,
            },
            BlockBody::AssertLength { len, next, .. } => BlockBody::AssertLength {
                len,
                next: Box::new(self.run_block_body(*next)),
                ana: Nil,
            },
            BlockBody::AssertInBounds { bound, arg, next, .. } => BlockBody::AssertInBounds {
                bound,
                arg,
                next: Box::new(self.run_block_body(*next)),
                ana: Nil,
            },
            BlockBody::Store { addr, offset, val, next, .. } => BlockBody::Store {
                addr,
                offset,
                val,
                next: Box::new(self.run_block_body(*next)),
                ana: Nil,
            },
        }
    }

    /// if all the arguments are not live, we can remove all of them
    /// returns true if we made progress
    fn run_imms(&mut self, live: &HashSet<VarName>, args: &[&Immediate<VarName>]) -> bool {
        let victims = args
            .iter()
            .filter_map(|arg| match arg {
                Immediate::Var(var) if !live.contains(var) => Some(var.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        let progress = victims.len() == args.len();
        if progress {
            self.vars.extend(victims);
        }
        progress
    }
}

// Constructs the register interference graph and perfect elimination
// order from an SSA program with liveness information.
pub struct ConflictAnalysis {
    /// interference graph:

    /// 1. All variables in the program should be in the graph, except
    /// for function block and extern function parameters, since their
    /// location is pre-determined by the calling convention

    /// 2. Two variables should share an edge if they cannot be in the same register:
    ///    - If x != y are parameters to the same block, they conflict
    ///    - If x is assigned to while y != x is live, then x, y conflict
    pub interference: Graph<VarName>,

    /// elimination order to use in Chaitin's algorithm
    /// If a variable x syntactically dominates a variable y then it should occur *earlier* in the ordering
    pub order: PerfectEliminationOrder,
}

impl ConflictAnalysis {
    pub fn new(prog: &Program<VarName, LiveSet>) -> Self {
        let mut analysis =
            ConflictAnalysis { interference: Graph::new(), order: PerfectEliminationOrder::new() };
        analysis.build_prog(prog);
        analysis
    }


    fn build_block_body(&mut self, body: &BlockBody<VarName, LiveSet>) {

        match body {
            BlockBody::Terminator(_terminator, _) => {},
            BlockBody::Operation { dest, op, next, ana } => {
                for v in next.analysis().iter() {
                    if v != dest {
                        self.interference.insert_edge(dest.clone(), v.clone());
                    }
                }
                self.interference.insert_vertex(dest.clone());
                self.order.push(dest.clone());
                self.build_block_body(next);
            }
            BlockBody::SubBlocks { blocks, next, ana } => {
                for block in blocks {
                    self.build_basic_block(block);
                }
                self.build_block_body(next);
            }
            // Store, Assert*, we can just recurse into next
            _ => {
                if let Some(next) = body.successor() {
                  self.build_block_body(next);
              }

            }
        }

    }

    fn build_basic_block(&mut self, block: &BasicBlock<VarName, LiveSet>) {
        // block params conflict with each other, add to graph and elimination order
        for (i, p1) in block.params.iter().enumerate() {
            self.interference.insert_vertex(p1.clone());
            for p2 in &block.params[i + 1..] {
                self.interference.insert_edge(p1.clone(), p2.clone());
            }
        }
        self.order.extend(block.params.iter().cloned());
        self.build_block_body(&block.body);
    }

    // Traverse the program, which is annotated with liveness information, building up the interference graph as well as the elimination order.
    fn build_prog(&mut self, Program { externs: _, funs: _, blocks }: &Program<VarName, LiveSet>) {

        for block in blocks {
            self.build_basic_block(block);
        }



    }
}

/// Colors the provided interference graph using the provided
/// elimination ordering.
pub struct RegisterAllocator {
    // assignment of registers or spills to variables
    pub assignment: Coloring,
    // reverse color mapping, to determine which registers are free
    regs_to_vars: HashMap<Reg, HashSet<VarName>>,
    // Spills for non-volatile registers that need to be saved
    callee_saves: HashMap<Reg, i32>,
    /// Internal state for determining where to spill
    max_spill: i32,
}

impl RegisterAllocator {
    pub fn new() -> Self {
        Self {
            max_spill: 0,
            assignment: Coloring::new(),
            regs_to_vars: HashMap::new(),
            callee_saves: HashMap::new(),
        }
    }
    /// Use this function when to get the next valid spill location.
    fn spill(&mut self) -> i32 {
        self.max_spill += 1;
        self.max_spill
    }

    // g: the graph to be colored
    // remaining: the variables that still need to be colored
    // all_regs: the registers available to use as colors
    // log: if true, then the verbose flag is set, and feel free to print debugging information
    fn chaitin(
        &mut self, mut g: Graph<VarName>, mut remaining: Vec<VarName>, all_regs: &[Reg], log: bool,
    ) {
        todo!("implement Chaitin's algorithm for graph coloring")
    }

    pub fn graph_color(&mut self, conflicts: ConflictAnalysis, registers: &[Reg], log: bool) {
        if log {
            println!("Elimination order:\n{}", conflicts.order);
            println!("Register order:\n{:?}", registers);
        }
        // First, color the graph
        self.chaitin(
            conflicts.interference,
            conflicts.order.0.into_iter().collect(),
            registers,
            log,
        );
        // Then, spill any used non-volatile registers
        let assns: Vec<_> = self.assignment.0.iter().map(|(_, loc)| loc.clone()).collect();
        for loc in assns.iter() {
            match loc {
                Allocation::Reg(reg) => {
                    if reg.is_non_volatile() && !self.callee_saves.contains_key(reg) {
                        let new_loc = self.spill();
                        self.callee_saves.insert(*reg, new_loc);
                    }
                }
                Allocation::Spill(_) => {}
            }
        }
    }
}

impl Reg {
    pub const ALL: [Reg; 16] = [
        Reg::Rax,
        Reg::Rbx,
        Reg::Rcx,
        Reg::Rdx,
        Reg::Rdi,
        Reg::Rsi,
        Reg::Rsp,
        Reg::Rbp,
        Reg::R8,
        Reg::R9,
        Reg::R10,
        Reg::R11,
        Reg::R12,
        Reg::R13,
        Reg::R14,
        Reg::R15,
    ];

    pub const VOLATILE: [Reg; 10] = [
        Reg::Rax,
        Reg::Rcx,
        Reg::Rdx,
        Reg::Rdi,
        Reg::Rsi,
        Reg::Rsp,
        Reg::R8,
        Reg::R9,
        Reg::R10,
        Reg::R11,
    ];

    pub const NON_VOLATILE: [Reg; 6] = [Reg::Rbx, Reg::Rbp, Reg::R12, Reg::R13, Reg::R14, Reg::R15];

    pub fn is_volatile(&self) -> bool {
        match self {
            Reg::Rax
            | Reg::Rcx
            | Reg::Rdx
            | Reg::Rdi
            | Reg::Rsi
            | Reg::Rsp
            | Reg::R8
            | Reg::R9
            | Reg::R10
            | Reg::R11 => true,
            Reg::Rbx | Reg::Rbp | Reg::R12 | Reg::R13 | Reg::R14 | Reg::R15 => false,
        }
    }

    pub fn is_non_volatile(&self) -> bool {
        !self.is_volatile()
    }

    /// The registers that can be used for allocations.
    /// Rax and R10 are excluded because they are used as the temporary registers.
    /// Rsp is excluded because it holds the stack pointer.

    /// The ordering reflects the order in which they are
    /// chosen. Argument registers are first as this reduces the cost
    /// of branching in a function block
    pub const ALLOCATABLE: [Reg; 13] = [
        Reg::Rdi,
        Reg::Rsi,
        Reg::Rdx,
        Reg::Rcx,
        Reg::R8,
        Reg::R9,
        Reg::R11,
        Reg::Rbx,
        Reg::Rbp,
        Reg::R12,
        Reg::R13,
        Reg::R14,
        Reg::R15,
    ];

    pub const ALLOCATABLE_VOLATILE: [Reg; 7] =
        [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9, Reg::R11];

    pub const ALLOCATABLE_NON_VOLATILE: [Reg; 6] =
        [Reg::Rbx, Reg::Rbp, Reg::R12, Reg::R13, Reg::R14, Reg::R15];

    /// The System-V calling convention uses the following registers for the first 6 arguments.
    pub const ARGS: [Reg; 6] = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];
}

impl Into<Reg8> for Reg {
    fn into(self) -> Reg8 {
        match self {
            Reg::Rax => Reg8::Al,
            Reg::Rbx => Reg8::Bl,
            Reg::Rdx => Reg8::Dl,
            Reg::Rcx => Reg8::Cl,
            Reg::Rsi => Reg8::Sil,
            Reg::Rdi => Reg8::Dil,
            Reg::Rsp => Reg8::Spl,
            Reg::Rbp => Reg8::Bpl,
            Reg::R8 => Reg8::R8b,
            Reg::R9 => Reg8::R9b,
            Reg::R10 => Reg8::R10b,
            Reg::R11 => Reg8::R11b,
            Reg::R12 => Reg8::R12b,
            Reg::R13 => Reg8::R13b,
            Reg::R14 => Reg8::R14b,
            Reg::R15 => Reg8::R15b,
        }
    }
}

impl BinArgs {
    /// Create a BinArgs from a destination register and a source allocation.
    ///
    /// ## Panic
    ///
    /// Having the same register for both dst and src (e.g. `op reg, reg`).
    pub fn from_alloc(dst: Reg, src: Allocation) -> Self {
        match src {
            Allocation::Reg(src) if src == dst => unreachable!(),
            Allocation::Reg(src) => BinArgs::ToReg(dst, Arg32::Reg(src)),
            Allocation::Spill(spill) => {
                BinArgs::ToReg(dst, Arg32::Mem(MemRef { reg: Reg::Rsp, offset: -8 * spill }))
            }
        }
    }

    /// Create a BinArgs from a destination allocation and a source register.
    ///
    /// ## Panic
    ///
    /// Having the same register for both dst and src (e.g. `op reg, reg`).
    pub fn to_alloc(dst: Allocation, src: Reg) -> Self {
        match dst {
            Allocation::Reg(dst) if dst == src => unreachable!(),
            Allocation::Reg(dst) => BinArgs::ToReg(dst, Arg32::Reg(src)),
            Allocation::Spill(spill) => {
                BinArgs::ToMem(MemRef { reg: Reg::Rsp, offset: -8 * spill }, Reg32::Reg(src))
            }
        }
    }
}

impl MovArgs {
    /// Create a MovArgs from a destination allocation and a source register.
    ///
    /// ## Panic
    ///
    /// Having the same register for both dst and src (e.g. `mov reg, reg`).
    pub fn to_alloc(dst: Allocation, src: Reg) -> Self {
        match dst {
            Allocation::Reg(dst) if dst == src => unreachable!(),
            Allocation::Reg(dst) => MovArgs::ToReg(dst, Arg64::Reg(src)),
            Allocation::Spill(spill) => {
                MovArgs::ToMem(MemRef { reg: Reg::Rsp, offset: -8 * spill }, Reg32::Reg(src))
            }
        }
    }
}

/// Example runtime error codes.
#[repr(u64)]
pub enum SnakeErr {
    ArithmeticOverflow = 0,
    ExpectedNum = 1,
    ExpectedBool = 2,
    ExpectedArray = 3,
    NegativeLength = 4,
    IndexOutOfBounds = 5,
}

impl SnakeErr {
    const COUNT: usize = 6;
}

impl From<usize> for SnakeErr {
    fn from(value: usize) -> Self {
        match value {
            0 => SnakeErr::ArithmeticOverflow,
            1 => SnakeErr::ExpectedNum,
            2 => SnakeErr::ExpectedBool,
            3 => SnakeErr::ExpectedArray,
            4 => SnakeErr::NegativeLength,
            5 => SnakeErr::IndexOutOfBounds,
            _ => panic!("Invalid SnakeErr value"),
        }
    }
}

impl std::fmt::Display for SnakeErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SnakeErr::ArithmeticOverflow => write!(f, "arithmetic_overflow_err"),
            SnakeErr::ExpectedNum => write!(f, "expected_num_err"),
            SnakeErr::ExpectedBool => write!(f, "expected_bool_err"),
            SnakeErr::ExpectedArray => write!(f, "expected_array_err"),
            SnakeErr::NegativeLength => write!(f, "negative_length_err"),
            SnakeErr::IndexOutOfBounds => write!(f, "index_out_of_bounds_err"),
        }
    }
}

pub struct Emitter {
    /// The output buffer for the sequence of instructions we are generating.
    instrs: Vec<Instr>,
    /// Register Allocation info
    allocation: RegisterAllocator,
}

impl From<RegisterAllocator> for Emitter {
    fn from(allocation: RegisterAllocator) -> Self {
        Emitter { instrs: Vec::new(), allocation }
    }
}

type BlockEnv = im::HashMap<BlockName, Vec<Allocation>>;
impl Emitter {
    pub fn to_asm(self) -> Vec<Instr> {
        self.instrs
    }

    fn emit(&mut self, instr: Instr) {
        self.instrs.push(instr);
    }

    fn resolve(&self, x: &VarName) -> Allocation {
        match self.allocation.assignment.get(x) {
            Some(a) => *a,
            None => {
                unreachable!("Didn't find {} in allocation {}", x, self.allocation.assignment);
            }
        }
    }

    fn resolve_imm(&self, imm: &Immediate<VarName>) -> Immediate<Allocation> {
        match imm {
            Immediate::Const(n) => Immediate::Const(*n),
            Immediate::Var(x) => Immediate::Var(self.resolve(x)),
        }
    }

    /// Resolve to an allocation that can be used as the destination of a binary operation.
    /// The following invariants should be checked before calling this function:
    ///
    /// 1. input should not be constant (e.g. 42) because we said so in the middle-end
    /// 2. input should not be rax or r10 because they are used as temporary registers
    ///
    /// ## Panic
    ///
    /// Panics if invariants are violated.
    fn resolve_to_alloc(&self, imm: &Immediate<VarName>) -> Allocation {
        match imm {
            Immediate::Var(x) => {
                let alloc = self.resolve(x);
                assert!(
                    !matches!(alloc, Allocation::Reg(Reg::Rax | Reg::R10)),
                    "{} is assigned to a temporary register {}",
                    x,
                    alloc
                );
                alloc
            }
            Immediate::Const(n) => unreachable!("Can't assign a constant {} to an allocation", n),
        }
    }

    pub fn emit_prog(&mut self, prog: &Program<VarName, LiveSet>) {
        let Program { externs, funs, blocks } = prog;
        // emit text section
        self.emit(Instr::Section(".text".to_string()));
        self.emit(Instr::Global("entry".to_string()));

        // emit the user-defined externs
        for ext in externs.iter() {
            self.emit_extern(ext);
        }

        // emit error handlers
        for i in 0..SnakeErr::COUNT {
            self.emit(Instr::Label(SnakeErr::from(i).to_string()));
            self.emit(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Signed(i as i64))));
            match SnakeErr::from(i) {
                SnakeErr::NegativeLength | SnakeErr::IndexOutOfBounds => {
                    // rax = rax << 1 (encode as snake integer)
                    self.emit(Instr::Sal(ShArgs { reg: Reg::Rax, by: 1 }));
                }
                SnakeErr::ArithmeticOverflow
                | SnakeErr::ExpectedNum
                | SnakeErr::ExpectedBool
                | SnakeErr::ExpectedArray => {}
            }
            self.emit(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))));
            self.emit(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(8))));
            self.emit(Instr::Call(JmpArgs::Label("snake_error".to_string())));
        }

        // Build up the environment for the blocks
        let mut block_env: BlockEnv = im::HashMap::new();
        for block in blocks.iter() {
            block_env.insert(
                block.label.clone(),
                block.params.iter().map(|x| self.resolve(x)).collect(),
            );
        }

        // emit the functions
        for fun in funs.iter() {
            self.emit_fun_block(fun, block_env.clone());
        }

        // finally, emit the blocks
        for block in blocks.iter() {
            self.emit_block(block, block_env.clone());
        }
    }

    fn emit_extern(&mut self, Extern { name, .. }: &Extern<VarName>) {
        self.emit(Instr::Extern(name.hint().to_owned()));
    }

    /// FunBlocks implement functions that support the Sys V calling convention.
    ///
    /// They must
    /// 1. Save the non-volatile registers that are used in the function.
    /// 2. Move the values into the appropriate place on the stack.

    /// FunBlocks move the arguments from their designated place in
    /// the Sys V calling convention to negative offsets from rsp.
    fn emit_fun_block(&mut self, f: &FunBlock<VarName>, block_env: BlockEnv) {
        self.emit(Instr::Label(f.name.to_string()));

        // save the non-volatile registers that are used
        if cfg!(debug_assertions) && !self.allocation.callee_saves.is_empty() {
            self.emit(Instr::Comment("    saving non-volatile registers..".to_string()));
        }
        for (reg, slot) in self.allocation.callee_saves.clone().into_iter() {
            if cfg!(debug_assertions) {
                self.emit(Instr::Comment(format!("        <{}> <- {}", slot, reg)));
            }
            self.emit(store_mem(slot, reg));
        }
        if cfg!(debug_assertions) && !self.allocation.callee_saves.is_empty() {
            self.emit(Instr::Comment("    ..saved".to_string()));
        }

        // lookup the destinations for the parameters
        let dests: Vec<Allocation> = block_env[&f.body.target].clone();

        // resolve the arguments to sources
        let mut srcs: Vec<Immediate<Allocation>> = Vec::new();
        for (reg, _param) in Reg::ARGS.iter().zip(f.params.iter()) {
            srcs.push(Immediate::Var(Allocation::Reg(*reg)));
        }
        for (i, _param) in f.params.iter().enumerate().skip(Reg::ARGS.len()) {
            let j = i + 1;
            let src: i32 = -1 * ((j - Reg::ARGS.len()) as i32);
            srcs.push(Immediate::Var(Allocation::Spill(src)))
        }

        // simultaneously move the arguments from their current location
        // to the body branch parameter allocations
        self.emit_simultaneous_move(dests, srcs);

        // finally, jump to the target
        self.emit(Instr::Jmp(JmpArgs::Label(f.body.target.to_string())));
    }

    fn emit_block(&mut self, block: &BasicBlock<VarName, LiveSet>, block_env: BlockEnv) {
        let BasicBlock { label, body, .. } = block;
        self.emit(Instr::Label(label.to_string()));
        self.emit_block_body(body, block_env);
    }

    fn emit_block_body(&mut self, b: &BlockBody<VarName, LiveSet>, mut block_env: BlockEnv) {
        match b {
            BlockBody::Terminator(t, ..) => {
                self.emit_terminator(t, block_env);
            }
            BlockBody::Operation { dest, op, next, .. } => {
                self.emit_operation(dest, op, next.analysis());
                self.emit_block_body(next, block_env);
            }
            BlockBody::SubBlocks { blocks, next, .. } => {
                for block in blocks.iter() {
                    block_env.insert(
                        block.label.clone(),
                        block.params.iter().map(|x| self.resolve(x)).collect(),
                    );
                }

                // emit the body
                self.emit_block_body(next, block_env.clone());
                // and then emit the sub-blocks
                for block in blocks.iter() {
                    self.emit_block(block, block_env.clone());
                }
            }
            BlockBody::AssertType { ty, arg: of, next, .. } => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!("    assert {} of type {}", of, ty)));
                }
                let mask = ty.mask();
                let tag = ty.tag();
                // rax = of
                self.emit_imm(Allocation::Reg(Reg::Rax), of);
                // rax = rax & mask
                self.emit(Instr::And(BinArgs::ToReg(Reg::Rax, Arg32::Signed(mask as i32))));
                // cmp rax, tag
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Signed(tag as i32))));
                // sub-optimal but it works and the compiler is cleaner
                // rax = of (mov will not alter the flag registers)
                self.emit_imm(Allocation::Reg(Reg::Rax), of);
                // raise error if not equal, assuming the argument is stored in rax
                self.emit(Instr::JCC(
                    ConditionCode::NE,
                    match ty {
                        Type::Int => SnakeErr::ExpectedNum,
                        Type::Bool => SnakeErr::ExpectedBool,
                        Type::Array => SnakeErr::ExpectedArray,
                    }
                    .to_string(),
                ));
                self.emit_block_body(next, block_env);
            }
            BlockBody::AssertLength { len, next, .. } => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!("    assert length {} is non-negative", len)));
                }
                // rax = len
                self.emit_imm(Allocation::Reg(Reg::Rax), len);
                // cmp rax, 0
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Signed(0))));
                // raise error if negative, assuming the argument is stored in rax
                self.emit(Instr::JCC(ConditionCode::L, SnakeErr::NegativeLength.to_string()));
                self.emit_block_body(next, block_env);
            }
            BlockBody::AssertInBounds { bound, arg: of, next, .. } => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!(
                        "    assert {} is in bounds [0, {})",
                        of, bound
                    )));
                }
                // rax = of
                self.emit_imm(Allocation::Reg(Reg::Rax), of);
                // cmp rax, 0
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Signed(0))));
                // raise error if negative, assuming the argument is stored in rax
                self.emit(Instr::JCC(ConditionCode::L, SnakeErr::IndexOutOfBounds.to_string()));
                // cmp bound, of (bound is never constant and is never temporary)
                self.emit(Instr::Cmp(BinArgs::to_alloc(self.resolve_to_alloc(bound), Reg::Rax)));
                // raise error if bound <= of
                self.emit(Instr::JCC(ConditionCode::LE, SnakeErr::IndexOutOfBounds.to_string()));
                self.emit_block_body(next, block_env);
            }
            BlockBody::Store { addr, offset: off, val, next, .. } => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!(
                        "    store [{} + {} * 8] = {}",
                        addr, off, val
                    )));
                }
                // rax = off
                self.emit_imm(Allocation::Reg(Reg::Rax), off);
                // rax = 8 * rax
                self.emit(Instr::IMul(BinArgs::ToReg(Reg::Rax, Arg32::Signed(8))));
                // rax = rax + addr (addr is never constant and is never temporary)
                self.emit(Instr::Add(BinArgs::from_alloc(Reg::Rax, self.resolve_to_alloc(addr))));
                // finally meeting our Thermopylae - only one temporary register doesn't work >_<
                // r10 = val
                self.emit_imm(Allocation::Reg(Reg::R10), val);
                // mov [rax], r10
                self.emit(Instr::Mov(MovArgs::ToMem(
                    MemRef { reg: Reg::Rax, offset: 0 },
                    Reg32::Reg(Reg::R10),
                )));
                self.emit_block_body(next, block_env);
            }
        }
    }

    fn emit_terminator(&mut self, t: &Terminator<VarName>, block_env: BlockEnv) {
        match t {
            Terminator::Return(imm) => {
                // rax = imm
                // (this must happen before restoring callee-saved registers to avoid clobbering imm)
                self.emit_imm(Allocation::Reg(Reg::Rax), imm);
                // restore callee-saved registers
                if cfg!(debug_assertions) && !self.allocation.callee_saves.is_empty() {
                    self.emit(Instr::Comment(format!("    restoring non-volatile registers..")));
                }
                for (reg, slot) in self.allocation.callee_saves.clone() {
                    if cfg!(debug_assertions) {
                        self.emit(Instr::Comment(format!("        {} <- <{}>", reg, slot)));
                    }
                    self.emit(load_mem(reg, slot));
                }
                if cfg!(debug_assertions) && !self.allocation.callee_saves.is_empty() {
                    self.emit(Instr::Comment(format!("    ..restored")));
                }
                self.emit(Instr::Ret);
            }
            Terminator::Branch(branch) => {
                // simultaneously move the arguments from their current location
                // to where the target block wants them to be
                self.emit_simultaneous_move(
                    block_env[&branch.target].clone(),
                    branch.args.iter().map(|a| self.resolve_imm(a)).collect(),
                );
                self.emit(Instr::Jmp(JmpArgs::Label(branch.target.to_string())));
            }
            Terminator::ConditionalBranch { cond, thn, els } => {
                // temporary register rax
                self.emit_imm(Allocation::Reg(Reg::Rax), cond);
                // cmp rax, 0 (false)
                self.emit(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Signed(0))));
                self.emit(Instr::JCC(ConditionCode::NE, thn.to_string()));
                self.emit(Instr::Jmp(JmpArgs::Label(els.to_string())));
            }
        }
    }

    /// pass the live set **after** the operation
    fn emit_operation(&mut self, dest: &VarName, oper: &Operation<VarName>, after_live: &LiveSet) {
        match oper {
            Operation::Immediate(imm) => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!("    operation {} = {}", dest, oper)));
                }

                self.emit_imm(self.resolve(dest), imm);
            }
            Operation::Prim1(op, imm) => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!("    operation {} = {}", dest, oper)));
                }

                let dst = self.resolve(dest);
                // if the destination is a register, we can use it as a temporary register
                // otherwise, use rax as a temporary register
                let tmp = dst.as_reg().unwrap_or(Reg::Rax);
                let mut emit_shift = |shift: fn(ShArgs) -> Instr, by: u8| {
                    self.emit_imm(Allocation::Reg(tmp), imm);
                    self.emit(shift(ShArgs { reg: tmp, by }));
                    // mov dest, tmp if dest is not a register after the operation
                };
                match op {
                    Prim1::BitNot => {
                        // mov r10, -1
                        self.emit(Instr::Mov(MovArgs::ToReg(Reg::R10, Arg64::Signed(-1))));
                        // mov tmp, imm
                        self.emit_imm(Allocation::Reg(tmp), imm);
                        // xor tmp, r10
                        self.emit(Instr::Xor(BinArgs::ToReg(tmp, Arg32::Reg(Reg::R10))));
                        // mov dest, tmp if dest is not a register after the operation
                    }
                    Prim1::BitSal(n) => {
                        emit_shift(Instr::Sal, *n);
                    }
                    Prim1::BitSar(n) => {
                        emit_shift(Instr::Sar, *n);
                    }
                    Prim1::BitShl(n) => {
                        emit_shift(Instr::Shl, *n);
                    }
                    Prim1::BitShr(n) => {
                        emit_shift(Instr::Shr, *n);
                    }
                }
                // if the destination is not a register, the temporary result is still in rax
                match dst.as_spill() {
                    Some(slot) => {
                        // need to store the temporary result to the spilled slot
                        self.emit(store_mem(slot, tmp));
                    }
                    None => {}
                }
            }
            Operation::Prim2(op, imm1, imm2) => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!("    operation {} = {}", dest, oper)));
                }

                let dst = self.resolve(dest);
                // move the second immediate to rax
                // THIS MUST HAPPEN BEFORE overwriting dest, because imm2 might be the same as dest
                self.emit_imm(Allocation::Reg(Reg::Rax), imm2);
                // temporary register can either be the destination or r10
                let tmp = dst.as_reg().unwrap_or(Reg::R10);
                // move the first immediate to the destination
                self.emit_imm(Allocation::Reg(tmp), imm1);
                // create a binargs with tmp and rax
                let ba = BinArgs::ToReg(tmp, Arg32::Reg(Reg::Rax));

                let mut emit_cc = |cc: ConditionCode| {
                    self.emit(Instr::Cmp(ba));
                    match dst.as_reg() {
                        Some(reg) => {
                            self.emit(Instr::Mov(MovArgs::ToReg(reg, Arg64::Signed(0))));
                            self.emit(Instr::SetCC(cc, reg.into()));
                        }
                        None => {
                            // if the destination is not a register, emit to rax before moving it to the destination
                            self.emit(Instr::Mov(MovArgs::ToReg(Reg::R10, Arg64::Signed(0))));
                            self.emit(Instr::SetCC(cc, Reg8::R10b));
                        }
                    }
                };

                match op {
                    Prim2::Add => self.emit_arith(Instr::Add(ba)),
                    Prim2::Sub => self.emit_arith(Instr::Sub(ba)),
                    Prim2::Mul => self.emit_arith(Instr::IMul(ba)),
                    Prim2::BitAnd => self.emit(Instr::And(ba)),
                    Prim2::BitOr => self.emit(Instr::Or(ba)),
                    Prim2::BitXor => self.emit(Instr::Xor(ba)),
                    Prim2::Lt => emit_cc(ConditionCode::L),
                    Prim2::Gt => emit_cc(ConditionCode::G),
                    Prim2::Le => emit_cc(ConditionCode::LE),
                    Prim2::Ge => emit_cc(ConditionCode::GE),
                    Prim2::Eq => emit_cc(ConditionCode::E),
                    Prim2::Neq => emit_cc(ConditionCode::NE),
                }

                // if the destination is not tmp, move tmp to the destination
                match dst.as_spill() {
                    Some(slot) => {
                        // need to store the temporary result to the spilled slot
                        self.emit(store_mem(slot, tmp));
                    }
                    None => {}
                }
            }
            Operation::Call { fun, args } => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!(
                        "    call {} = {}({})",
                        dest,
                        fun,
                        args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>().join(", ")
                    )));
                }
                // emit the call, with the result written to dest
                self.emit_stack_aligned_call(self.resolve(dest), fun.clone(), &args, after_live);
            }
            Operation::AllocateArray { len } => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!(
                        "    allocate array to {} of size {}",
                        dest, len
                    )));
                }
                // dest = snake_new_array(len)
                self.emit_stack_aligned_call(
                    self.resolve(dest),
                    FunName::unmangled("snake_new_array"),
                    &[len.clone()],
                    after_live,
                );
            }
            Operation::Load { addr, offset: off } => {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!(
                        "    load {} = [{} + 8 * {}]",
                        dest, addr, off
                    )));
                }
                // rax = off
                self.emit_imm(Allocation::Reg(Reg::Rax), off);
                // rax = 8 * rax
                self.emit(Instr::IMul(BinArgs::ToReg(Reg::Rax, Arg32::Signed(8))));
                // rax = rax + addr (addr is never constant and is never temporary)
                self.emit(Instr::Add(BinArgs::from_alloc(Reg::Rax, self.resolve_to_alloc(addr))));
                // mov rax, [rax]
                self.emit(Instr::Mov(MovArgs::ToReg(
                    Reg::Rax,
                    Arg64::Mem(MemRef { reg: Reg::Rax, offset: 0 }),
                )));
                // dest = rax
                self.emit_reg_to_alloc(self.resolve(dest), Reg::Rax);
            }
        }
    }

    fn emit_arith(&mut self, op: Instr) {
        self.emit(op);
        self.emit(Instr::JCC(ConditionCode::O, SnakeErr::ArithmeticOverflow.to_string()));
    }

    fn emit_stack_aligned_call(
        &mut self, dest: Allocation, fun: FunName, args: &[Immediate<VarName>],
        after_live: &LiveSet,
    ) {
        // 1. Save the live volatiles
        let caller_saves: HashSet<Reg> = after_live
            .iter()
            .filter_map(|x| match self.resolve(x) {
                imm @ Allocation::Reg(reg) if imm != dest && reg.is_volatile() => Some(reg),
                _ => None,
            })
            .collect();
        if cfg!(debug_assertions) {
            if !caller_saves.is_empty() {
                self.emit(Instr::Comment("    saving volatile registers..".to_string()));
            }
        }
        for (i, r) in caller_saves.iter().enumerate() {
            let slot = self.allocation.max_spill + (i as i32) + 1;
            if cfg!(debug_assertions) {
                self.emit(Instr::Comment(format!("        <{}> <- {}", slot, r)));
            }
            self.emit(store_mem(slot, *r));
        }
        if cfg!(debug_assertions) {
            self.emit(Instr::Comment("    ..saved".to_string()));
        }

        let num_stack_args = args.len().saturating_sub(Reg::ARGS.len()) as i32;
        let frame_size = {
            let mut f = self.allocation.max_spill + (caller_saves.len() as i32) + num_stack_args;
            f += if f % 2 == 1 { 0 } else { 1 };
            f
        };
        if frame_size % 2 == 0 {
            panic!("We were about to misalign the stack! in call {}", fun);
        }
        // 2. (simultaneously) Move the arguments into the place dictated by the calling convention
        let mut dests: Vec<Allocation> = Vec::new();
        // first args go in registers
        for (reg, _) in Reg::ARGS.iter().zip(args.iter()) {
            dests.push(Allocation::Reg(*reg));
        }
        // remaining go on the stack
        for (i, _) in args.iter().skip(Reg::ARGS.len()).enumerate() {
            dests.push(Allocation::Spill(frame_size - i as i32));
        }
        self.emit_simultaneous_move(dests, args.iter().map(|arg| self.resolve_imm(arg)).collect());

        // 3. Save the locals
        self.emit(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(8 * frame_size))));
        // 4. call
        self.emit(Instr::Call(JmpArgs::Label(fun.to_string())));
        // 5. Restore rsp
        self.emit(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Signed(8 * frame_size))));
        // 6. mov result to destination
        self.emit_resolved_imm(dest, Immediate::Var(Allocation::Reg(Reg::Rax)));
        // 7. Restore live volatiles
        if cfg!(debug_assertions) {
            if !caller_saves.is_empty() {
                self.emit(Instr::Comment("    restoring volatile registers..".to_string()));
            }
        }
        for (i, reg) in caller_saves.iter().enumerate() {
            let slot = self.allocation.max_spill + (i as i32) + 1;
            if cfg!(debug_assertions) {
                self.emit(Instr::Comment(format!("        {} <- <{}>", reg, slot)));
            }
            self.emit(load_mem(*reg, slot));
        }
        if cfg!(debug_assertions) {
            self.emit(Instr::Comment("    ..restored".to_string()));
        }
    }

    // params are destinations..
    // ..and args are sources
    fn emit_simultaneous_move(
        &mut self, params: Vec<Allocation>, args: Vec<Immediate<Allocation>>,
    ) {
        assert_eq!(params.len(), args.len());

        // if there are no parameters, we're done
        if params.is_empty() {
            return;
        }

        if cfg!(debug_assertions) {
            self.emit(Instr::Comment(format!("    simultaneously moving..")));
        }
        for (param, arg) in params.iter().zip(args.iter()) {
            if cfg!(debug_assertions) {
                self.emit(Instr::Comment(format!("        {} <- {}", param, arg)));
            }
        }

        // move the arguments:
        //   - from their current location
        //   - to the body branch parameter allocations

        // The algorithm is based on the following observation:
        //   - each argument location may point to none or multiple parameters
        //     in other words, the "source" locations are not necessarily distinct
        //     (e.g. a <- c, b <- c)
        //   - however, each parameter has only one possible argument value pointing to it
        //     in other words, the "destination" is always unique and distinct from each other
        //     (i.e. there can't be two parameters of the same location)
        //   - therefore, we hope that we can find destinations that are safe to write to
        //     (i.e. the destination doesn't have any incoming edges)
        //     (i.e. the parameter location is not someone else's source)
        //     we call these destinations "finals" and move them first
        //   - after iteratively removing all finals, we are left with only cycles
        //     (pigeon-hole principle)
        //   - finally, we solve the cycles one by one with swaps

        // 0: remove the trivial moves
        let (params, args): (Vec<Allocation>, Vec<Immediate<Allocation>>) = params
            .into_iter()
            .zip(args.into_iter())
            .filter(|(param, arg)| match arg {
                // if the param <- arg is identity, skip the move
                Immediate::Var(src) if param == src => {
                    if cfg!(debug_assertions) {
                        self.emit(Instr::Comment(format!("    identity: {}", param)));
                    }
                    false
                }
                _ => true,
            })
            .unzip();

        // 1. analyze the dependencies w/ two graphs represented by maps
        //    - (a) create a inward (destination) map of map(param <- arg)
        //    - (b) create a outward (source) map of map(arg -> { param | param <- arg }) + map(param -> {})

        use std::collections::BTreeSet;
        // (a) each parameter has only one possible argument value pointing to it
        let mut inward: HashMap<Allocation, _> =
            params.iter().copied().zip(args.iter().cloned()).collect();
        // (b) however, each argument location may point to none or multiple parameters
        let mut outward: HashMap<Allocation, _> = {
            let mut outward = HashMap::new();
            for (arg, param) in args.iter().zip(params.iter()) {
                outward.entry(*param).or_insert_with(BTreeSet::new);
                match arg {
                    Immediate::Var(src) => {
                        outward.entry(*src).or_insert_with(BTreeSet::new).insert(param);
                    }
                    _ => {}
                }
            }
            outward
        };

        // 2. iteratively find locs that are not sources, which have no out edges,
        //    i.e. no value in the out entry
        loop {
            let finals = outward
                .iter()
                .filter_map(|(loc, out)| if out.is_empty() { Some(*loc) } else { None })
                .collect::<Vec<_>>();
            // 2.1 if there are no more finals, we're done with this step and leave with only cycles
            if finals.is_empty() {
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment("    finished removing finals".to_string()));
                }
                break;
            }
            // 2.2 if there are finals, emit the moves
            for f in finals {
                // 2.2.1 remove final from inward and outward maps
                // should safely remove because the entry is guaranteed to be empty
                outward.remove(&f);
                // the inward map holds the source of the removing final
                match inward.remove(&f) {
                    // the final is not a destination because it's only a source
                    None => {}
                    // the final is a destination because it's only a source
                    Some(arg) => {
                        // 2.2.2 emit the move here
                        if cfg!(debug_assertions) {
                            self.emit(Instr::Comment(format!(
                                "    removing final {} <- {}",
                                f, arg
                            )));
                        }
                        self.emit_resolved_imm(f, arg);
                        // 2.2.3 remove source of final (which is a destination) from outward map
                        match arg {
                            Immediate::Const(_) => {}
                            Immediate::Var(loc) => {
                                outward.get_mut(&loc).map(|out| out.remove(&f));
                            }
                        }
                    }
                }
            }
        }

        // 3. after all finals are removed, we are left with only cycles
        //    - the cycles are now stored in inward
        //    - so we just swap them one after another
        if !inward.is_empty() {
            if cfg!(debug_assertions) {
                self.emit(Instr::Comment("    remaining cycles:".to_string()));
            }

            // 3.1 we gradually transform all cycles into sequences (of cycles)
            let mut cycles = inward;
            let mut seqs = Vec::new();
            while let Some((start_dst, start_src)) =
                cycles.iter().map(|(dst, src)| (*dst, src.clone())).next()
            {
                let mut seq = Vec::new();
                cycles.remove(&start_dst);
                seq.push(start_dst);
                let mut next = start_src;
                loop {
                    let Immediate::Var(src) = next else { unreachable!() };
                    seq.push(src);
                    match cycles.remove(&src) {
                        Some(arg) => next = arg,
                        None => {
                            break;
                        }
                    }
                }
                if cfg!(debug_assertions) {
                    self.emit(Instr::Comment(format!(
                        "        {}",
                        seq.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" <- ")
                    )));
                }
                seqs.push(seq);
            }

            // 3.2 emit the sequences with temporary register rax
            for seq in seqs {
                // the seq has at least two elements, otherwise it's not a cycle at all
                // a typical cycle looks like:
                //
                //     a <- b <- c <- d <- a
                //
                // where a is the [0] and [-1] of the cycle

                if seq.iter().all(|x| matches!(x, Allocation::Reg(_))) {
                    // if all the allocations are registers, we can just use xchg to swap them
                    use itertools::Itertools as _;
                    let mut iter = seq.into_iter();
                    // we basically remove and ignore the start of the cycle
                    let Some(..) = iter.next() else { unreachable!() };
                    for (a, b) in iter.tuple_windows() {
                        let Allocation::Reg(a) = a else { unreachable!() };
                        let Allocation::Reg(b) = b else { unreachable!() };
                        self.emit(Instr::Xchg(a, b));
                    }
                } else {
                    // otherwise, use r10 as a temporary swap register for efficiency
                    let mut iter = seq.into_iter();
                    // we basically remove and ignore the start of the cycle
                    let Some(..) = iter.next() else { unreachable!() };
                    // ..and begin with the second to last element
                    let Some(mut curr) = iter.next() else { unreachable!() };
                    // (must) use r10 as a temporary register;
                    // not using rax because it's used by emit_alloc_to_alloc
                    // r10 = curr
                    self.emit_alloc_to_alloc(Allocation::Reg(Reg::R10), curr.clone());
                    while let Some(next) = iter.next() {
                        // curr = next
                        self.emit_alloc_to_alloc(curr, next.clone());
                        curr = next;
                    }
                    // curr = r10
                    self.emit_reg_to_alloc(curr, Reg::R10);
                }
            }
        }
        if cfg!(debug_assertions) {
            self.emit(Instr::Comment("    ..simultaneously moving".to_string()));
        }
    }

    fn emit_reg_to_alloc(&mut self, dst: Allocation, src: Reg) {
        // only move if the source and destination are different;
        if dst != Allocation::Reg(src) {
            self.emit(Instr::Mov(MovArgs::to_alloc(dst, src)))
        }
    }

    fn emit_alloc_to_alloc(&mut self, dst: Allocation, src: Allocation) {
        match (dst, src) {
            (_, Allocation::Reg(src)) => self.emit_reg_to_alloc(dst, src),
            // move from a spilled slot to a register
            (Allocation::Reg(reg), Allocation::Spill(src)) => self.emit(load_mem(reg, src)),
            // move from a spilled slot to a spilled slot
            (Allocation::Spill(slot), Allocation::Spill(src)) => {
                // first move the spilled value to rax
                self.emit(Instr::Mov(MovArgs::ToReg(
                    Reg::Rax,
                    Arg64::Mem(MemRef { reg: Reg::Rsp, offset: -8 * src }),
                )));
                // then move rax to the destination
                self.emit(Instr::Mov(MovArgs::ToMem(
                    MemRef { reg: Reg::Rsp, offset: -8 * slot },
                    Reg32::Reg(Reg::Rax),
                )));
            }
        }
    }

    fn emit_imm(&mut self, dst: Allocation, imm: &Immediate<VarName>) {
        let imm2 = self.resolve_imm(imm);
        self.emit_resolved_imm(dst, imm2);
    }
    /// Emit an immediate value into a destination allocation.
    /// The immediate is either an allocation (in register or spilled) or a constant.
    /// The destination is either a register or a spilled slot.
    fn emit_resolved_imm(&mut self, dst: Allocation, imm: Immediate<Allocation>) {
        match imm {
            Immediate::Var(x) => self.emit_alloc_to_alloc(dst, x),
            Immediate::Const(u) => {
                match dst {
                    Allocation::Reg(reg) => self.emit(load_signed(reg, u)),
                    Allocation::Spill(dst) => {
                        // first move the constant to rax
                        self.emit(load_signed(Reg::Rax, u));
                        // then move rax to the destination
                        self.emit(store_mem(dst, Reg::Rax));
                    }
                }
            }
        }
    }
}

/// Put the value of a signed constant into a register.
fn load_signed(reg: Reg, val: i64) -> Instr {
    Instr::Mov(MovArgs::ToReg(reg, Arg64::Signed(val)))
}

/// Put the value of a memory reference into a register.
fn load_mem(reg: Reg, src: i32) -> Instr {
    Instr::Mov(MovArgs::ToReg(reg, Arg64::Mem(MemRef { reg: Reg::Rsp, offset: -8 * src })))
}

/// Flush the value of a register into a memory reference.
/// the dst is viewed as a negative offset with a stride of 8.
fn store_mem(dst: i32, reg: Reg) -> Instr {
    Instr::Mov(MovArgs::ToMem(MemRef { reg: Reg::Rsp, offset: -8 * dst }, Reg32::Reg(reg)))
}

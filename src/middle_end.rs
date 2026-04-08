//! The middle "end" of our compiler is the part that transforms our well-formed
//! source-language abstract syntax tree (AST) into the intermediate representation
//! As well as performs some SSA to SSA optimizations

use crate::ast::{self, *};
use crate::ssa::{self, *};
use crate::{ana::Nil, frontend::Resolver, identifiers::*};
use std::collections::{HashMap, HashSet};

pub struct Lowerer {
    pub vars: IdGen<VarName>,
    pub funs: IdGen<FunName>,
    pub blocks: IdGen<BlockName>,
    /// The live variables at the start of each function.
    fun_scopes: HashMap<FunName, Vec<VarName>>,
    /// The functions that should be lambda lifted.
    should_lift: HashSet<FunName>,
    /// The name of the basic block generated for each function.
    fun_as_block: HashMap<FunName, BlockName>,
    /// Lifted functions. Removed after the lowering pass.
    lifted_funs: Vec<(FunBlock<VarName>, BasicBlock<VarName, Nil>)>,
}

/// A helper struct for variable renaming.
#[derive(Clone)]
struct Substitution {
    /// The map of old variables to new variables.
    rename_map: HashMap<VarName, VarName>,
}
impl Substitution {
    fn new() -> Self {
        Substitution { rename_map: HashMap::new() }
    }
    fn insert(&mut self, old: VarName, new: VarName) {
        self.rename_map.insert(old, new);
    }
    fn run(&self, mut var: VarName) -> VarName {
        while let Some(new) = self.rename_map.get(&var) {
            var = new.to_owned();
        }
        var
    }
}

/// Indicates whether the expression being compiled is in a tail position.
#[derive(Clone)]
enum Continuation {
    Return,
    Block(VarName, BlockBody<VarName, Nil>),
}

impl Continuation {
    fn invoke(self, imm: Immediate<VarName>) -> BlockBody<VarName, Nil> {
        match self {
            Continuation::Return => BlockBody::Terminator(Terminator::Return(imm), Nil),
            Continuation::Block(dest, b) => BlockBody::Operation {
                dest,
                op: Operation::Immediate(imm),
                next: Box::new(b),
                ana: Nil,
            },
        }
    }
}

impl From<Resolver> for Lowerer {
    fn from(resolver: Resolver) -> Self {
        let Resolver { vars, funs, .. } = resolver;
        Lowerer {
            vars,
            funs,
            blocks: IdGen::new(),
            fun_scopes: HashMap::new(),
            should_lift: HashSet::new(),
            fun_as_block: HashMap::new(),
            lifted_funs: Vec::new(),
        }
    }
}

/// Traverse the AST and collect the live variables at the start of each function.
/// Also collect the functions that are non-tail called and the functions that are called
/// by a lifted function, either tail or non-tail.
struct Lifter {
    /// Functions that are non-tail called.
    non_tail_called_funs: HashSet<FunName>,
    /// The call graph of the program.
    /// Records all functions that are called, either tail or non-tail.
    /// Used to lift all functions called by a lifted function.
    fun_calls: HashMap<FunName, HashSet<FunName>>,
}

impl Lifter {
    /// What should be lambda lifted?
    /// 1. Any function that is called with a non-tail call.
    /// 2. Any function that is called by a lifted function.
    pub fn should_lift(&self) -> HashSet<FunName> {
        let mut should_lift = HashSet::new();
        // find all functions that should be lifted
        let mut worklist = self.non_tail_called_funs.iter().cloned().collect::<Vec<_>>();
        while let Some(fun) = worklist.pop() {
            // 1. include the function in worklist to the result set
            if should_lift.insert(fun.clone()) {
                // 2. if it's the first time met, add all functions that it calls to the worklist
                worklist.extend(self.fun_calls.get(&fun).cloned().unwrap_or_default());
            }
        }
        should_lift
    }
}

impl Lifter {
    fn new() -> Self {
        Self { non_tail_called_funs: HashSet::new(), fun_calls: HashMap::new() }
    }

    fn lift_prog(&mut self, prog: &BoundProg) {
        let Prog { externs: _, name, param: _, body, loc: _ } = prog;
        self.lift_expr(body, &name, true);
    }

    fn lift_expr(&mut self, e: &BoundExpr, site: &FunName, tail_position: bool) {
        match e {
            Expr::Num(_, _) | Expr::Bool(_, _) | Expr::Var(_, _) => {}
            Expr::Prim { prim: _, args, loc: _ } => {
                for arg in args {
                    self.lift_expr(arg, site, false);
                }
            }
            Expr::Let { bindings, body, loc: _ } => {
                for Binding { var: _, expr } in bindings {
                    self.lift_expr(expr, site, false);
                }
                self.lift_expr(body, site, tail_position);
            }
            Expr::If { cond, thn, els, loc: _ } => {
                self.lift_expr(cond, site, false);
                self.lift_expr(thn, site, tail_position);
                self.lift_expr(els, site, tail_position);
            }
            Expr::FunDefs { decls, body, loc: _ } => {
                for FunDecl { name, body, .. } in decls {
                    self.lift_expr(body, name, true);
                }
                self.lift_expr(body, site, tail_position);
            }
            Expr::Call { fun, args, loc: _ } => {
                if !tail_position {
                    self.non_tail_called_funs.insert(fun.clone());
                }
                self.fun_calls.entry(site.clone()).or_default().insert(fun.clone());
                for arg in args {
                    self.lift_expr(arg, site, false);
                }
            }
        }
    }
}

impl Immediate<VarName> {
    pub fn raw(val: usize) -> Self {
        Self::Const(val as i64)
    }
    pub fn integer(val: i64) -> Self {
        // should not overflow after frontend checks
        Self::Const(val << 1)
    }
    pub fn boolean(val: bool) -> Self {
        if val { Self::Const(0b101) } else { Self::Const(0b001) }
    }
}

impl Lowerer {
    pub fn lower_prog(&mut self, prog: BoundProg) -> Program<VarName, Nil> {
        // first, collect all functions that should be lifted
        let mut lifter = Lifter::new();
        lifter.lift_prog(&prog);
        self.should_lift = lifter.should_lift();

        // then, lower the program
        let Prog { externs, name, param, body, loc: _ } = prog;
        // register function scope for the main function
        self.fun_scopes.insert(name.clone(), Vec::new());
        // create a block name for the main function
        let block = self.blocks.fresh(name.hint());
        self.fun_as_block.insert(name.clone(), block.clone());
        // lower the externs
        let externs = Vec::from_iter(
            (externs.into_iter())
                .map(|ExtDecl { name, params, loc: _ }| Extern {
                    name,
                    params: params.into_iter().map(|(p, _)| p).collect(),
                })
                .chain([
                    // add the built-in functions
                    Extern {
                        name: FunName::unmangled("snake_error"),
                        params: vec![self.vars.fresh("ecode"), self.vars.fresh("v")],
                    },
                    Extern {
                        name: FunName::unmangled("snake_new_array"),
                        params: vec![self.vars.fresh("len")],
                    },
                ]),
        );
        // lower the parameter
        let (param, _) = param;
        // lower the body
        let body = self.lower_expr_kont(
            body,
            &vec![param.clone()],
            &Substitution::new(),
            Continuation::Return,
        );
        // collect the lifted functions and blocks
        let (mut funs, mut blocks): (Vec<FunBlock<VarName>>, Vec<BasicBlock<VarName, Nil>>) =
            std::mem::take(&mut self.lifted_funs).into_iter().unzip();
        // create the entry block and function
        blocks.push(BasicBlock {
            label: block.clone(),
            params: vec![param.clone()],
            body,
            ana: Nil,
        });
        let fun_param = self.vars.fresh(param.hint());
        funs.push(FunBlock {
            name,
            params: vec![fun_param.clone()],
            body: Branch { target: block, args: vec![Immediate::Var(fun_param)] },
        });

        Program { externs, funs, blocks }
    }

    fn kont_to_block(&mut self, k: Continuation) -> (VarName, BlockBody<VarName, Nil>) {
        match k {
            Continuation::Block(x, b) => (x, b),
            Continuation::Return => {
                let x = self.vars.fresh("result");
                (x.clone(), BlockBody::Terminator(Terminator::Return(Immediate::Var(x)), Nil))
            }
        }
    }

    /// Compiles an expression to a basic block that uses the continuation k on
    /// the value e produces.
    fn lower_expr_kont(
        &mut self, e: BoundExpr, live: &[VarName], subst: &Substitution, k: Continuation,
    ) -> BlockBody<VarName, Nil> {
        match e {
            Expr::Num(n, _) => k.invoke(Immediate::integer(n)),
            Expr::Bool(b, _) => k.invoke(Immediate::boolean(b)),
            Expr::Var(v, _) => k.invoke(Immediate::Var(subst.run(v))),
            Expr::Prim { prim, args, loc: _ } => {
                // prepare the arguments
                let (args_var, args_imm): (Vec<_>, Vec<_>) = args
                    .iter()
                    .enumerate()
                    .map(|(i, _arg)| {
                        // the arguments are named after the primitive name and the argument index
                        let var = self.vars.fresh(format!("{:?}_{}", prim, i));
                        (var.clone(), Immediate::Var(var))
                    })
                    .unzip();
                let (dest, next) = self.kont_to_block(k);
                let prim1_integer_one = |prim: ssa::Prim2, next| {
                    Self::assert_type(Type::Int, &args_imm[0], {
                        let dest = dest.clone();
                        let imm = Immediate::integer(1);
                        let op = Operation::Prim2(prim, args_imm[0].to_owned(), imm);
                        BlockBody::Operation { dest, op, next: Box::new(next), ana: Nil }
                    })
                };
                let prim2 = |prim: ssa::Prim2, next| {
                    let dest = dest.clone();
                    let op = Operation::Prim2(prim, args_imm[0].to_owned(), args_imm[1].to_owned());
                    BlockBody::Operation { dest, op, next: Box::new(next), ana: Nil }
                };
                let prim2_kont = |prim: ssa::Prim2, imms: &[Immediate<VarName>], (dest, next)| {
                    let op = Operation::Prim2(prim, imms[0].to_owned(), imms[1].to_owned());
                    BlockBody::Operation { dest, op, next: Box::new(next), ana: Nil }
                };
                let prim2_compare = |lowerer: &mut Lowerer, prim: ssa::Prim2, next| {
                    let tagged = lowerer.vars.fresh("tagged");
                    Self::assert_type_multi(
                        Type::Int,
                        &args_imm,
                        prim2_kont(
                            prim,
                            &args_imm,
                            (
                                tagged.clone(),
                                lowerer.tagging(
                                    &Immediate::Var(tagged),
                                    Type::Bool,
                                    Continuation::Block(dest.clone(), next),
                                ),
                            ),
                        ),
                    )
                };
                let prim2_equality = |lowerer: &mut Lowerer, prim: ssa::Prim2, next| {
                    let tagged = lowerer.vars.fresh("tagged");
                    prim2_kont(
                        prim,
                        &args_imm,
                        (
                            tagged.clone(),
                            lowerer.tagging(
                                &Immediate::Var(tagged),
                                Type::Bool,
                                Continuation::Block(dest.clone(), next),
                            ),
                        ),
                    )
                };
                let block = match prim {
                    ast::Prim::Add1 => prim1_integer_one(ssa::Prim2::Add, next),
                    ast::Prim::Sub1 => prim1_integer_one(ssa::Prim2::Sub, next),
                    ast::Prim::Not => Self::assert_type(
                        Type::Bool,
                        &args_imm[0],
                        // dest = imm ^ 100
                        // 0 ^ anything is itself, so the last two are 0 to maintain the tag
                        // 1 ^ anything negates itself
                        BlockBody::Operation {
                            dest,
                            op: Operation::Prim2(
                                Prim2::BitXor,
                                args_imm[0].to_owned(),
                                Immediate::Const(0b100),
                            ),
                            next: Box::new(next),
                            ana: Nil,
                        },
                    ),
                    ast::Prim::Add => {
                        Self::assert_type_multi(Type::Int, &args_imm, prim2(ssa::Prim2::Add, next))
                    }
                    ast::Prim::Sub => {
                        Self::assert_type_multi(Type::Int, &args_imm, prim2(ssa::Prim2::Sub, next))
                    }
                    ast::Prim::Mul => Self::assert_type_multi(Type::Int, &args_imm, {
                        let half = self.vars.fresh("half");
                        BlockBody::Operation {
                            // half = imm0 >> 1
                            dest: half.clone(),
                            op: Operation::Prim1(ssa::Prim1::BitSar(1), args_imm[0].to_owned()),
                            next: Box::new(prim2_kont(
                                ssa::Prim2::Mul,
                                &[Immediate::Var(half), args_imm[1].to_owned()],
                                (dest, next),
                            )),
                            ana: Nil,
                        }
                    }),
                    ast::Prim::And => Self::assert_type_multi(
                        Type::Bool,
                        &args_imm,
                        prim2(ssa::Prim2::BitAnd, next),
                    ),
                    ast::Prim::Or => Self::assert_type_multi(
                        Type::Bool,
                        &args_imm,
                        prim2(ssa::Prim2::BitOr, next),
                    ),
                    ast::Prim::Lt => prim2_compare(self, ssa::Prim2::Lt, next),
                    ast::Prim::Le => prim2_compare(self, ssa::Prim2::Le, next),
                    ast::Prim::Gt => prim2_compare(self, ssa::Prim2::Gt, next),
                    ast::Prim::Ge => prim2_compare(self, ssa::Prim2::Ge, next),
                    ast::Prim::Eq => prim2_equality(self, ssa::Prim2::Eq, next),
                    ast::Prim::Neq => prim2_equality(self, ssa::Prim2::Neq, next),

                    ast::Prim::IsType(ty) => {
                        let dest = dest.clone();
                        // maybe we can avoid using `test`
                        let tag = self.vars.fresh("tag");
                        let is_tag = self.vars.fresh("is_tag");
                        BlockBody::Operation {
                            dest: tag.clone(),
                            // tag = imm & mask
                            op: Operation::Prim2(
                                ssa::Prim2::BitAnd,
                                args_imm[0].to_owned(),
                                Immediate::raw(ty.mask() as usize),
                            ),
                            next: Box::new(BlockBody::Operation {
                                dest: is_tag.clone(),
                                // is_tag = tag == <tag>
                                op: Operation::Prim2(
                                    ssa::Prim2::Eq,
                                    Immediate::Var(tag),
                                    Immediate::raw(ty.tag() as usize),
                                ),
                                next: Box::new(self.tagging(
                                    &Immediate::Var(is_tag),
                                    Type::Bool,
                                    Continuation::Block(dest, next),
                                )),
                                ana: Nil,
                            }),
                            ana: Nil,
                        }
                    }
                    ast::Prim::NewArray => {
                        let len = self.vars.fresh("len");
                        let arr = self.vars.fresh("arr");
                        let tagged_arr = self.tagging(
                            &Immediate::Var(arr.clone()),
                            Type::Array,
                            Continuation::Block(dest, next),
                        );
                        Self::assert_type(
                            Type::Int,
                            // assertInt(num)
                            &args_imm[0],
                            self.untagging(
                                Type::Int,
                                &args_imm[0],
                                Continuation::Block(
                                    len.clone(),
                                    BlockBody::AssertLength {
                                        // assertLength(len)
                                        len: Immediate::Var(len.clone()),
                                        next: Box::new(BlockBody::Operation {
                                            dest: arr,
                                            // arr = allocateArray(len)
                                            op: Operation::AllocateArray {
                                                len: Immediate::Var(len.to_owned()),
                                            },
                                            next: Box::new(tagged_arr),
                                            ana: Nil,
                                        }),
                                        ana: Nil,
                                    },
                                ),
                            ),
                        )
                    }
                    ast::Prim::MakeArray => {
                        let arr = self.vars.fresh("arr");
                        let len = Immediate::raw(args.len());
                        let stores = |next| {
                            (0..args.len()).rev().fold(next, |next, i| {
                                let imm = args_imm[i].to_owned();
                                BlockBody::Store {
                                    // store(arr, i + 1, imm)
                                    addr: Immediate::Var(arr.clone()),
                                    offset: Immediate::raw(i + 1),
                                    val: imm,
                                    next: Box::new(next),
                                    ana: Nil,
                                }
                            })
                        };
                        BlockBody::Operation {
                            // allocateArray(len)
                            dest: arr.clone(),
                            op: Operation::AllocateArray { len: len.to_owned() },
                            next: Box::new(stores(self.tagging(
                                &Immediate::Var(arr.clone()),
                                Type::Array,
                                Continuation::Block(dest, next),
                            ))),
                            ana: Nil,
                        }
                    }
                    ast::Prim::ArrayGet => {
                        let arr = self.vars.fresh("arr");
                        let len = self.vars.fresh("len");
                        let idx = self.vars.fresh("idx");
                        let off = self.vars.fresh("off");
                        let load_by_idx = self.untagging(
                            Type::Int,
                            &args_imm[1],
                            Continuation::Block(
                                idx.clone(),
                                BlockBody::AssertInBounds {
                                    bound: Immediate::Var(len.clone()),
                                    // assertInBounds(len, idx)
                                    arg: Immediate::Var(idx.clone()),
                                    next: Box::new(BlockBody::Operation {
                                        dest: off.clone(),
                                        // off = idx + 1
                                        op: Operation::Prim2(
                                            ssa::Prim2::Add,
                                            Immediate::Var(idx.clone()),
                                            Immediate::raw(1),
                                        ),
                                        next: Box::new(BlockBody::Operation {
                                            dest,
                                            // res = load(arr, off)
                                            op: Operation::Load {
                                                addr: Immediate::Var(arr.clone()),
                                                offset: Immediate::Var(off),
                                            },
                                            next: Box::new(next),
                                            ana: Nil,
                                        }),
                                        ana: Nil,
                                    }),
                                    ana: Nil,
                                },
                            ),
                        );

                        Self::assert_types(
                            // assertArray(imm0)
                            // assertInt(imm1)
                            [Type::Array, Type::Int],
                            &args_imm,
                            self.untagging(
                                Type::Array,
                                &args_imm[0],
                                Continuation::Block(
                                    arr.clone(),
                                    BlockBody::Operation {
                                        // len = load(arr, 0)
                                        dest: len.clone(),
                                        op: Operation::Load {
                                            addr: Immediate::Var(arr.clone()),
                                            offset: Immediate::raw(0),
                                        },
                                        next: Box::new(load_by_idx),
                                        ana: Nil,
                                    },
                                ),
                            ),
                        )
                    }
                    ast::Prim::ArraySet => {
                        let arr = self.vars.fresh("arr");
                        let len = self.vars.fresh("len");
                        let idx = self.vars.fresh("idx");
                        let off = self.vars.fresh("off");
                        let store_by_idx = self.untagging(
                            Type::Int,
                            &args_imm[1],
                            Continuation::Block(
                                idx.clone(),
                                BlockBody::AssertInBounds {
                                    // assertInBounds(len, idx)
                                    bound: Immediate::Var(len.clone()),
                                    arg: Immediate::Var(idx.clone()),
                                    next: Box::new(BlockBody::Operation {
                                        // off = idx + 1
                                        dest: off.clone(),
                                        op: Operation::Prim2(
                                            ssa::Prim2::Add,
                                            Immediate::Var(idx.clone()),
                                            Immediate::raw(1),
                                        ),
                                        next: Box::new(BlockBody::Store {
                                            // store(arr, off, imm2)
                                            addr: Immediate::Var(arr.clone()),
                                            offset: Immediate::Var(off),
                                            val: args_imm[2].to_owned(),
                                            next: Box::new(BlockBody::Operation {
                                                // dest = imm2
                                                dest,
                                                op: Operation::Immediate(args_imm[2].to_owned()),
                                                next: Box::new(next),
                                                ana: Nil,
                                            }),
                                            ana: Nil,
                                        }),
                                        ana: Nil,
                                    }),
                                    ana: Nil,
                                },
                            ),
                        );

                        Self::assert_types(
                            [Type::Array, Type::Int],
                            &args_imm,
                            self.untagging(
                                Type::Array,
                                &args_imm[0],
                                Continuation::Block(
                                    arr.clone(),
                                    BlockBody::Operation {
                                        dest: len.clone(),
                                        // len = load(arr, 0)
                                        op: Operation::Load {
                                            addr: Immediate::Var(arr.clone()),
                                            offset: Immediate::raw(0),
                                        },
                                        next: Box::new(store_by_idx),
                                        ana: Nil,
                                    },
                                ),
                            ),
                        )
                    }
                    ast::Prim::Length => {
                        let arr = self.vars.fresh("arr");
                        let len = self.vars.fresh("len");
                        let load_len_int = BlockBody::Operation {
                            dest: len.clone(),
                            op: Operation::Load {
                                addr: Immediate::Var(arr.clone()),
                                offset: Immediate::raw(0),
                            },
                            next: Box::new(self.tagging(
                                &Immediate::Var(len),
                                Type::Int,
                                Continuation::Block(dest, next),
                            )),
                            ana: Nil,
                        };
                        Self::assert_type(
                            Type::Array,
                            &args_imm[0],
                            self.untagging(
                                Type::Array,
                                &args_imm[0],
                                Continuation::Block(arr, load_len_int),
                            ),
                        )
                    }
                };

                // backwards, so we need to reverse the arguments
                args.into_iter().zip(args_var).rev().fold(block, |block, (arg, var)| {
                    self.lower_expr_kont(arg, live, subst, Continuation::Block(var, block))
                })
            }
            Expr::Let { bindings, body, loc: _ } => {
                // collect the live variables up to this point
                let mut live = live
                    .to_owned()
                    .into_iter()
                    .chain(bindings.iter().map(|Binding { var: (var, _), .. }| var.clone()))
                    .collect::<Vec<_>>();

                // backwards, here we go
                let block = self.lower_expr_kont(*body, &live, subst, k);

                // reversed, as usual
                bindings.into_iter().rev().fold(block, |block, Binding { var: (var, _), expr }| {
                    live.pop();
                    let expr = self.lower_expr_kont(
                        expr,
                        &live,
                        subst,
                        Continuation::Block(var.clone(), block),
                    );
                    expr
                })
            }
            Expr::If { cond, thn, els, loc: _ } => {
                let cond_var = self.vars.fresh("cond");
                let flag_var = self.vars.fresh("flag");
                let thn_name = self.blocks.fresh("thn");
                let els_name = self.blocks.fresh("els");
                let untagged_cbr = self.untagging(
                    Type::Bool,
                    &Immediate::Var(cond_var.clone()),
                    Continuation::Block(
                        flag_var.clone(),
                        BlockBody::Terminator(
                            Terminator::ConditionalBranch {
                                cond: Immediate::Var(flag_var.clone()),
                                thn: thn_name.clone(),
                                els: els_name.clone(),
                            },
                            Nil,
                        ),
                    ),
                );
                let cond_branch = Box::new(self.lower_expr_kont(
                    *cond,
                    &live,
                    subst,
                    Continuation::Block(
                        cond_var.clone(),
                        Self::assert_type(
                            Type::Bool,
                            &Immediate::Var(cond_var.clone()),
                            untagged_cbr,
                        ),
                    ),
                ));

                // Here is the exponential implementation
                // let mut branch = |label, body: BoundExpr| BasicBlock {
                //     label,
                //     params: Vec::new(),
                //     body: self.lower_expr_kont(body, live, subst, k.clone()),
                // };
                // BlockBody::SubBlocks {
                //     blocks: vec![branch(thn_label, *thn), branch(els_label, *els)],
                //     next: cond_branch,
                // }

                // Here is the correct implementation, also optimizing to not create a joing point if in tail position

                match k {
                    Continuation::Return => {
                        let mut branch = |label, body: BoundExpr| BasicBlock {
                            label,
                            params: Vec::new(),
                            body: self.lower_expr_kont(body, live, subst, Continuation::Return),
                            ana: Nil,
                        };

                        BlockBody::SubBlocks {
                            blocks: vec![branch(thn_name, *thn), branch(els_name, *els)],
                            next: cond_branch,
                            ana: Nil,
                        }
                    }
                    // if we have a non-trivial continuation, we create a join point
                    Continuation::Block(dest, body) => {
                        // fresh variables for return positions in kontinuations
                        let thn_var = self.vars.fresh("thn_res");
                        let els_var = self.vars.fresh("els_res");
                        let join_name = self.blocks.fresh("jn");

                        let mut branch = |label, expr: BoundExpr, var: VarName| BasicBlock {
                            label,
                            params: Vec::new(),
                            body: self.lower_expr_kont(
                                expr,
                                live,
                                subst,
                                Continuation::Block(
                                    var.clone(),
                                    BlockBody::Terminator(
                                        Terminator::Branch(Branch {
                                            target: join_name.clone(),
                                            args: vec![Immediate::Var(var)],
                                        }),
                                        Nil,
                                    ),
                                ),
                            ),
                            ana: Nil,
                        };

                        BlockBody::SubBlocks {
                            blocks: vec![
                                branch(thn_name, *thn, thn_var),
                                branch(els_name, *els, els_var),
                                BasicBlock { label: join_name, params: vec![dest], body, ana: Nil },
                            ],
                            next: cond_branch,
                            ana: Nil,
                        }
                    }
                }
            }
            Expr::FunDefs { decls, body, loc: _ } => {
                // create a block name for each function
                for FunDecl { name: fun, .. } in decls.iter() {
                    let block = self.blocks.fresh(fun.hint());
                    self.fun_as_block.insert(fun.clone(), block);
                    // collect the live variables up to this point
                    self.fun_scopes.insert(fun.clone(), live.to_owned());
                }
                // lower the body
                let next = Box::new(self.lower_expr_kont(*body, live, subst, k));
                // compile the functions
                let blocks: Vec<_> = decls
                    .into_iter()
                    .filter_map(|FunDecl { name: fun, params, body, loc: _ }| {
                        let live = live
                            .to_owned()
                            .into_iter()
                            .chain(params.iter().map(|(p, _)| p.clone()))
                            .collect::<Vec<_>>();
                        let block = self.fun_as_block.get(&fun).cloned().expect("fun not found");
                        if self.should_lift.contains(&fun) {
                            // Here we need to produce a fundecl in lifted_funs,
                            // but we need to add extra arguments.
                            let mut subst = subst.clone();
                            // get ambient live variables rename the ambient variables
                            // to be unique; the ambient variables are prefixed with "@"
                            let ambient = self
                                .fun_scopes
                                .get(&fun)
                                .cloned()
                                .expect("fun not found")
                                .into_iter()
                                .map(|v| {
                                    // with a hint from the previous name
                                    let new = self.vars.fresh(format!("@{}", v.hint()));
                                    subst.insert(v, new.clone());
                                    new
                                });
                            // get function parameters prepared
                            let fun_params = params.into_iter().map(|(p, _)| p);
                            // parameters are ambient live variables and the function parameters combined
                            let params = ambient.chain(fun_params).collect::<Vec<_>>();
                            let body =
                                self.lower_expr_kont(body, &live, &subst, Continuation::Return);
                            let funblock_params = params
                                .iter()
                                .map(|p| self.vars.fresh(p.hint()))
                                .collect::<Vec<_>>();
                            let funblock = FunBlock {
                                name: fun.clone(),
                                params: funblock_params.clone(),
                                body: Branch {
                                    target: block.clone(),
                                    args: funblock_params
                                        .clone()
                                        .into_iter()
                                        .map(|p| Immediate::Var(p))
                                        .collect(),
                                },
                            };
                            let block = BasicBlock { label: block, params, body, ana: Nil };
                            self.lifted_funs.push((funblock, block));
                            None
                        } else {
                            // tail recursive functions are built as sub-blocks
                            Some(BasicBlock {
                                label: block.clone(),
                                params: params.into_iter().map(|(p, _)| p).collect(),
                                body: self.lower_expr_kont(
                                    body,
                                    &live,
                                    subst,
                                    Continuation::Return,
                                ),
                                ana: Nil,
                            })
                        }
                    })
                    .collect();
                if blocks.is_empty() {
                    *next
                } else {
                    BlockBody::SubBlocks { blocks, next, ana: Nil }
                }
            }
            Expr::Call { fun, args, loc: _ } => {
                // prepare the arguments
                let (args_var, args_imm): (Vec<_>, _) = args
                    .iter()
                    .enumerate()
                    .map(|(i, _arg)| {
                        // the arguments are named after the function name and the argument index
                        let var = self.vars.fresh(format!("{}_{}", fun.hint(), i));
                        (var.clone(), Immediate::Var(var))
                    })
                    .unzip();
                let lower_call = |lowerer: &mut Lowerer, block: BlockBody<VarName, Nil>| {
                    // backwards, so we need to reverse the arguments
                    args.into_iter().zip(args_var).rev().fold(block, |block, (arg, var)| {
                        lowerer.lower_expr_kont(arg, &live, subst, Continuation::Block(var, block))
                    })
                };
                if fun.is_unmangled() {
                    // extern function. Always produce a call here
                    let (dest, next) = self.kont_to_block(k);
                    lower_call(
                        self,
                        BlockBody::Operation {
                            dest,
                            op: Operation::Call { fun, args: args_imm },
                            next: Box::new(next),
                            ana: Nil,
                        },
                    )
                } else {
                    let block = self.fun_as_block.get(&fun).cloned().expect("fun not found");
                    if self.should_lift.contains(&fun) {
                        let ambient = self
                            .fun_scopes
                            .get(&fun)
                            .cloned()
                            .expect("fun not found")
                            .into_iter()
                            .map(|v| subst.run(v));
                        // the arguments are the ambient live variables and the arguments combined
                        let args_imm =
                            ambient.map(|v| Immediate::Var(v)).chain(args_imm).collect::<Vec<_>>();

                        match k {
                            Continuation::Return => lower_call(
                                self,
                                BlockBody::Terminator(
                                    Terminator::Branch(Branch { target: block, args: args_imm }),
                                    Nil,
                                ),
                            ),
                            Continuation::Block(dest, next) => lower_call(
                                self,
                                BlockBody::Operation {
                                    dest,
                                    op: Operation::Call { fun, args: args_imm },
                                    next: Box::new(next),
                                    ana: Nil,
                                },
                            ),
                        }
                    } else {
                        // tail calls are compiled to a branch
                        assert!(matches!(k, Continuation::Return));
                        lower_call(
                            self,
                            BlockBody::Terminator(
                                Terminator::Branch(Branch { target: block, args: args_imm }),
                                Nil,
                            ),
                        )
                    }
                }
            }
        }
    }

    // shorthands for asserting types
    fn assert_type(
        ty: Type, of: &Immediate<VarName>, next: BlockBody<VarName, Nil>,
    ) -> BlockBody<VarName, Nil> {
        BlockBody::AssertType { ty, arg: of.to_owned(), next: Box::new(next), ana: Nil }
    }
    fn assert_type_multi(
        ty: Type, of: &[Immediate<VarName>], next: BlockBody<VarName, Nil>,
    ) -> BlockBody<VarName, Nil> {
        of.into_iter().fold(next, |block, imm| BlockBody::AssertType {
            ty,
            arg: imm.to_owned(),
            next: Box::new(block),
            ana: Nil,
        })
    }
    fn assert_types<'a>(
        ty: impl IntoIterator<Item = Type>, of: impl IntoIterator<Item = &'a Immediate<VarName>>,
        next: BlockBody<VarName, Nil>,
    ) -> BlockBody<VarName, Nil> {
        ty.into_iter().zip(of).fold(next, |block, (ty, imm)| BlockBody::AssertType {
            ty,
            arg: imm.to_owned(),
            next: Box::new(block),
            ana: Nil,
        })
    }

    /// tagging and untagging
    fn tagging(
        &mut self, imm: &Immediate<VarName>, ty: Type, k: Continuation,
    ) -> BlockBody<VarName, Nil> {
        let (dest, next) = self.kont_to_block(k);
        match ty {
            Type::Int | Type::Bool => {
                let shifted = self.vars.fresh("shifted");
                // shifted = imm << <mask_length>
                // dest = shifted | <tag>
                BlockBody::Operation {
                    dest: shifted.clone(),
                    op: Operation::Prim1(Prim1::BitSal(ty.mask_length()), imm.to_owned()),
                    next: Box::new(BlockBody::Operation {
                        dest,
                        op: Operation::Prim2(
                            Prim2::BitOr,
                            Immediate::Var(shifted),
                            Immediate::raw(ty.tag() as usize),
                        ),
                        next: Box::new(next),
                        ana: Nil,
                    }),
                    ana: Nil,
                }
            }
            Type::Array => {
                // dest = imm | <tag>
                BlockBody::Operation {
                    dest,
                    op: Operation::Prim2(
                        Prim2::BitOr,
                        imm.to_owned(),
                        Immediate::raw(ty.tag() as usize),
                    ),
                    next: Box::new(next),
                    ana: Nil,
                }
            }
        }
    }
    fn untagging(
        &mut self, ty: Type, imm: &Immediate<VarName>, k: Continuation,
    ) -> BlockBody<VarName, Nil> {
        let (dest, next) = self.kont_to_block(k);
        match ty {
            Type::Int | Type::Bool => {
                // dest = imm >> <mask_length>
                BlockBody::Operation {
                    dest,
                    op: Operation::Prim1(Prim1::BitSar(ty.mask_length()), imm.to_owned()),
                    next: Box::new(next),
                    ana: Nil,
                }
            }
            Type::Array => {
                // dest = imm ^ <tag>
                BlockBody::Operation {
                    dest,
                    op: Operation::Prim2(
                        Prim2::BitXor,
                        imm.to_owned(),
                        Immediate::raw(ty.tag() as usize),
                    ),
                    next: Box::new(next),
                    ana: Nil,
                }
            }
        }
    }
}

/// A simple abstraction of sets of 64-bit integers for Assertion Removal.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum PossibleValues {
    /// The set of integers whose last two bits are constrained by [`PossibleBitValues`].
    ///
    /// The first element is the second-to-last bit, and the second element is the last bit.
    Assigned([PossibleBitValues; 2]),
    /// The empty set, i.e., the value has never been assigned
    None,
}

impl PossibleValues {
    /// The least [`PossibleValues`]
    fn bottom() -> Self {
        PossibleValues::None
    }

    /// The least upper bound of two possible values
    fn lub(self, other: Self) -> Self {
        match (self, other) {
            // least upper bound of each "component" so to speak
            (PossibleValues::Assigned(a), PossibleValues::Assigned(b)) => {
                PossibleValues::Assigned([a[0].lub(b[0]), a[1].lub(b[1])])
            },
            (PossibleValues::Assigned(a), PossibleValues::None) => PossibleValues::Assigned(a),
            (PossibleValues::None, PossibleValues::Assigned(b)) => PossibleValues::Assigned(b),
            (PossibleValues::None, PossibleValues::None) => PossibleValues::None
        }
    }


    /// mutably update self to be its least upper bound with other
    fn lub_mut(&mut self, other: Self) {
        *self = self.lub(other);
    }

    /// The greatest [`PossibleValues`]
    fn top() -> Self {
        PossibleValues::Assigned([PossibleBitValues::Any, PossibleBitValues::Any])
    }

    /// The possible values of an integer that is assigned
    fn integer() -> Self {
        PossibleValues::Assigned([PossibleBitValues::Any, PossibleBitValues::Zero])
    }

    /// The possible values of a boolean that is assigned
    fn boolean() -> Self {
        PossibleValues::Assigned([PossibleBitValues::Zero, PossibleBitValues::One])
    }

    /// The possible values of an array that is assigned
    fn array() -> Self {
        PossibleValues::Assigned([PossibleBitValues::One, PossibleBitValues::One])
    }
}

/// Possible values of a bit that is assigned.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum PossibleBitValues {
    /// The set of all possible bit values, i.e., the bit could be either 0 or 1
    Any,
    /// {0}
    Zero,
    /// {1}
    One,
}

impl PossibleBitValues {
    /// The least upper bound of two possible bit values
    fn lub(self, other: Self) -> Self {
        match (self, other) {
            (PossibleBitValues::Any, PossibleBitValues::Any) => PossibleBitValues::Any,
            (PossibleBitValues::Any, PossibleBitValues::Zero) => PossibleBitValues::Any,
            (PossibleBitValues::Any, PossibleBitValues::One) => PossibleBitValues::Any,
            (PossibleBitValues::Zero, PossibleBitValues::Any) => PossibleBitValues::Any,
            (PossibleBitValues::Zero, PossibleBitValues::One) => PossibleBitValues::Any,
            (PossibleBitValues::One, PossibleBitValues::Any) => PossibleBitValues::Any,
            (PossibleBitValues::One, PossibleBitValues::Zero) => PossibleBitValues::Any,
            (PossibleBitValues::One, PossibleBitValues::One) => PossibleBitValues::One,
            (PossibleBitValues::Zero, PossibleBitValues::Zero) => PossibleBitValues::Zero,
        }
    }
}

/// The [`PossibleValuesEnv`] is stored at every node.
/// The [`HashMap`] not containing a name is considered equivalent to that name being mapped to Bottom.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PossibleValuesEnv(HashMap<VarName, PossibleValues>);

impl PossibleValuesEnv {
    fn bottom() -> Self {
        PossibleValuesEnv(HashMap::new())
    }

    /// mutably update self to be its least upper bound with other
    fn lub_mut(&mut self, other: Self) {
        for (key, val) in other.0 {
            self.0.entry(key)
                .and_modify(|existing| existing.lub_mut(val))
                .or_insert(val);
        }
    }

    /// Produces the possible values an immediate may have based on the
    /// current environment information
    fn possible_values(&self, imm: &Immediate<VarName>) -> PossibleValues {
        match imm {
            Immediate::Const(c) => {
                let last = if c & 1 == 0 { PossibleBitValues::Zero } else { PossibleBitValues::One };
                let second = if c & 2 == 0 { PossibleBitValues::Zero } else { PossibleBitValues::One };
                PossibleValues::Assigned([second, last])
            }
            Immediate::Var(v) => self.0.get(v).copied().unwrap_or(PossibleValues::None)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PVRoundSummary {
    /// maps each block to the latest assumptions
    block_info: HashMap<BlockName, PossibleValuesEnv>,
}

impl Default for PVRoundSummary {
    fn default() -> Self {
        PVRoundSummary { block_info: HashMap::new() }
    }
}

pub struct AssertionRemover {
    /// The result of the previous round of analysis for blocks
    previous: PVRoundSummary,
    current: PVRoundSummary,
    /// The names of the parameters for every block in the program
    block_arg_names: HashMap<BlockName, Vec<VarName>>,
}

impl AssertionRemover {
    pub fn new<T>(prog: &Program<VarName, T>) -> Self {
        fn find_names_prog<T>(
            p: &Program<VarName, T>, blocks: &mut HashMap<BlockName, Vec<VarName>>,
        ) {
            for block in p.blocks.iter() {
                find_names_basic_block(&block, blocks);
            }
        }
        fn find_names_block_body<T>(
            b: &BlockBody<VarName, T>, blocks: &mut HashMap<BlockName, Vec<VarName>>,
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
            b: &BasicBlock<VarName, T>, blocks: &mut HashMap<BlockName, Vec<VarName>>,
        ) {
            blocks.insert(b.label.clone(), b.params.clone());
            find_names_block_body(&b.body, blocks);
        }
        let mut block_arg_names = HashMap::new();
        find_names_prog(prog, &mut block_arg_names);
        let mut previous = PVRoundSummary::default();
        for (l, _) in block_arg_names.iter() {
            previous.block_info.insert(l.clone(), PossibleValuesEnv::bottom());
        }
        Self { previous, current: PVRoundSummary::default(), block_arg_names }
    }

    /// Removes assertions that can be proven to always succeed at runtime.
    pub fn optimize(&mut self, prog: Program<VarName, Nil>) -> Program<VarName, Nil> {
        let analyzed_prog = self.analyze(prog);
        // println!("Analyzed:\n{}", analyzed_prog);
        self.remove_assertions(analyzed_prog)
    }

    /// Performs the possible-values analysis by fixed-point iteration
    fn analyze(&mut self, prog: Program<VarName, Nil>) -> Program<VarName, PossibleValuesEnv> {
        let mut prog = self.analyze_prog(prog);
        while self.previous != self.current {
            self.previous = std::mem::take(&mut self.current);
            prog = self.analyze_prog(prog);
        }
        prog
    }

    /// Fills in dataflow analysis information as well as updating self.current
    ///
    /// The input is generic in T because we don't need the previous
    /// round's liveness information everywhere, only the summary in
    /// self.previous.
    fn analyze_prog<T>(
        &mut self, prog: Program<VarName, T>,
    ) -> Program<VarName, PossibleValuesEnv> {
        // println!("Summary: {:?}", self.previous);
        // initialize the current summary to be trivial
        for (l, _) in self.block_arg_names.iter() {
            self.current.block_info.insert(l.clone(), PossibleValuesEnv::bottom());
        }
        for f in prog.funs.iter() {
            self.analyze_fun(f);
        }
        Program {
            blocks: prog.blocks.into_iter().map(|b| self.analyze_basic_block(b)).collect(),
            externs: prog.externs,
            funs: prog.funs,
        }
    }

    // Assumes all functions can have arbitrary (Any) inputs.
    fn analyze_fun(&mut self, f: &FunBlock<VarName>) {
        let args: Vec<PossibleValues> = f.params.iter().map(|_| PossibleValues::top()).collect();
        self.flow_branch(&f.body.target, &args, &PossibleValuesEnv::bottom());
    }

    fn analyze_basic_block<T>(
        &mut self, b: BasicBlock<VarName, T>,
    ) -> BasicBlock<VarName, PossibleValuesEnv> {
        let pre = self.previous.block_info.get(&b.label).unwrap().clone();
        let body = self.analyze_block_body(b.body, &pre);
        BasicBlock { label: b.label, params: b.params, ana: pre, body }
    }

    // update the BlockBody's info, with pre being the information we
    // know previous to runnning this BlockBody
    fn analyze_block_body<T>(
        &mut self, b: BlockBody<VarName, T>, pre: &PossibleValuesEnv,
    ) -> BlockBody<VarName, PossibleValuesEnv> {
        use ssa::BlockBody::*;
        match b {
            Terminator(t, _) => {
                self.flow_terminator(&t, pre);
                Terminator(t, pre.clone())
            }
            Operation { dest, op, next, .. } => {
                let post = self.flow_operation(&dest, &op, pre);
                Operation {
                    dest,
                    op,
                    next: Box::new(self.analyze_block_body(*next, &post)),
                    ana: post,
                }
            }
            SubBlocks { blocks, next, .. } => SubBlocks {
                blocks: blocks.into_iter().map(|b| self.analyze_basic_block(b)).collect(),
                next: Box::new(self.analyze_block_body(*next, pre)),
                ana: pre.clone(),
            },

            AssertType { ty, arg, next, .. } => {
                todo!("implement analysis for AssertType")
            }
            AssertLength { len, next, .. } => {
                todo!("implement AssertLength analysis")
            }
            AssertInBounds { bound, arg, next, .. } => {
                todo!("implement AssertInBounds analysis")
            }
            Store { addr, offset, val, next, .. } => {
                todo!("implement Store analysis")
            }
        }
    }

    /// Computes the flow function for a branch.
    ///
    /// Since this is a forwards dataflow analysis, this works by
    /// refining the information in the *target* of the branch.
    ///
    /// The arguments provided are the possible values of the arguments to the branch
    fn flow_branch(
        &mut self, target: &BlockName, args: &[PossibleValues], pre: &PossibleValuesEnv,
    ) {
        let targ_params = self.block_arg_names.get(target).unwrap();
        let mut post = pre.clone();
        for (name, pv) in targ_params.iter().zip(args) {
            post.0.insert(name.clone(), *pv);
        }
        let targ_info = self.current.block_info.get_mut(target).unwrap();
        targ_info.lub_mut(post);
    }

    /// Compute the flow function for the terminator.
    ///
    /// The flow function doesn't directly output anything, instead it
    /// should mutably update any blocks that the terminator may branch
    /// to.
    fn flow_terminator(&mut self, t: &Terminator<VarName>, pre: &PossibleValuesEnv) {
        use ssa::Terminator::*;
        match t {
            Return(_imm) => {}
            Branch(b) => {
                let arg_pvs: Vec<PossibleValues> =
                    b.args.iter().map(|imm| pre.possible_values(imm)).collect();
                self.flow_branch(&b.target, &arg_pvs, pre)
            }
            ConditionalBranch { cond, thn, els } => match pre.possible_values(cond) {
                PossibleValues::None => {}
                _ => {
                    self.flow_branch(&thn, &[], pre);
                    self.flow_branch(&els, &[], pre);
                }
            },
        }
    }

    /// Compute the flow function for an operation.
    fn flow_operation(
        &mut self, dest: &VarName, op: &Operation<VarName>, pre: &PossibleValuesEnv,
    ) -> PossibleValuesEnv {
        todo!("implement flow_operation")
    }

    /// Removes AssertInt assertions that are guaranteed by the dataflow analysis to succeed
    fn remove_assertions(
        &self, prog: Program<VarName, PossibleValuesEnv>,
    ) -> Program<VarName, Nil> {
        todo!("implement remove_assertions")
    }
}

/// Copy propagation
///
/// Replaces all uses of a variable with the variable it is assigned to.
pub struct CopyPropagator {
    // var_l = var_r, so all uses of var_l should be replaced with var_r
    vars: HashMap<VarName, VarName>,
}

impl CopyPropagator {
    pub fn new() -> Self {
        Self { vars: HashMap::new() }
    }

    pub fn query(&self, var: &VarName) -> Option<VarName> {
        if let Some(subst) = self.vars.get(var) {
            Some(self.query(subst).unwrap_or_else(|| subst.clone()))
        } else {
            None
        }
    }

    pub fn run(&mut self, mut prog: Program<VarName, Nil>) -> Program<VarName, Nil> {
        prog.blocks = prog.blocks.into_iter().map(|block| self.run_block(block)).collect();
        prog
    }

    fn run_block(&mut self, mut block: BasicBlock<VarName, Nil>) -> BasicBlock<VarName, Nil> {
        block.body = self.run_block_body(block.body);
        block
    }

    fn run_block_body(&mut self, body: BlockBody<VarName, Nil>) -> BlockBody<VarName, Nil> {
        match body {
            BlockBody::Terminator(terminator, ana) => {
                BlockBody::Terminator(self.run_terminator(terminator), ana)
            }
            BlockBody::Operation { dest, op, next, ana } => {
                let op = match op {
                    Operation::Immediate(imm) => match self.run_immediate(imm) {
                        Immediate::Const(c) => Operation::Immediate(Immediate::Const(c)),
                        Immediate::Var(v) => {
                            self.vars.insert(dest.clone(), v.clone());
                            return self.run_block_body(*next);
                        }
                    },
                    Operation::Prim1(prim1, imm) => {
                        Operation::Prim1(prim1, self.run_immediate(imm))
                    }
                    Operation::Prim2(prim2, imm1, imm2) => {
                        Operation::Prim2(prim2, self.run_immediate(imm1), self.run_immediate(imm2))
                    }
                    Operation::Call { fun, args } => Operation::Call {
                        fun,
                        args: args.into_iter().map(|imm| self.run_immediate(imm)).collect(),
                    },
                    Operation::AllocateArray { len } => {
                        Operation::AllocateArray { len: self.run_immediate(len) }
                    }
                    Operation::Load { addr, offset } => Operation::Load {
                        addr: self.run_immediate(addr),
                        offset: self.run_immediate(offset),
                    },
                };
                BlockBody::Operation { dest, op, next: Box::new(self.run_block_body(*next)), ana }
            }
            BlockBody::SubBlocks { blocks, next, ana } => BlockBody::SubBlocks {
                blocks: blocks.into_iter().map(|block| self.run_block(block)).collect(),
                next: Box::new(self.run_block_body(*next)),
                ana,
            },
            BlockBody::AssertType { ty, arg, next, ana } => BlockBody::AssertType {
                ty,
                arg: self.run_immediate(arg),
                next: Box::new(self.run_block_body(*next)),
                ana,
            },
            BlockBody::AssertLength { len, next, ana } => BlockBody::AssertLength {
                len: self.run_immediate(len),
                next: Box::new(self.run_block_body(*next)),
                ana,
            },
            BlockBody::AssertInBounds { bound, arg, next, ana } => BlockBody::AssertInBounds {
                bound: self.run_immediate(bound),
                arg: self.run_immediate(arg),
                next: Box::new(self.run_block_body(*next)),
                ana,
            },
            BlockBody::Store { addr, offset, val, next, ana } => BlockBody::Store {
                addr: self.run_immediate(addr),
                offset: self.run_immediate(offset),
                val: self.run_immediate(val),
                next: Box::new(self.run_block_body(*next)),
                ana,
            },
        }
    }

    fn run_terminator(&mut self, terminator: Terminator<VarName>) -> Terminator<VarName> {
        match terminator {
            Terminator::Return(imm) => Terminator::Return(self.run_immediate(imm)),
            Terminator::Branch(Branch { target, args }) => Terminator::Branch(Branch {
                target,
                args: args.into_iter().map(|imm| self.run_immediate(imm)).collect(),
            }),
            Terminator::ConditionalBranch { cond, thn, els } => {
                Terminator::ConditionalBranch { cond: self.run_immediate(cond), thn, els }
            }
        }
    }

    fn run_immediate(&mut self, imm: Immediate<VarName>) -> Immediate<VarName> {
        match imm {
            Immediate::Var(var) => Immediate::Var(self.query(&var).unwrap_or(var)),
            _ => imm,
        }
    }
}

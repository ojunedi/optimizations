use crate::identifiers::*;
use crate::types::*;

#[derive(Clone)]
pub struct Program<Var, Ana> {
    pub externs: Vec<Extern<Var>>,
    pub funs: Vec<FunBlock<Var>>,
    pub blocks: Vec<BasicBlock<Var, Ana>>,
}

#[derive(Clone)]
pub struct Extern<Var> {
    pub name: FunName,
    pub params: Vec<Var>,
}

#[derive(Clone)]
pub struct FunBlock<Var> {
    pub name: FunName,
    pub params: Vec<Var>,
    pub body: Branch<Var>,
}

#[derive(Clone)]
pub struct BasicBlock<Var, Ana> {
    pub label: BlockName,
    pub params: Vec<Var>,
    pub body: BlockBody<Var, Ana>,
    pub ana: Ana,
}

#[derive(Clone)]
pub enum BlockBody<Var, Ana> {
    Terminator(Terminator<Var>, Ana),
    Operation {
        dest: Var,
        op: Operation<Var>,
        next: Box<BlockBody<Var, Ana>>,
        ana: Ana,
    },
    SubBlocks {
        blocks: Vec<BasicBlock<Var, Ana>>,
        next: Box<BlockBody<Var, Ana>>,
        ana: Ana,
    },
    /// arg: tagged
    AssertType {
        ty: Type,
        arg: Immediate<Var>,
        next: Box<BlockBody<Var, Ana>>,
        ana: Ana,
    },
    /// len: untagged
    AssertLength {
        len: Immediate<Var>,
        next: Box<BlockBody<Var, Ana>>,
        ana: Ana,
    },
    /// bound: untagged, arg: untagged
    AssertInBounds {
        bound: Immediate<Var>,
        arg: Immediate<Var>,
        next: Box<BlockBody<Var, Ana>>,
        ana: Ana,
    },
    /// addr: untagged, offset: untagged, val: either
    Store {
        addr: Immediate<Var>,
        offset: Immediate<Var>,
        val: Immediate<Var>,
        next: Box<BlockBody<Var, Ana>>,
        ana: Ana,
    },
}

#[derive(Clone)]
pub enum Terminator<Var> {
    Return(Immediate<Var>),
    Branch(Branch<Var>),
    ConditionalBranch { cond: Immediate<Var>, thn: BlockName, els: BlockName },
}

#[derive(Clone)]
pub struct Branch<Var> {
    pub target: BlockName,
    pub args: Vec<Immediate<Var>>,
}

#[derive(Clone)]
pub enum Operation<Var> {
    Immediate(Immediate<Var>),
    Prim1(Prim1, Immediate<Var>),
    Prim2(Prim2, Immediate<Var>, Immediate<Var>),
    Call {
        fun: FunName,
        args: Vec<Immediate<Var>>,
    },
    /// len: untagged
    AllocateArray {
        len: Immediate<Var>,
    },
    /// addr: untagged, offset: untagged
    Load {
        addr: Immediate<Var>,
        offset: Immediate<Var>,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Prim1 {
    BitNot,
    // shift
    BitSal(u8),
    BitSar(u8),
    BitShl(u8),
    BitShr(u8),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Prim2 {
    // arithmetic
    Add,
    Sub,
    Mul,
    // logical
    BitAnd,
    BitOr,
    BitXor,
    // comparison
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Neq,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Immediate<Var> {
    Const(i64),
    Var(Var),
}

/* -------------------------------- Analysis -------------------------------- */

pub trait Analysis<Ana> {
    fn analysis(&self) -> &Ana;
}

impl<Var, Ana> Analysis<Ana> for BasicBlock<Var, Ana> {
    fn analysis(&self) -> &Ana {
        &self.ana
    }
}

impl<Var, Ana> Analysis<Ana> for BlockBody<Var, Ana> {
    fn analysis(&self) -> &Ana {
        match self {
            BlockBody::Terminator(.., ana) => ana,
            BlockBody::Operation { ana, .. } => ana,
            BlockBody::SubBlocks { ana, .. } => ana,
            BlockBody::AssertType { ana, .. } => ana,
            BlockBody::AssertLength { ana, .. } => ana,
            BlockBody::AssertInBounds { ana, .. } => ana,
            BlockBody::Store { ana, .. } => ana,
        }
    }
}

/* -------------------------------- Successor ------------------------------- */
pub trait Successor {
    type Succ;
    fn successor(&self) -> Option<&Self::Succ>;
}

impl<Var, Ana> Successor for BasicBlock<Var, Ana> {
    type Succ = BlockBody<Var, Ana>;
    fn successor(&self) -> Option<&Self::Succ> {
        Some(&self.body)
    }
}

impl<Var, Ana> Successor for BlockBody<Var, Ana> {
    type Succ = BlockBody<Var, Ana>;

    fn successor(&self) -> Option<&Self::Succ> {
        match self {
            BlockBody::Terminator(..) => None,
            BlockBody::Operation { next, .. } => Some(next),
            BlockBody::SubBlocks { next, .. } => Some(next),
            BlockBody::AssertType { next, .. } => Some(next),
            BlockBody::AssertLength { next, .. } => Some(next),
            BlockBody::AssertInBounds { next, .. } => Some(next),
            BlockBody::Store { next, .. } => Some(next),
        }
    }
}

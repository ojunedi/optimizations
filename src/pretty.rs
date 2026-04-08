use std::fmt;

/* ------------------------------- Combinators ------------------------------ */

pub struct Indent<'a, T: ?Sized>(pub usize, pub &'a T);
impl<'a, T: ?Sized> Indent<'a, T> {
    fn inner(&self) -> (usize, &'a T) {
        (self.0, self.1)
    }
}

pub struct Separated<'a, T, Iter>(pub &'a Iter, pub &'static str)
where
    Iter: Iterator<Item = T> + Clone;

impl<T: fmt::Debug, Iter: Iterator<Item = T> + Clone> fmt::Debug for Separated<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0.clone().enumerate())
            .map(|(i, t)| {
                if i > 0 {
                    fmt::Display::fmt(self.1, f)?;
                }
                t.fmt(f)
            })
            .collect()
    }
}

impl<T: fmt::Display, Iter: Iterator<Item = T> + Clone> fmt::Display for Separated<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.0.clone().enumerate())
            .map(|(i, t)| {
                if i > 0 {
                    fmt::Display::fmt(self.1, f)?;
                }
                t.fmt(f)
            })
            .collect()
    }
}

pub struct Surfix<'a, T, Iter>(pub &'a Iter, pub &'static str)
where
    Iter: Iterator<Item = T> + Clone;

impl<T: fmt::Debug, Iter: Iterator<Item = T> + Clone> fmt::Debug for Surfix<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0
            .clone()
            .map(|t| {
                t.fmt(f)?;
                fmt::Display::fmt(self.1, f)
            })
            .collect()
    }
}

impl<T: fmt::Display, Iter: Iterator<Item = T> + Clone> fmt::Display for Surfix<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0
            .clone()
            .map(|t| {
                t.fmt(f)?;
                self.1.fmt(f)
            })
            .collect()
    }
}

pub struct Comma<'a, T, Iter>(pub &'a Iter)
where
    Iter: Iterator<Item = T> + Clone;

impl<T: fmt::Debug, Iter: Iterator<Item = T> + Clone> fmt::Debug for Comma<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Separated(self.0, ", ").fmt(f)
    }
}

impl<T: fmt::Display, Iter: Iterator<Item = T> + Clone> fmt::Display for Comma<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Separated(self.0, ", ").fmt(f)
    }
}

pub struct LineBreaks<'a, T, Iter>(pub &'a Iter)
where
    Iter: Iterator<Item = T> + Clone;

impl<T: fmt::Debug, Iter: Iterator<Item = T> + Clone> fmt::Debug for LineBreaks<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Surfix(self.0, "\n").fmt(f)
    }
}

impl<T: fmt::Display, Iter: Iterator<Item = T> + Clone> fmt::Display for LineBreaks<'_, T, Iter> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Surfix(self.0, "\n").fmt(f)
    }
}

/* ----------------------------- Implementations ---------------------------- */

/// Pretty ugly printing of the (Resolved) AST
mod impl_ast {
    use super::*;
    use crate::ast::*;

    impl<Var: fmt::Display, Fun: fmt::Display> fmt::Display for Prog<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Prog { externs, name, param: (param, _), body, loc: _ } = self;
            write!(f, "{}def {}({}): {}", LineBreaks(&externs.iter()), name, param, body)
        }
    }

    impl<Var: fmt::Display, Fun: fmt::Display> fmt::Display for ExtDecl<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "extern {}({}) and", self.name, Comma(&self.params.iter().map(|(p, _)| p)))
        }
    }

    impl<Var: fmt::Display, Fun: fmt::Display> fmt::Display for Expr<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Expr::Num(n, _) => write!(f, "{}", n),
                Expr::Bool(b, _) => write!(f, "{}", b),
                Expr::Var(v, _) => write!(f, "{}", v),
                Expr::Prim { prim, args, loc: _ } => match prim {
                    Prim::Add1 | Prim::Sub1 | Prim::IsType(_) | Prim::NewArray | Prim::Length => {
                        write!(f, "{}({})", prim, &args[0])
                    }
                    Prim::Add
                    | Prim::Sub
                    | Prim::Mul
                    | Prim::Not
                    | Prim::And
                    | Prim::Or
                    | Prim::Lt
                    | Prim::Le
                    | Prim::Gt
                    | Prim::Ge
                    | Prim::Eq
                    | Prim::Neq => write!(f, "({} {} {})", &args[0], prim, &args[1]),
                    Prim::MakeArray => {
                        write!(f, "[{}]", Comma(&args.into_iter()))
                    }
                    Prim::ArrayGet => {
                        write!(f, "{}[{}]", &args[0], &args[1])
                    }
                    Prim::ArraySet => {
                        write!(f, "{}[{}] := {}", &args[0], &args[1], &args[2])
                    }
                },
                Expr::Let { bindings, body, loc: _ } => {
                    write!(f, "let {} in {}", Comma(&bindings.iter()), body)
                }
                Expr::If { cond, thn, els, loc: _ } => {
                    write!(f, "if {}: {} else: {}", cond, thn, els)
                }
                Expr::FunDefs { decls, body, loc: _ } => {
                    write!(f, "{} in {}", Separated(&decls.iter(), " and "), body)
                }
                Expr::Call { fun, args, loc: _ } => {
                    write!(f, "{}({})", fun, Comma(&args.iter()))
                }
            }
        }
    }

    impl<Var: fmt::Display, Fun: fmt::Display> fmt::Display for Binding<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{} = {}", self.var.0, self.expr)
        }
    }

    impl<Var: fmt::Display, Fun: fmt::Display> fmt::Display for FunDecl<Var, Fun> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "def {} ({}): {}",
                self.name,
                Comma(&self.params.iter().map(|(p, _)| p)),
                self.body
            )
        }
    }

    impl fmt::Debug for Prim {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim::Add => write!(f, "add"),
                Prim::Sub => write!(f, "sub"),
                Prim::Mul => write!(f, "mul"),
                Prim::Not => write!(f, "not"),
                Prim::And => write!(f, "and"),
                Prim::Or => write!(f, "or"),
                Prim::Lt => write!(f, "lt"),
                Prim::Le => write!(f, "le"),
                Prim::Gt => write!(f, "gt"),
                Prim::Ge => write!(f, "ge"),
                Prim::Eq => write!(f, "eq"),
                Prim::Neq => write!(f, "neq"),
                Prim::Add1
                | Prim::Sub1
                | Prim::IsType(_)
                | Prim::NewArray
                | Prim::MakeArray
                | Prim::ArrayGet
                | Prim::ArraySet
                | Prim::Length => fmt::Display::fmt(self, f),
            }
        }
    }

    impl fmt::Display for Prim {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim::Add1 => write!(f, "add1"),
                Prim::Sub1 => write!(f, "sub1"),
                Prim::Not => write!(f, "!"),
                Prim::Add => write!(f, "+"),
                Prim::Sub => write!(f, "-"),
                Prim::Mul => write!(f, "*"),
                Prim::And => write!(f, "&&"),
                Prim::Or => write!(f, "||"),
                Prim::Lt => write!(f, "<"),
                Prim::Le => write!(f, "<="),
                Prim::Gt => write!(f, ">"),
                Prim::Ge => write!(f, ">="),
                Prim::Eq => write!(f, "=="),
                Prim::Neq => write!(f, "!="),
                Prim::IsType(ty) => write!(f, "is{}", ty),
                Prim::NewArray => write!(f, "newArray"),
                Prim::MakeArray => write!(f, "mkArray"),
                Prim::ArrayGet => write!(f, "arrayGet"),
                Prim::ArraySet => write!(f, "arraySet"),
                Prim::Length => write!(f, "length"),
            }
        }
    }
}

mod impl_ssa {
    use super::*;
    use crate::ssa::*;

    impl<Var, Ana> fmt::Debug for Program<Var, Ana>
    where
        Var: fmt::Display,
        Ana: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Program { externs, funs, blocks } = self;
            LineBreaks(&externs.iter()).fmt(f)?;
            LineBreaks(&funs.iter()).fmt(f)?;
            LineBreaks(&blocks.iter().map(|b| Indent(0, b))).fmt(f)?;
            Ok(())
        }
    }

    impl<Var, Ana> fmt::Display for Program<Var, Ana>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Program { externs, funs, blocks } = self;
            LineBreaks(&externs.iter()).fmt(f)?;
            LineBreaks(&funs.iter()).fmt(f)?;
            LineBreaks(&blocks.iter().map(|b| Indent(0, b))).fmt(f)?;
            Ok(())
        }
    }

    impl<Var> fmt::Debug for Extern<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Extern { name, params } = self;
            write!(f, "extern {}({})", name, Comma(&params.iter()))
        }
    }

    impl<Var> fmt::Display for Extern<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Extern { name, params } = self;
            write!(f, "extern {}({})", name, Comma(&params.iter()))
        }
    }

    impl<Var> fmt::Debug for FunBlock<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let FunBlock { name, params, body } = self;
            write!(f, "fun {}({}):\n", name, Comma(&params.iter()))?;
            write!(f, "  br {}", body)
        }
    }

    impl<Var> fmt::Display for FunBlock<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let FunBlock { name, params, body } = self;
            write!(f, "fun {}({}):\n", name, Comma(&params.iter()))?;
            write!(f, "  br {}", body)
        }
    }

    impl<Var, Ana> fmt::Debug for Indent<'_, BasicBlock<Var, Ana>>
    where
        Var: fmt::Display,
        Ana: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let (indent, BasicBlock { label, params, body, ana }) = self.inner();
            write!(f, "{}", "  ".repeat(indent))?;
            write!(f, "block {} {} ({}):", label, ana, Comma(&params.iter()))?;
            writeln!(f)?;
            Indent(indent + 1, body).fmt(f)?;
            Ok(())
        }
    }

    impl<Var, Ana> fmt::Display for Indent<'_, BasicBlock<Var, Ana>>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let (indent, BasicBlock { label, params, body, .. }) = self.inner();
            write!(f, "{}", "  ".repeat(indent))?;
            write!(f, "block {}({}):", label, Comma(&params.iter()))?;
            writeln!(f)?;
            Indent(indent + 1, body).fmt(f)?;
            Ok(())
        }
    }

    impl<Var, Ana> fmt::Debug for Indent<'_, BlockBody<Var, Ana>>
    where
        Var: fmt::Display,
        Ana: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let (indent, body) = self.inner();
            match body {
                BlockBody::Terminator(terminator, ana) => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    ana.fmt(f)?;
                    writeln!(f)?;
                    write!(f, "{}", "  ".repeat(indent))?;
                    terminator.fmt(f)?;
                    Ok(())
                }
                BlockBody::Operation { dest, op, next, ana } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    ana.fmt(f)?;
                    writeln!(f)?;
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "{} = {}", dest, op)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::SubBlocks { blocks, next, ana } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    ana.fmt(f)?;
                    writeln!(f)?;
                    LineBreaks(&blocks.iter().map(|b| Indent(indent, b))).fmt(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::AssertType { ty, arg: of, next, ana } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    ana.fmt(f)?;
                    writeln!(f)?;
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "assert{}({})", ty, of)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::AssertLength { len, next, ana } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    ana.fmt(f)?;
                    writeln!(f)?;
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "assertLength({})", len)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::AssertInBounds { bound, arg: of, next, ana } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    ana.fmt(f)?;
                    writeln!(f)?;
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "assertInBounds({}, {})", bound, of,)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::Store { addr, offset: off, val, next, ana } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    ana.fmt(f)?;
                    writeln!(f)?;
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "store({}, {}, {})", addr, off, val)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
            }
        }
    }

    impl<Var, Ana> fmt::Display for Indent<'_, BlockBody<Var, Ana>>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let (indent, body) = self.inner();
            match body {
                BlockBody::Terminator(terminator, ..) => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    terminator.fmt(f)?;
                    Ok(())
                }
                BlockBody::Operation { dest, op, next, .. } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "{} = {}", dest, op)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::SubBlocks { blocks, next, .. } => {
                    LineBreaks(&blocks.iter().map(|b| Indent(indent, b))).fmt(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::AssertType { ty, arg: of, next, .. } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "assert{}({})", ty, of)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::AssertLength { len, next, .. } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "assertLength({})", len)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::AssertInBounds { bound, arg: of, next, .. } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "assertInBounds({}, {})", bound, of,)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
                BlockBody::Store { addr, offset: off, val, next, .. } => {
                    write!(f, "{}", "  ".repeat(indent))?;
                    write!(f, "store({}, {}, {})", addr, off, val)?;
                    writeln!(f)?;
                    Indent(indent, next.as_ref()).fmt(f)?;
                    Ok(())
                }
            }
        }
    }

    impl<Var> fmt::Debug for Terminator<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Terminator::Return(imm) => write!(f, "ret {}", imm),
                Terminator::Branch(branch) => write!(f, "br {}", branch),
                Terminator::ConditionalBranch { cond, thn, els } => {
                    write!(f, "cbr {} {} {}", cond, thn, els)
                }
            }
        }
    }

    impl<Var> fmt::Display for Terminator<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Terminator::Return(imm) => write!(f, "ret {}", imm),
                Terminator::Branch(branch) => write!(f, "br {}", branch),
                Terminator::ConditionalBranch { cond, thn, els } => {
                    write!(f, "cbr {} {} {}", cond, thn, els)
                }
            }
        }
    }

    impl<Var> fmt::Debug for Branch<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Branch { target, args } = self;
            write!(f, "{}({})", target, Comma(&args.iter()))
        }
    }

    impl<Var> fmt::Display for Branch<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Branch { target, args } = self;
            write!(f, "{}({})", target, Comma(&args.iter()))
        }
    }

    impl<Var> fmt::Debug for Operation<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Operation::Immediate(imm) => write!(f, "{}", imm),
                Operation::Prim1(prim @ Prim1::BitNot, imm) => write!(f, "{} {}", prim, imm),
                Operation::Prim1(prim, imm) => write!(f, "{} {}", imm, prim),
                Operation::Prim2(prim, imm1, imm2) => write!(f, "{} {} {}", imm1, prim, imm2),
                Operation::Call { fun, args } => write!(f, "{}({})", fun, Comma(&args.iter())),
                Operation::AllocateArray { len } => write!(f, "allocateArray({})", len),
                Operation::Load { addr, offset: off } => write!(f, "load({}, {})", addr, off),
            }
        }
    }

    impl<Var> fmt::Display for Operation<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Operation::Immediate(imm) => write!(f, "{}", imm),
                Operation::Prim1(prim @ Prim1::BitNot, imm) => write!(f, "{} {}", prim, imm),
                Operation::Prim1(prim, imm) => write!(f, "{} {}", imm, prim),
                Operation::Prim2(prim, imm1, imm2) => write!(f, "{} {} {}", imm1, prim, imm2),
                Operation::Call { fun, args } => write!(f, "{}({})", fun, Comma(&args.iter())),
                Operation::AllocateArray { len } => write!(f, "allocateArray({})", len),
                Operation::Load { addr, offset: off } => write!(f, "load({}, {})", addr, off),
            }
        }
    }

    impl fmt::Debug for Prim1 {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim1::BitNot => write!(f, "bit_not"),
                Prim1::BitSal(n) => write!(f, "bit_sal/{}", n),
                Prim1::BitSar(n) => write!(f, "bit_sar/{}", n),
                Prim1::BitShl(n) => write!(f, "bit_shl/{}", n),
                Prim1::BitShr(n) => write!(f, "bit_shr/{}", n),
            }
        }
    }

    impl fmt::Display for Prim1 {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim1::BitNot => write!(f, "~"),
                Prim1::BitSal(n) => write!(f, "<< {}", n),
                Prim1::BitSar(n) => write!(f, ">> {}", n),
                Prim1::BitShl(n) => write!(f, "<<< {}", n),
                Prim1::BitShr(n) => write!(f, ">>> {}", n),
            }
        }
    }

    impl fmt::Debug for Prim2 {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim2::Add => write!(f, "add"),
                Prim2::Sub => write!(f, "sub"),
                Prim2::Mul => write!(f, "mul"),
                Prim2::BitAnd => write!(f, "bit_and"),
                Prim2::BitOr => write!(f, "bit_or"),
                Prim2::BitXor => write!(f, "bit_xor"),
                Prim2::Lt => write!(f, "lt"),
                Prim2::Le => write!(f, "le"),
                Prim2::Gt => write!(f, "gt"),
                Prim2::Ge => write!(f, "ge"),
                Prim2::Eq => write!(f, "eq"),
                Prim2::Neq => write!(f, "neq"),
            }
        }
    }

    impl fmt::Display for Prim2 {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Prim2::Add => write!(f, "+"),
                Prim2::Sub => write!(f, "-"),
                Prim2::Mul => write!(f, "*"),
                Prim2::BitAnd => write!(f, "&"),
                Prim2::BitOr => write!(f, "|"),
                Prim2::BitXor => write!(f, "^"),
                Prim2::Lt => write!(f, "<"),
                Prim2::Le => write!(f, "<="),
                Prim2::Gt => write!(f, ">"),
                Prim2::Ge => write!(f, ">="),
                Prim2::Eq => write!(f, "=="),
                Prim2::Neq => write!(f, "!="),
            }
        }
    }

    impl<Var> fmt::Debug for Immediate<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Immediate::Const(c) => write!(f, "{}", c),
                Immediate::Var(v) => write!(f, "{}", v),
            }
        }
    }

    impl<Var> fmt::Display for Immediate<Var>
    where
        Var: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Immediate::Const(c) => write!(f, "{}", c),
                Immediate::Var(v) => write!(f, "{}", v),
            }
        }
    }
}

//! Simply Typed Lambda Calculus
//!

use std::rc::Rc;

pub mod statics;
pub mod dynamics;

#[derive(Debug,PartialEq,Eq,Clone)]
pub enum Type {
    /// ()
    Unit,
    /// τ+τ
    Sum(RcType, RcType),
    /// τ→τ
    Arr(RcType, RcType),
}

pub type RcType = Rc<Type>;

impl Type {
    pub fn unit() -> RcType { Rc::new (Type::Unit) }
    pub fn sum(tleft: RcType, tright: RcType) -> RcType { Rc::new (Type::Sum(tleft, tright)) }
    pub fn arr(tdom: RcType, tcod: RcType) -> RcType { Rc::new (Type::Arr(tdom, tcod)) }
}

#[derive(Debug)]
pub enum Var<'s> {
    /// Local variable with its DeBruijn index
    Local(u32),
    /// Global variable identified by its name
    Global(&'s str)
}

#[derive(Debug,Copy,Clone)]
pub enum Dir { Left, Right }

impl Dir {
    pub fn select<T> (&self, left: T, right: T) -> T {
	match &self {
	    Dir::Left => left,
	    Dir::Right => right
	}
    }
}

/// A marker to indicate a binding form
type Bind<T> = T;

#[derive(Debug)]
pub enum Term<'s> {
    /// x
    Var(Var<'s>),
    /// λ:τ.m
    Lam(RcType, Bind<RcTerm<'s>>),
    /// m₁ m₂
    App(RcTerm<'s>, RcTerm<'s>),
    /// in{l/r}:τ m
    Inj(Dir, RcType, RcTerm<'s>),
    /// case:τ (m; .m; .m)
    Case(RcType, RcTerm<'s>, Bind<RcTerm<'s>>, Bind<RcTerm<'s>>),
    Unit
}

pub type RcTerm<'s> = Rc<Term<'s>>;

pub mod variables {
    use super::*;
    pub fn shift<'s> (n: u32, v: &Var<'s>) -> Option<Var<'s>> {
        match v {
            Var::Local(m) => Some(Var::Local(n + m)),
            Var::Global(_s) => None
        }
    }

}

impl<'s> Var<'s> {
    pub fn is_local (&self) -> bool {
        match self {
            Var::Local(_) => true,
            Var::Global(_) => false,
        }
    }
}

impl<'s> Term<'s> {
    pub fn local_var(idx: u32) -> RcTerm<'s> { Rc::new (Term::Var (Var::Local (idx))) }

    pub fn unit() -> RcTerm<'s> { Rc::new (Term::Unit) }
    pub fn lam(ty: RcType, body: Bind<RcTerm<'s>>) -> RcTerm<'s> { Rc::new (Term::Lam (ty, body)) }
    pub fn app(fun: RcTerm<'s>, arg: RcTerm<'s>) -> RcTerm<'s> { Rc::new (Term::App (fun, arg)) }

    pub fn inj(dir: Dir, ty: RcType, term: RcTerm<'s>) -> RcTerm<'s> {
	Rc::new (Term::Inj (dir, ty, term))
    }

    pub fn inl (ty:RcType, term: RcTerm<'s>) -> RcTerm<'s> { Term::inj (Dir::Left, ty, term) }
    pub fn inr (ty:RcType, term: RcTerm<'s>) -> RcTerm<'s> { Term::inj (Dir::Right, ty, term) }

    pub fn case (ty: RcType, subj: RcTerm<'s>, left: Bind<RcTerm<'s>>, right: Bind<RcTerm<'s>>) -> RcTerm<'s> {
	Rc::new (Term::Case (ty, subj, left, right))
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_is_local () {
        assert! (Var::Local (0).is_local());
    }
}

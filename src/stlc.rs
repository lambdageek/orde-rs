// Simply Typed Lambda Calculus  syntax
// 
use std::rc::Rc;

pub mod statics;
pub mod dynamics;

#[derive(Debug,PartialEq,Eq)]
pub enum Type {
    Unit,
    Arr(RcType, RcType),
}

pub type RcType = Rc<Type>;

impl Type {
    pub fn unit() -> RcType { Rc::new (Type::Unit) }
    pub fn arr(tdom: RcType, tcod: RcType) -> RcType { Rc::new (Type::Arr(tdom, tcod)) }
}

#[derive(Debug)]
pub enum Var<'s> {
    Local(u32),
    Global(&'s str)
}

#[derive(Debug)]
pub enum Term<'s> {
    Var(Var<'s>),
    Lam(RcType, RcTerm<'s>),
    App(RcTerm<'s>, RcTerm<'s>),
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
    pub fn unit() -> RcTerm<'s> { Rc::new (Term::Unit) }
    pub fn lam(ty: RcType, body: RcTerm<'s>) -> RcTerm<'s> { Rc::new (Term::Lam (ty, body)) }
    pub fn app(fun: RcTerm<'s>, arg: RcTerm<'s>) -> RcTerm<'s> { Rc::new (Term::App (fun, arg)) }

    pub fn local_var(idx: u32) -> RcTerm<'s> { Rc::new (Term::Var (Var::Local (idx))) }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_is_local () {
        assert! (Var::Local (0).is_local());
    }
}

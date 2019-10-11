// Simply Typed Lambda Calculus  syntax
// 
use std::rc::Rc;

mod statics;

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
pub enum Var {
    Local(u32),
    Global(String)
}

#[derive(Debug)]
pub enum Term {
    Var(Var),
    Lam(RcType, RcTerm),
    App(RcTerm, RcTerm),
    Unit
}

pub type RcTerm = Rc<Term>;

pub mod variables {
    use super::*;
    pub fn shift (n: u32, v: &Var) -> Option<Var> {
        match v {
            Var::Local(m) => Some(Var::Local(n + m)),
            Var::Global(_s) => None
        }
    }

}

impl Var {
    pub fn is_local (&self) -> bool {
        match self {
            Var::Local(_) => true,
            Var::Global(_) => false,
        }
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

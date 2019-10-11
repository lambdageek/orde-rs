
use super::*;


#[derive(Debug)]
pub enum Ctx<'a> {
    Nil,
    Snoc(&'a Ctx<'a>, RcType)
}

impl<'a> Ctx<'a> {
    pub fn nil() -> Ctx<'a> { Ctx::Nil }
    pub fn snoc(&'a self, ty: RcType) -> Ctx<'a> {
        Ctx::Snoc (self, ty)
    }

    pub fn lookup(&self, idx: u32) -> Option<RcType> {
        match &self {
            Ctx::Nil => Option::None,
            Ctx::Snoc (ctx, ty) => if idx == 0 { Option::Some(Rc::clone(ty)) } else { ctx.lookup(idx - 1) }
        }
    }
}

#[derive(Debug,PartialEq,Eq)]
pub enum TypeError {
    NotImplemented,
    NoGlobalVariable(String),
    NoLocalVariable(u32)
}

fn not_implemented() -> Result<RcType, TypeError> {
    Err(TypeError::NotImplemented)
}


fn infer_var<'a>(ctx: &'a Ctx<'a>, var: &Var) -> Result<RcType, TypeError> {
    match var {
        Var::Local(idx) => match ctx.lookup (*idx) {
            Some(ty) => Ok(ty.clone()),
            None => Err(TypeError::NoLocalVariable(*idx))
        }
        Var::Global(str) => Err(TypeError::NoGlobalVariable(str.clone()))
    }
}

pub fn check<'a>(ctx: &'a Ctx<'a>, term: &Term) -> Result<RcType, TypeError> {
    match term {
        Term::Unit => Ok (Rc::new(Type::Unit)),
        Term::Var(v) => infer_var(ctx, v),
        _ => not_implemented()
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn check_unit() {
        let nil_ctx = Ctx::nil ();
        let tm = Term::Unit;
        assert_eq!(check(&nil_ctx, &tm), Result::Ok(Type::unit()));
    }

    #[test]
    fn check_0var() {
        let nil_ctx = Ctx::nil ();
        let ctx = Ctx::snoc (&nil_ctx, Type::unit());
        let tm = Term::Var(Var::Local(0));
        assert_eq!(check(&ctx, &tm), Ok(Type::unit()))
    }

    #[test]
    fn check_0var_nil() {
        let nil_ctx = Ctx::nil ();
        let tm = Term::Var(Var::Local(0));
        assert_eq!(check(&nil_ctx, &tm), Err(TypeError::NoLocalVariable (0)));
    }
}

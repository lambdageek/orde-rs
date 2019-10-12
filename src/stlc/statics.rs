
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
pub enum TypeError<'s> {
    #[cfg(has_unimpl)]
    NotImplemented,
    NoGlobalVariable(&'s str),
    NoLocalVariable(u32),
    ExpectedFunctionTypeGot(RcType),
    ExpectedSumTypeGot(RcType),
    ExpectedTypeMismatch {wanted: RcType, given: RcType}
}

#[cfg(has_unimpl)]
fn not_implemented<'s>() -> Result<RcType, TypeError<'s>> {
    Err(TypeError::NotImplemented)
}


fn infer_var<'a,'s>(ctx: &'a Ctx<'a>, var: &Var<'s>) -> Result<RcType, TypeError<'s>> {
    match var {
        Var::Local(idx) => match ctx.lookup (*idx) {
            Some(ty) => Ok(ty.clone()),
            None => Err(TypeError::NoLocalVariable(*idx))
        }
        Var::Global(str) => Err(TypeError::NoGlobalVariable(str))
    }
}

fn expect_arr<'s>(ty: RcType) -> Result<(RcType,RcType), TypeError<'s>> {
    match &*ty {
	Type::Arr(dom,cod) => Ok((dom.clone(),cod.clone())),
	_ => Err(TypeError::ExpectedFunctionTypeGot(ty.clone()))
    }
}

fn expect_sum<'s>(ty: RcType) -> Result<(RcType,RcType), TypeError<'s>> {
    match &*ty {
	Type::Sum(tleft, tright) => Ok ((tleft.clone(), tright.clone())),
	_ => Err(TypeError::ExpectedSumTypeGot(ty.clone()))
    }
}

fn expect_eq<'s>(wanted: RcType, given: RcType) -> Result<(), TypeError<'s>> {
    if *wanted == *given {
	Ok(())
    } else {
	Err(TypeError::ExpectedTypeMismatch {wanted: wanted.clone(), given: given.clone()})
    }
}

pub fn extend_and_check<'a,'s>(ctx: &'a Ctx<'a>, ty: RcType, body: &Bind<Term<'s>>) -> Result<RcType, TypeError<'s>> {
    let ctx = Ctx::snoc (ctx, ty);
    check (&ctx, body)
}

pub fn check<'a,'s>(ctx: &'a Ctx<'a>, term: &Term<'s>) -> Result<RcType, TypeError<'s>> {
    match term {
        Term::Unit => Ok (Rc::new(Type::Unit)),
        Term::Var(v) => infer_var(ctx, v),
	Term::Lam(ty, term) => {
	    // let ctx = Ctx::snoc (ctx, ty.clone ());
	    //let tycod = check (&ctx, term)?;
	    let tycod = extend_and_check (ctx, ty.clone(), term)?;
	    Ok (Type::arr ((*ty).clone(), tycod))
	}
	Term::App (term1, term2) => {
	    let tyfun = check (ctx, term1)?;
	    let (tyarg, tyres) = expect_arr (tyfun)?;
	    let tyarg2 = check (ctx, term2)?;
	    expect_eq (tyarg, tyarg2)?;
	    Ok (tyres)
	}
	Term::Inj (dir, ty, term) => {
	    let (tleft, tright) = expect_sum (ty.clone())?;
	    let ty = dir.select (tleft, tright);
	    let tinfer = check (ctx, term)?;
	    expect_eq (ty.clone (), tinfer)?;
	    Ok (ty)
	}
	Term::Case (tres, subj, left, right) => {
	    let tysubj = check (ctx, subj)?;
	    let (tleft, tright) = expect_sum (tysubj)?;
	    let tleft = extend_and_check (ctx, tleft, left)?;
	    let tright = extend_and_check (ctx, tright, right)?;
	    expect_eq (tres.clone (), tleft)?;
	    expect_eq (tres.clone (), tright)?;
	    Ok (tres.clone ())
	}
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

    fn id_fun<'s>(ty:RcType) -> RcTerm<'s> {
	Term::lam (ty.clone (), Term::local_var (0))
    }

    #[test]
    fn check_id_fun() {
	let nil_ctx = Ctx::nil ();
	let tm = id_fun (Type::unit ());
	assert_eq!(check(&nil_ctx, &tm), Ok(Type::arr(Type::unit(), Type::unit())));
    }

    #[test]
    fn check_id_fun_app() {
	let nil_ctx = Ctx::nil ();
	let tm = Term::app (id_fun (Type::unit ()), Term::unit ());
	assert_eq!(check(&nil_ctx, &tm), Ok(Type::unit ()));
    }

    #[test]
    fn check_unit_app_bad() {
	let nil_ctx = Ctx::nil ();
	let u = Term::unit ();
	let tm = Term::app (u.clone(), u);
	assert_eq!(check(&nil_ctx, &tm), Err(TypeError::ExpectedFunctionTypeGot(Type::unit())));
    }

    #[test]
    fn check_id_app_bad_arg() {
	let nil_ctx = Ctx::nil ();
	let id = id_fun (Type::unit ());
	let tm = Term::app (id.clone (), id);
	let u = Type::unit ();
	let u_arr_u = Type::arr (u.clone(), u.clone());
	assert_eq!(check(&nil_ctx, &tm), Err(TypeError::ExpectedTypeMismatch {wanted: u, given: u_arr_u}));
    }
}

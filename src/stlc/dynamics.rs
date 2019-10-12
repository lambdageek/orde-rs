
/// SECD machine
///
/// Env :: {} | Env*val
/// val ::= () | clo (E) m | inj dir val
/// C ::= [] m | (clo (E) m) [] | inj dir [] | case [] m1 m2
///
/// K ::= eval: m | ret: val
/// S ::= # | C ; S
/// D ::= done | pop: (Env + S) then D
///
/// Env | K | S | D  --->  Env | K | S | D
///
/// Env | eval:j | S | D ---> Env | ret: nth(Env,j) | S | D
/// Env | eval:() | S | D ---> Env | ret: () | S | D
/// Env | eval:lam m | S | D ---> Env | ret: clo (Env) m | S | D
/// Env | eval:app m1 m2 | S | D ---> Env | eval: m1 | [] m2 ; S | D
/// Env | eval:inj A dir m | S | D ---> Env | eval: m | inj dir [] ; S | D
/// Env | eval:case A m l r | S | D ---> Env | eval: m | case [] l r ; S | D
///
/// {} | ret:val | # | done    terminal
///
/// _  | ret:val | # | pop (Env + S) then D  ---> Env | ret: val | S | D
/// Env | ret: val | inj dir [] ; S | D  ---> Env | ret: inj dir val | S | D
/// Env | ret:(clo Env2 m) | [] m2 ; S | D  ---> Env | eval: m2 | (clo Env2 m) [] ; S | D
/// Env | ret:val | clo (Env2 m) [] ; S | D ---> Env2*val | eval: m | # | pop (Env + S) then D
/// Env | ret:inj dir val | case [] l r ; S | D --> Env*val | eval: dir.select(l,r) | S | D

use super::*;

#[derive(Debug,Clone)]
pub struct Closure<'s> {env: RcEnv<'s>, body: RcTerm<'s> }

#[derive(Debug)]
pub enum Val<'s> {
    Unit,
    Closure (Closure<'s>),
    Inj (Dir, RcVal<'s>)
}

impl<'s> PartialEq for Val<'s> {
    fn eq(&self, other: &Self) -> bool {
	match (&self, other) {
	    (Val::Unit, Val::Unit) => true,
	    _ => false
	}
    }
}

type RcVal<'s> = Rc<Val<'s>>;

impl<'s> Val<'s> {
    pub fn unit() -> RcVal<'s> {
	Rc::new (Val::Unit)
    }

    pub fn inj(dir: Dir, val: RcVal<'s>) -> RcVal<'s> {
	Rc::new (Val::Inj (dir, val))
    }
}

#[derive(Debug)]
pub enum Env<'s> {
    Nil,
    Snoc(RcEnv<'s>, RcVal<'s>)
}

type RcEnv<'s> = Rc<Env<'s>>;

impl<'s> Env<'s> {
    pub fn nil() -> RcEnv<'s> {
	Rc::new (Env::Nil)
    }

    pub fn snoc(env: RcEnv<'s>, val:RcVal<'s>) -> RcEnv<'s> {
	Rc::new (Env::Snoc(env, val))
    }

    pub fn lookup(&self, j: u32) -> Option<RcVal<'s>> {
	match &self {
	    Env::Nil => None,
	    Env::Snoc(env, val) => if j == 0 { Some(val.clone ()) } else { env.lookup (j - 1) }
	}
    }
}

#[derive(Debug)]
pub enum Cont<'s> {
    App1 (RcTerm<'s>),
    App2 (Closure<'s>),
    Inj (Dir),
    Case (Bind<RcTerm<'s>>, Bind<RcTerm<'s>>)
}

#[derive(Debug)]
pub enum Stack<'s> {
    Nil,
    Cons(Cont<'s>, RcStack<'s>)
}

type RcStack<'s> = Rc<Stack<'s>>;

impl<'s> Stack<'s> {
    pub fn nil() -> RcStack<'s> {
	Rc::new (Stack::Nil)
    }

    pub fn app1 (tm2: RcTerm<'s>, stk: RcStack<'s>) -> RcStack<'s> {
	Rc::new (Stack::Cons(Cont::App1(tm2), stk))
    }

    pub fn app2 (clo: Closure<'s>, stk: RcStack<'s>) -> RcStack<'s> {
	Rc::new (Stack::Cons(Cont::App2(clo), stk))
    }

    pub fn inj (dir: Dir, stk: RcStack<'s>) -> RcStack<'s> {
	Rc::new (Stack::Cons(Cont::Inj(dir), stk))
    }

    pub fn case (left: Bind<RcTerm<'s>>, right: Bind<RcTerm<'s>>, stk: RcStack<'s>) -> RcStack<'s> {
	Rc::new (Stack::Cons(Cont::Case(left,right), stk))
    }
}

#[derive(Debug,Clone)]
pub enum Control<'s> {
    Eval (RcTerm<'s>),
    Ret (RcVal<'s>)
}

#[derive(Debug)]
pub enum Dump<'s> {
    Done,
    Pop {frame: (RcEnv<'s>, RcStack<'s>), then: RcDump<'s>}
}

type RcDump<'s> = Rc<Dump<'s>>;

impl<'s> Dump<'s> {
    pub fn done () -> RcDump<'s> {
	Rc::new (Dump::Done)
    }

    pub fn pop(env: RcEnv<'s>, stk: RcStack<'s>, then: RcDump<'s>) -> RcDump<'s> {
	Rc::new (Dump::Pop {frame: (env, stk), then})
    }
}
    

#[derive(Debug,Clone)]
pub struct Config<'s> {
    env: RcEnv<'s>,
    control: Control<'s>,
    stack: RcStack<'s>,
    dump: RcDump<'s>
}

impl<'s> Config<'s> {
    pub fn initial(term: RcTerm<'s>) -> Config<'s> {
	let env = Env::nil();
	let control = Control::Eval(term);
	let stack = Stack::nil();
	let dump = Dump::done();
	Config {env, control, stack, dump}
    }
}

pub fn is_done<'s> (cfg: &Config<'s>) -> Option<RcVal<'s>> {
    match (&cfg.control, &*cfg.stack, &*cfg.dump) {
	(Control::Ret (val), Stack::Nil, Dump::Done) => Some(val.clone ()),
	_ => None
    }
}

#[derive(Debug)]
pub enum DynamicErr<'s> {
    Finished,
    UnboundVariable(u32),
    UnboundGlobal(&'s str),
    ApplicationNotClosure,
    CaseNotInj,
}


fn lookup_var<'s> (env: &Env<'s>, j: u32) -> Result<RcVal<'s>, DynamicErr<'s>> {
    match env.lookup (j) {
	None => Err(DynamicErr::UnboundVariable(j)),
	Some(val) => Ok(val)
    }
}

fn closure<'s> (env: RcEnv<'s>, body: RcTerm<'s>) -> RcVal<'s> {
    Rc::new (Val::Closure (Closure {env, body}))
}

fn expect_closure<'s> (val: RcVal<'s>) -> Result<Closure<'s>, DynamicErr<'s>> {
    match &*val {
	Val::Closure (clo) => Ok (clo.clone ()),
	_ => Err(DynamicErr::ApplicationNotClosure)
    }
}

fn expect_inj<'s> (val: RcVal<'s>) -> Result<(Dir, RcVal<'s>), DynamicErr<'s>> {
    match &*val {
	Val::Inj (dir, val) => Ok ((*dir, val.clone())),
	_ => Err(DynamicErr::CaseNotInj)
    }
}

pub fn step<'s> (cfg: Config<'s>) -> Result<Config<'s>, DynamicErr<'s>> {
    match cfg {
	Config {control: Control::Eval (tm), env, stack, dump} =>
	    match &*tm {
		Term::Var(Var::Local(j)) =>
		    Ok (Config {control: Control::Ret (lookup_var (&env, *j)?), env, stack, dump}),
		Term::Var(Var::Global(s)) => Err(DynamicErr::UnboundGlobal(s)),

		Term::Lam (_ty, body) =>
		    Ok (Config {control: Control::Ret (closure (env.clone(), body.clone())), env, stack, dump}),

		Term::App (tm1, tm2) =>
		    Ok (Config {control: Control::Eval (tm1.clone ()), env, stack: Stack::app1 (tm2.clone (), stack), dump}),

		Term::Unit => Ok (Config {control: Control::Ret (Val::unit()), env, stack, dump}),

		Term::Inj(dir, _ty, tm) => Ok (Config { control: Control::Eval(tm.clone ()), env, stack: Stack::inj (*dir, stack), dump }),
		Term::Case(_ty, tm, left, right) =>
		    Ok (Config { control: Control::Eval(tm.clone ()),
				 env,
				 stack: Stack::case (left.clone(), right.clone(), stack),
				 dump }),
	    }
	Config {control: Control::Ret (val), env, stack, dump} =>
	    match &*stack {
		Stack::Nil => match &*dump {
		    Dump::Done => Err (DynamicErr::Finished),
		    Dump::Pop {frame: (env,stack), then: dump} =>
			Ok (Config {control: Control::Ret (val),
				    env: env.clone (),
				    stack: stack.clone(),
				    dump: dump.clone()})
		}
		Stack::Cons (k, stack) =>
		    match k {
			Cont::App1(term2) => {
			    let clo = expect_closure (val)?;
			    Ok (Config {control: Control::Eval(term2.clone()),
					env,
					stack: Stack::app2 (clo, stack.clone()),
					dump})
			},
			Cont::App2(Closure {env: env2, body}) => {
			    let env3 = Env::snoc(env2.clone(), val);
			    let dump = Dump::pop(env.clone(), stack.clone(), dump.clone());
			    Ok (Config {control: Control::Eval(body.clone()),
					env: env3,
					stack: Stack::nil (),
					dump: dump})
			},
			Cont::Inj(dir) =>
			    Ok (Config {control: Control::Ret (Val::inj(*dir, val)),
					env,
					stack: stack.clone (),
					dump}),
			Cont::Case(left, right) => {
			    let (dir, val) = expect_inj (val)?;
			    let env = Env::snoc (env.clone (), val);
			    Ok (Config {control: Control::Eval (dir.select (left.clone(), right.clone())),
					env,
					stack: stack.clone(),
					dump })
			}
		    }
	    }
    }
}

pub fn eval<'s> (term: RcTerm<'s>) -> Result<RcVal<'s>, DynamicErr<'s>> {
    let mut c = Config::initial (term);
    loop {
	if let Some(v) = is_done (&c) {
	    break Ok(v);
	} else {
	    c = step (c)?;
	}
    }
}

#[derive(Debug)]
pub enum Stepped<'s> {
    Done (RcVal<'s>),
    NotDone (Config<'s>),
}

pub fn step_n<'s> (term: RcTerm<'s>, n: u32) -> Result<Stepped<'s>, DynamicErr<'s>> {
    let mut c = Config::initial (term);
    for _ in 0..n {
	if let Some(v) = is_done (&c) {
	    return Ok(Stepped::Done(v));
	} else {
	    c = step (c)?;
	}
    }
    Ok(Stepped::NotDone (c))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn done_is_done() {
	let nil_env = Env::nil ();
	let done = Dump::done ();
	let c = Config {
	    env: nil_env,
	    control: Control::Ret (Val::unit ()),
	    stack: Stack::nil (),
	    dump: done
	};
	assert_eq! (is_done (&c), Some(Val::unit ()))
    }

    #[test]
    fn eval_id_unit() {
	let uty = Type::unit ();
	let id = Term::lam (uty, Term::local_var (0));
	let term = Term::app (id, Term::unit ());
	assert_eq! (format! ("{:?}", eval (term)), "Ok(Unit)");
    }

    #[test]
    fn eval_tt_inl() {
	let boolty = Type::sum(Type::unit(), Type::unit());
	let tr = Term::inl(boolty.clone(), Term::unit());
	let tt = Term::lam(boolty.clone(), Term::lam(boolty.clone(), Term::local_var (1)));
	let prog = Term::app (tt, tr);
	let ans = eval (prog);
	assert_eq! (format! ("{:?}", ans), "Ok(Closure(Closure { env: Snoc(Nil, Inj(Left, Unit)), body: Var(Local(1)) }))");
	    
    }

    #[test]
    fn eval_lam_case() {
	// type 2 = () + ()
	// let tr = inl 2 ()
	// let fa = inr 2 ()
	// let tt = \x:2.\y:2.x
	// let ff = \x:2.\y:2.y
	// (\u. case (2->2) u {x. x tr} {x. x fa}) (inl (2 -> 2 -> 2)+... tt)
	let boolty = Type::sum(Type::unit(), Type::unit());
	let tr = Term::inl(boolty.clone(), Term::unit());
	let fa = Term::inr(boolty.clone(), Term::unit());
	let tt = Term::lam(boolty.clone(), Term::lam(boolty.clone(), Term::local_var (1)));
	let _ff = Term::lam(boolty.clone(), Term::lam(boolty.clone(), Term::local_var (0)));
	let left = Term::app(Term::local_var(0), tr.clone());
	let right = Term::app(Term::local_var(0), fa.clone());
	let b2b = Type::arr(boolty.clone(), boolty.clone());
	let b22b = Type::arr(boolty.clone(), b2b.clone());
	let c = Term::case (b2b.clone(), Term::local_var(0), left, right);
	let sumb22b = Type::sum(b22b.clone(), b22b.clone ());
	let l = Term::lam (sumb22b.clone(), c);
	let prog = Term::app (l, Term::inl(sumb22b, tt.clone()));
	let ans = eval(prog);
	assert_eq!(format!("{:?}", ans), "Ok(Closure(Closure { env: Snoc(Nil, Inj(Left, Unit)), body: Var(Local(1)) }))");
    }
}

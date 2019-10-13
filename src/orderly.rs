//! The orderly lambda calculus
//!
//! Based on
//!
//! Leaf Petersen, Robert Harper, Karl Crary, Frank Pfenning. _A Type
//! Theory for Memory Allocation and Data Layout._  POPL 2003.

use std::rc::Rc;
use std::vec::Vec;
use std::marker::PhantomData;

#[derive(Debug,Eq,PartialEq,Clone)]
pub enum Type {
    /// ()
    Unit,
    /// int
    Int,
    /// τ→τ
    Arr(RcType, RcType),
    /// τ•τ
    Fuse(RcType, RcType),
    /// !τ
    Ptr(RcType),
    /// Nonsense
    ///
    /// The nonsense type represents uninitialized memory
    NS(u32),
}

pub type RcType = Rc<Type>;

impl Type {
    pub fn size (&self) -> u32 {
	match &self {
	    Type::Unit => 0,
	    Type::Int | Type::Ptr(_) | Type::Arr(_,_) => 1,
	    Type::Fuse(ty1, ty2) => ty1.size() + ty2.size (),
	    Type::NS(j) => *j
	}
    }

    /// The derived load operation in the paper is type-driven
    pub fn load(&self, i: u32) -> Option<RcType> {
	match &self {
	    Type::Fuse(ty1, ty2) => {
		let sz = ty1.size ();
		if sz > i { ty1.load (i) }
		else { ty2.load (i - sz) }
	    },
	    Type::NS(sz) =>
		if i < *sz { Some(Rc::new (Type::NS(1))) } else { None },
	    _ => if i == 0 { Some (Rc::new (self.clone())) } else {None}
	}
    }
}

/// A trait that marks the syntactic categories.  Used as a bound on `Var`.
pub trait Syntax {}

/// Variables
///
/// Variables at the syntactic level given by `T`
#[derive (Debug)]
pub struct Var<T : Syntax> {
    local: u32,
    phantom: PhantomData<T>
}

/// Heap locations
///
/// An allocated heap location that contains a value of a type of kind `Kind::Heap`
#[derive(Debug)]
pub struct Loc {
    /// Location names are abstract
    name: u32
}

/// Coercion terms
///
/// Coercion terms let you focus on a piece of the ordered context
/// without changing its size or changing its representation
#[derive(Debug)]
pub enum Coer {
    Var (Var<Coer>),
    Unit,
    Fuse(RcCoer, RcCoer),
}

type RcCoer = Rc<Coer>;

impl Syntax for Coer {}

// annoying to have to resort to this
type BindTerm<T> = T;
type BindCoer<T> = T;

/// Pure terms
///
/// Pure terms do not reserve or allocate in the course of their computation
#[derive(Debug)]
pub enum Term {
    Var (Var<Term>),
    /// Nonsense
    NS,
    IntConst(i32),
    Lam(RcType,BindTerm<RcExpr>),
    Ptr(Loc),
}

pub type RcTerm = Rc<Term>;

impl Syntax for Term {}

/// Effectful expressions
///
/// Expressions represent possibly-effectful computations
#[derive(Debug)]
pub enum Expr {
    // Ordinary expressions
    Ret(RcTerm),
    App(RcTerm, RcTerm),
    Let(RcExpr, RcType, BindTerm<RcExpr>),

    // Memory management
    Reserve(u32, BindCoer<RcExpr>),
    Alloc(RcCoer, BindTerm<RcExpr>),
    Assign(RcCoer, RcTerm, BindCoer<RcExpr>),

    // Coercion eliminations
    ElimUnit(RcCoer, RcExpr),
    ElimFuse(RcCoer, BindCoer<BindCoer<RcExpr>>),
    LetCoer(RcCoer, BindCoer<RcExpr>),

    // Memory Load
    Load(RcType, u32, RcTerm, BindTerm<RcExpr>)
}

pub type RcExpr = Rc<Expr>;

pub mod statics {
    //! Static semantics

    use super::*;

    #[derive(Debug,Eq,PartialEq,Clone,Copy)]
    pub enum Kind { Reg , Heap }


    /// Ordered Contexts
    ///
    /// Variables in an ordered context cannot be rearranged, duplicated
    /// or discared.  (That is, it's a linear context with the further
    /// restriction that reordering variables is not allowed).  In the
    /// orderly lambda calculus, the ordered contexts are used to model
    /// memory heaps.  Each type in the ordered context may have kind Reg
    /// or kind [`Kind::Heap`].
    #[derive(Debug)]
    pub struct OCtx {
	contents: Vec<RcType>
    }

    impl OCtx {
	pub fn size (&self) -> u32 { self.contents.iter().map(|ty| ty.size()).sum () }
    }

    /// Ordinary Contexts
    ///
    /// The ordinary typing context is used to model the register file
    /// of a machine.  As a result, It may only contain types of kind
    /// [Kind] `Reg` that each have size 1 corresponding to one machine
    /// word.
    pub enum Ctx {
	Nil,
	Snoc (RcCtx, RcType)
    }

    pub type RcCtx = Rc<Ctx>;
}

pub mod dynamics {
    //! Dynamic semantics

    use super::*;

    #[derive(Debug)]
    pub enum HeapVal {
	Unit,
	NS(u32),
	IntConst(i32),
	Fuse(RcHeapVal,RcHeapVal),
	Fn(RcType,BindTerm<RcExpr>),
	
    }

    pub type RcHeapVal = Rc<HeapVal>;


    #[derive(Debug)]
    pub stuct Frontier {
	frontier: Vec[RcHeapVal],
    }
}

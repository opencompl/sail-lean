import SailLean.Syntax.AST
import SailLean.Syntax.Elab
import Aesop
import Qq
import Mathlib.Lean.Meta.Simp

open Qq Lean Elab Term

namespace Sail

/-inductive TypArg where | nexp (n : Q(Nat)) | type (t : Q(Type)) | bool (c : Q(Prop))
  deriving Repr-/

/-- Obtain the kind of a typ argument. -/
def AST.TypArg.kind : AST.TypArg → AST.Kind
  | .nexp _ => .int
  | .bool _ => .bool
  | .typ _ => .type


def kindUniv : AST.Kind → Expr
  | .type => q(Type 1)
  | _ => q(Type)

/-- Quote Sail's type parameter into `Type 0` or `Type 1`. -/
def quoteKind : (k : AST.Kind) → Expr
  | .int => q(_root_.Int)
  | .bool => q(Prop)
  | .type => q(Type)

inductive QuantItem where
  | kId (k : AST.KId)
  | nConstraint (c : AST.NConstraint)  -- TODO maybe save in quoted form (`Q(Prop)`)
  | dom
  deriving Inhabited, BEq

def QuantItem.ofASTQuantItem : AST.QuantItem → QuantItem
  | .nConstraint c => .nConstraint c
  | .kindedId (.kId i) => .kId i
  | .kindedId (.annotated _ i) => .kId i

abbrev TypeVarCtx := List QuantItem

variable (ctx : TypeVarCtx)

def quoteNExp : AST.NExp → Q(_root_.Int)
  | .constant n => q($n)
  | .var k =>
    -- Look up the variable in the context to obtain the DeBruĳn index
    match ctx.indexOf? (.kId k) with
    | .some idx => Expr.bvar idx
    | .none => panic! "variable not found in context!"
  | .sum m n => q($(quoteNExp m) + $(quoteNExp n))
  | .product m n => q($(quoteNExp m) * $(quoteNExp n))
  | .subtraction m n => q($(quoteNExp m) - $(quoteNExp n))
  | .neg n => q(-$(quoteNExp n))
  | .exponential n => q(2^$(quoteNExp n).toNat) -- TODO[semantics] negative exponents?
  | _ => panic! "not able to quote this nexp yet!"

def quoteTypArg : (a : AST.TypArg) → Expr
  | .nexp n => quoteNExp ctx n
  | .typ t => q(Unit)  -- TODO need recursion here
  | .bool c => q(True)  -- TODO quote nconstraints

def AST.Kind.isType : AST.Kind → _root_.Bool
  | .type => .true
  | _ => .false

def AST.Kind.level (k : AST.Kind) : Level := if k.isType then 1 else 0

/-- Build the argument type out of a list of Sail kinds, also return its universe level -/
def liftKindListToProduct : List AST.Kind → (Expr × Level)
  | [] => (q(True), 0)
  | [k] => (quoteKind k, k.level)
  | k::ks =>
    let l1 := k.level
    let (e, l2) := liftKindListToProduct ks
    (mkApp2 (mkConst `PProd [l1, l2]) (quoteKind k) e, mkLevelMax l1 l2)

/-- Build the tuple of type arguments given a `List AST.TypArg`.
It should have the type `(liftKindListToProduct (args.map AST.TypArg.kind)).1`.
Also returns its universe level. -/
def liftTypArgListToTuple : List AST.TypArg → Expr
  | [] => (q(.intro) : Q(True))
  | [arg] => quoteTypArg ctx arg
  | (arg::args) =>
    let lhs := quoteTypArg ctx arg
    let l := arg.kind.level
    let tlhs := quoteKind arg.kind
    let rhs := liftTypArgListToTuple args
    let (trhs, l') := liftKindListToProduct (args.map (·.kind))
    mkApp4 (mkConst `PProd.mk [l, l']) tlhs trhs lhs rhs

structure RegisteredType where
  params : List AST.Kind := []
  typ : Expr

instance : Repr RegisteredType where
  reprPrec o _ :=
    match o with
    | ⟨params@ [], t⟩
    | ⟨params@ (_::_), t⟩ => s!"({repr params}, { repr t }})"

def liftListToProduct : List Q(Type) → Q(Type 1)
  | [] => q(PUnit.{2})
  | [t] => t
  | t::ts => q($t × $(liftListToProduct ts))

structure Env where
  typ_ids : Std.HashMap AST.Id RegisteredType

/-- Quotes any Typ from the AST into the quotation of a Lean type, provided an environment -/
partial def quoteTyp (ctx : TypeVarCtx) (e : Env) : AST.Typ → TermElabM Q(Type 1)
  | .fn s t => return q($(← quoteTyp ctx e s) → $(← quoteTyp (.dom :: ctx) e t))
  | .tuple ts => return q($(liftListToProduct (← ts.mapM (quoteTyp ctx e))))
  | .app i args =>
      match e.typ_ids[i]? with
      | .some ⟨params, t⟩ =>
        match params with
        | [] => return t  -- TODO wrap in effects monad
        | params@(_::_) => do
          let argTuple := liftTypArgListToTuple ctx args
          unless params = args.map AST.TypArg.kind do
            panic! "kind of argument do not match the kinds of parameters!"
          let e := mkApp t argTuple
          return e
      | _ => throwError "could not find type {repr i} in environment. \n
         environment: {repr e.typ_ids.toList}"
  | _ => throwError "unable to quote type"

partial def quoteTypschm (e : Env) (ctx : TypeVarCtx := []) : AST.Typschm → TermElabM Q(Type 1)
  | ⟨[], t⟩ => quoteTyp ctx e t
  | ⟨q::qs, t⟩ => do
    let (head, n) : Q(Type 1) × String := match q with
      | .kindedId (.annotated k i) => (quoteKind k, i)
      | .nConstraint c => panic! "nconstraints not supported right now"  -- TODO
      | _ => panic! "need kind annotations for quantifiers right now"  -- TODO fill these in on the "way back up"
    let q := QuantItem.ofASTQuantItem q
    let body ← quoteTypschm e (q::ctx) ⟨qs, t⟩
    return .forallE (.mkSimple n) head body .default

/- Testing -/

def sailUnit : RegisteredType where
  typ := q(Unit)

def sailBool : RegisteredType where
  typ := q(_root_.Bool)

def sailBits : RegisteredType where
  params := [.int]
  typ := q(BitVec ∘ Int.toNat)  -- TODO see if the `ulift`s are getting too annoying to work with

/-- Example environment for tests -/
def std_env : Env where
  typ_ids := Std.HashMap.ofList
    [(.ident "bool", sailBool), (.ident "bits", sailBits)]

def testTypeQuotation (stx : TermElabM (Lean.TSyntax `typschm)) : TermElabM Lean.Format := do
  match elabTypschm (← stx) with
  | .error err => throwError err
  | .ok astx =>
    let qt ← quoteTypschm std_env [] astx
    let qt ← Core.betaReduce (← Meta.whnf qt)
    let qt' := (← Meta.simpOnlyNames [`Function.comp_apply] qt).1
    let _ ← Meta.inferType qt'
    Lean.Meta.ppExpr qt'

#eval testTypeQuotation `(typschm| forall Int @m, Int @n. (bits(@m), bits(@n)) -> bits(@m + @n))

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

/-- Quote Sail's type parameter into `Type 1` (instead of `Type`, since they can be quoted to
`Type`s) -/
def quoteKind : AST.Kind → Q(Type 1)
  | .int => q(ULift _root_.Int)
  | .bool => q(ULift Prop)
  | .type => q(Type)

inductive QuantItem where
  | kId (k : AST.KId)
  | nConstraint (c : AST.NConstraint)  -- TODO maybe save in quoted form (`Q(Prop)`)
  deriving Inhabited, BEq

def QuantItem.ofASTQuantItem : AST.QuantItem → QuantItem
  | .nConstraint c => .nConstraint c
  | .kindedId (.kId i) => .kId i
  | .kindedId (.annotated _ i) => .kId i

abbrev TypeVarCtx := List QuantItem

variable (ctx : TypeVarCtx)

def quoteNExp : AST.NExp → Q(ULift.{1} Nat)
  | .constant n => q(⟨$n⟩)
  | .var k =>
    -- Look up the variable in the context to obtain the DeBruĳn index
    match ctx.indexOf? (.kId k) with
    | .some idx => Expr.bvar idx
    | .none => panic! "variable not found in context!"
  | .sum m n => q(⟨$(quoteNExp m).down + $(quoteNExp n).down⟩)
  | .product m n => q(⟨$(quoteNExp m).down * $(quoteNExp n).down⟩)
  | .subtraction m n => q(⟨$(quoteNExp m).down - $(quoteNExp n).down⟩)  -- TODO[semantics] is this really a monus
  | _ => panic! "not able to quote this nexp yet!"

def quoteTypArg : (a : AST.TypArg) → Q($(quoteKind a.kind))
  | .nexp n => quoteNExp ctx n
  | .typ t => q(Unit)  -- TODO need recursion here
  | .bool c => q(⟨True⟩)  -- TODO quote nconstraints

def liftListToProduct : List Q(Type) → Q(Type 1)
  | [] => q(PUnit.{2})
  | [t] => t
  | t::ts => q($t × $(liftListToProduct ts))

def liftKindListToProduct : List AST.Kind → Q(Type 1) :=
  liftListToProduct ∘ (·.map quoteKind)

/-- Build a tuple -/
def buildTuple (ts : List Expr) (es : List Expr) : Expr :=
 match ts, es with
 | [], [] => (q(.unit) : Q(PUnit.{2}))
 | [_], [e] => e
 | (t::ts), (e::es) => mkApp4 (.const `Prod.mk [mkLevelSucc levelOne]) t (liftListToProduct ts) e (buildTuple ts es)
 | _, _ => panic! "incorrect number of arguments!"

/-- Build the tuple of type arguments given a `List AST.TypArg`.
It should have the type `liftKindListToProduct (args.map AST.TypArg.kind)`. -/
def liftTypArgListToTuple (args : List AST.TypArg) :
    Q($(liftKindListToProduct (args.map AST.TypArg.kind))) :=
  buildTuple (args.map (quoteKind ∘ AST.TypArg.kind)) (args.map (quoteTypArg ctx))

def RegisteredTypeKind : List AST.Kind → Q(Type 1)
  | [] => q(Type)
  | args@(_::_) => q($(liftKindListToProduct args) → Type)

@[simp]
theorem registeredTypeKind_nil : RegisteredTypeKind [] = q(Type) := rfl

@[simp]
theorem registeredTypeKind_cons :
     RegisteredTypeKind (a::as) = q($(liftKindListToProduct (a::as)) → Type) := rfl

structure RegisteredType where
  params : List AST.Kind := []
  type : Q($(RegisteredTypeKind params))

instance : Repr RegisteredType where
  reprPrec o _ :=
    match o with
    | ⟨params@ [], t⟩
    | ⟨params@ (_::_), t⟩ =>
      s!"({repr params}, {by { simp at t; exact repr t }})"

structure Env where
  typ_ids : Std.HashMap AST.Id RegisteredType

/-- Quotes any Typ from the AST into the quotation of a Lean type, provided an environment -/
partial def quoteTyp (e : Env) : AST.Typ → TermElabM Q(Type 1)
  | .fn s t => return q($(← quoteTyp e s) → $(← quoteTyp e t))
  | .tuple ts => return q($(liftListToProduct (← ts.mapM (quoteTyp e))))
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
    let head : Q(Type 1) := match q with
      | .kindedId (.annotated k i) => quoteKind k
      | .nConstraint c => panic! "nconstraints not supported right now"  -- TODO
      | _ => panic! "need kind annotations for quantifiers right now"  -- TODO fill these in on the "way back up"
    let q := QuantItem.ofASTQuantItem q
    let body ← quoteTypschm e (q::ctx) ⟨qs, t⟩
    return .forallE .anonymous head body .default

/- Testing -/

def sailUnit : RegisteredType where
  type := q(Unit)

def sailBool : RegisteredType where
  type := q(_root_.Bool)

def sailBits : RegisteredType where
  params := [.int]
  type := q(BitVec ∘ Int.toNat ∘ ULift.down)  -- TODO see if the `ulift`s are getting too annoying to work with

/-- Example environment for tests -/
def std_env : Env where
  typ_ids := Std.HashMap.ofList
    [(.ident "bool", sailBool)
     , (.ident "bits", sailBits)]

def testTypeQuotation (stx : TermElabM (Lean.TSyntax `typschm)) : TermElabM Lean.Format := do
  match elabTypschm (← stx) with
  | .error err => throwError err
  | .ok astx =>
    let qt ← quoteTypschm std_env [] astx
    let qt ← Core.betaReduce (← Meta.whnf qt)
    let qt' := (← Meta.simpOnlyNames [`Function.comp_apply] qt).1
    Lean.Meta.ppExpr qt'

#eval testTypeQuotation `(typschm| forall Int @m, Int @n. (bits(@m), bits(@n)) -> bits(@m + @n))

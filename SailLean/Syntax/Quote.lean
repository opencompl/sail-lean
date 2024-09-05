import SailLean.Syntax.AST
import SailLean.Syntax.Elab
import Aesop
import Qq

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
  | .int => q(ULift Nat)
  | .bool => q(ULift Prop)
  | .type => q(Type)

def quoteTypArg : (a : AST.TypArg) → Q($(quoteKind a.kind))
  | .nexp n => q(⟨42⟩)  -- TODO quote as equality somehow
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
  buildTuple (args.map (quoteKind ∘ AST.TypArg.kind)) (args.map quoteTypArg)

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

def sailUnit : RegisteredType where
  type := q(Unit)

def sailBool : RegisteredType where
  type := q(_root_.Bool)

def sailFin : RegisteredType where
  params := [.int]
  type := q(Fin ∘ ULift.down)  -- TODO see if the `ulift`s are getting too annoying to work with

def foo : List α → _root_.Bool
  | [] => .false
  | (_::_) => .true

def std_env : Env where
  typ_ids := Std.HashMap.ofList
    [(.ident "bool", sailBool)
     , (.ident "fin", sailFin)]

/-- Quotes any Typ from the AST into the quotation of a Lean type, provided an environment -/
partial def quoteTyp (e : Env) : AST.Typ → Lean.Elab.Term.TermElabM Q(Type 1)
  | .fn []         dom => quoteTyp e dom
  | .fn args       dom => return q($(liftListToProduct (← args.mapM (quoteTyp e)))
                                      → $(← quoteTyp e dom))
  | .tuple []      => return q(PUnit)
  | .tuple [t]     => quoteTyp e t
  | .tuple (t::ts) => return q($(← quoteTyp e t) × $(← quoteTyp e (.tuple ts)))
  | .app i args =>
      --println! "fgoo"
      match e.typ_ids[i]? with
      | .some ⟨params, t⟩ =>
        match params with
        | [] => return t
        | params@(_::_) => do
          let argTuple := liftTypArgListToTuple args
          unless params = args.map AST.TypArg.kind do
            panic! "kind of argument do not match the kinds of parameters!"
          let e := mkApp t argTuple
          return e
      | _ => throwError "could not find type {repr i} in environment. \n
         environment: {repr e.typ_ids.toList}"
  | _ => throwError "unable to quote type"

def testTypeQuotation (stx : Lean.Elab.Term.TermElabM (Lean.TSyntax `typ)) :
    Lean.Elab.Term.TermElabM Lean.Format := do
  let .ok astx := elabTyp (← stx) | throwError "unable to elaborate type"
  let qt ← quoteTyp std_env astx
  Lean.Meta.ppExpr qt

#eval testTypeQuotation `(typ|(foo))

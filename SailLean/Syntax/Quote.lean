import SailLean.Syntax.AST
import SailLean.Syntax.Elab
import Aesop
import Qq

open Qq

namespace Sail

inductive TypArg where | nexp (n : Q(Nat)) | type (t : Q(Type)) | bool (c : Q(Prop))

def quoteTypArgType : TypArg → Q(Type)
  | .nexp n => q(Unit)  -- TODO quote as equality somehow
  | .type t => t
  | .bool c => q(Inhabited $c)  -- TODO sure?

def liftListToProduct : List Q(Type) → Q(Type)
  | [] => q(Unit)
  | [t] => t
  | t::ts => q($t × $(liftListToProduct ts))

def liftTypArgListToProduct : List TypArg → Q(Type) :=
  liftListToProduct ∘ (·.map quoteTypArgType)

def RegisteredTypeKind : List TypArg → Type
  | [] => Q(Type)
  | args@(_::_) => Q(Type → Type)

structure RegisteredType where
  args : List TypArg := []
  type : RegisteredTypeKind args

structure Env where
  typ_ids : Std.HashMap AST.Id RegisteredType

def sailUnit : RegisteredType where
  type := q(Unit)

def sailBool : RegisteredType where
  type := q(_root_.Bool)

def sailFin : RegisteredType where
  args := [.type q(Nat)]
  type := q(Fin)

def std_env : Env where
  typ_ids := Std.HashMap.ofList [(.ident `bool, sailBool), (.ident `fin, sailFin)]

partial def quoteTyp (e : Env) : AST.Typ → Q(Type)
  | .fn []          dom => quoteTyp e dom
  | .fn args       dom => q($(liftListToProduct (args.map (quoteTyp e))) → $(quoteTyp e dom))
  | .tuple []      => q(Unit)
  | .tuple [t]     => quoteTyp e t
  | .tuple (t::ts) => q($(quoteTyp e t) × $(quoteTyp e (.tuple ts)))
  | .id i =>
      let ⟨args, t⟩ := e.typ_ids.getD i sailUnit  -- TODO fail instead
      match args with
      | [] => t
      | _ => panic! "called type without giving arguments"  -- TODO tidy
  | _ => q(Unit)

#eval! Lean.Meta.ppExpr <| quoteTyp std_env <|
  (.tuple [.tuple [], .fn [.id (.ident `bool)] (.tuple [])])

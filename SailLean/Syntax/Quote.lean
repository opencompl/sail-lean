import SailLean.Syntax.AST
import Qq

open Qq

namespace Sail

structure Env where
  typ_ids : Std.HashMap AST.Id Q(Type)

def std_env : Env where
  typ_ids := Std.HashMap.ofList [(.ident `bool, q(Bool))]

def quoteTyp (e : Env) : AST.Typ → Q(Type)
  | .fn []          dom => quoteTyp e dom
  | .fn [arg]       dom => q($(quoteTyp e arg) → $(quoteTyp e dom))
  | .fn (arg::args) dom => q($(quoteTyp e arg) → $(quoteTyp e (.fn args dom)))
  | .tuple []      => q(Unit)
  | .tuple [t]     => quoteTyp e t
  | .tuple (t::ts) => q($(quoteTyp e t) × $(quoteTyp e (.tuple ts)))
  | .id i => e.typ_ids.getD i q(Unit)  -- TODO fail instead
  | _ => q(Unit)

#eval Lean.Meta.ppExpr <| quoteTyp std_env (.tuple [.tuple [], .fn [.id (.ident `bool)] (.tuple [])])

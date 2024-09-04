import Std.Data.HashSet
import Mathlib.Tactic.DeriveToExpr

namespace Sail.AST

/-!
# The AST for Sail
-/

inductive Id where
  | ident (i : Lean.Name)
  | operator (i : Lean.Name)
  deriving Lean.ToExpr, Repr, BEq, Hashable

def KId := Lean.Name
  deriving Lean.ToExpr, Repr

inductive Kind where
  | type
  | int
  | bool
  deriving Inhabited, Lean.ToExpr, Repr

inductive KindedId
  | kId (k : KId)
  | annotated (k : Kind) (k' : KId)
  deriving Repr

inductive Order where
  | dec
  | inc
  deriving Repr

mutual

inductive NExp where
  | id (i : Id)
  | var (k : KId)
  | constant (n : Nat)
  | app (fn : Id) (ns : List NExp)
  | ifThenElse (p : NConstraint) (t : NExp) (e : NExp)
  | product (m n : NExp)
  | sum (m n : NExp)
  | subtraction (m n : NExp)
  | exponential (n : NExp)
  | neg (n : NExp)
  deriving Repr

inductive Typ where
  | id (i : Id)
  | var (k : KId)
  | fn (args : List Typ) (dom : Typ)
  | bidir (t s : Typ)
  | tuple (ts : List Typ)
  | app (i : Id) (args : List TypArg)
  | exist (ids : List KindedId) (c : NConstraint) (t : Typ)
  deriving Repr

inductive TypArg where
  | nexp (n : NExp)
  | typ (t : Typ)
  | bool (c : NConstraint)
  deriving Repr

inductive NConstraint
  | equal (m n : TypArg)
  | not_equal (m n : TypArg)
  | ge (m n : NExp)
  | gt (m n : NExp)
  | le (m n : NExp)
  | lt (m n : NExp)
  | set (k : KId) (ns : Std.HashSet Nat)
  | or (l r : NConstraint)
  | and (l r : NConstraint)
  | app (i : Lean.Name) (args : List TypArg)
  | var (k : KId)
  | true
  | false
  deriving Repr

end

inductive QuantItem
  | kindedId (k : KindedId)
  | nConstraint (n : NConstraint)
  deriving Repr

def TypQuant := List QuantItem
  deriving Repr

structure Typschm where
  quants : TypQuant
  typ : Typ
  deriving Repr

import Std.Data.HashSet
import Mathlib.Tactic.DeriveToExpr

namespace Sail.AST

/-!
# The AST for Sail
-/

inductive Id where
  | ident (i : Lean.Name)
  | bool
  | bit
  | unit
  | nat
  | string
  | range
  | atom
  | vector
  | list
  | reg
  | toNum
  | toVec
  | msb
  deriving Lean.ToExpr, Repr

def KId := Lean.Name
  deriving Lean.ToExpr, Repr

inductive BaseKind where
  | type
  | nat
  | order
  | effect
  deriving Inhabited, Lean.ToExpr, Repr

structure Kind where
  args : List BaseKind
  kind : BaseKind
  deriving Lean.ToExpr, Repr

inductive NExp where
  | ident (i : Lean.Name)
  | kId (k : KId)
  | num (n : Nat)
  | mul (m n : NExp)
  | add (m n : NExp)
  | sub (m n : NExp)
  | exponential (n : NExp)
  deriving Lean.ToExpr, Repr

inductive Order where
  | kId (k : KId)
  | dec
  | inc
  deriving Lean.ToExpr, Repr

inductive BaseEffect where
  | rreg
  | wreg
  | rmem
  | wmem
  | wmea
  | wmv
  | barr
  | depend
  | undef
  | unspec
  | nondet
  | escape
  | lset
  | lret
  deriving BEq, Hashable, Lean.ToExpr, Repr

inductive Effect where
  | kId (k : KId)
  | set (bs : Std.HashSet BaseEffect)
  | pure  -- TODO maybe macro this away
  | union (es : List Effect)  -- TODO maybe macro this away
  deriving Repr

mutual

inductive Typ where
  | unspecified
  | id (i : Id)
  | kId (k : KId)
  | function (dom cod : Typ) (effect : Effect)
  | tuple (ts : List Typ)
  | tconstructor (i : Id) (args : List TypArg)
  deriving Repr

inductive TypArg where
  | nexp (n : NExp)
  | typ (t : Typ)
  | order (o : Order)
  | effect (e : Effect)
  deriving Repr

end

inductive NConstraint
  | eq (m n : NExp)
  | le (m n : NExp)
  | ge (m n : NExp)
  | in (k : KId) (ns : Std.HashSet Nat)
  deriving Repr

inductive KindedId
  | kId (k : KId)
  | annotated (k : Kind) (k' : KId)
  deriving Repr

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

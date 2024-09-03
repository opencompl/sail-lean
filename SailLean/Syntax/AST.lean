import Std.Data.HashSet

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

def KId := Lean.Name

inductive BaseKind where
  | type
  | nat
  | order
  | effect
  deriving Inhabited

structure Kind where
  args : List BaseKind
  kind : BaseKind

inductive NExp where
  | ident (i : Lean.Name)
  | kId (k : KId)
  | num (n : Nat)
  | mul (m n : NExp)
  | add (m n : NExp)
  | sub (m n : NExp)
  | exponential (n : NExp)

inductive Order where
  | kId (k : KId)
  | dec
  | inc

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
  deriving BEq, Hashable

inductive Effect where
  | kId (k : KId)
  | set (bs : Std.HashSet BaseEffect)
  | pure  -- TODO maybe macro this away
  | union (es : List Effect)  -- TODO maybe macro this away

mutual

inductive Typ where
  | unspecified
  | id (i : Id)
  | kId (k : KId)
  | function (dom cod : Typ) (effect : Effect)
  | tuple (ts : List Typ)
  | tconstructor (i : Id) (args : List TypArg)

inductive TypArg where
  | nexp (n : NExp)
  | typ (t : Typ)
  | order (o : Order)
  | effect (e : Effect)

end

inductive NConstraint
  | eq (m n : NExp)
  | le (m n : NExp)
  | ge (m n : NExp)
  | in (k : KId) (ns : Std.HashSet Nat)

inductive KindedId
  | kId (k : KId)
  | annotated (k : Kind) (k' : KId)

inductive QuantItem
  | kindedId (k : KindedId)
  | nConstraint (n : NConstraint)

def TypQuant := List QuantItem

structure Typschm where
  quants : TypQuant
  typ : Typ

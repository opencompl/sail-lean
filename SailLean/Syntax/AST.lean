import Std.Data.HashSet
import Mathlib.Tactic.DeriveToExpr

namespace Sail.AST

/-!
# The AST for Sail
-/

inductive Id where
  | ident (i : String)
  | operator (i : String)
  deriving Lean.ToExpr, Repr, BEq, Hashable

def KId := String
  deriving Lean.ToExpr, Repr, Inhabited, BEq

inductive Kind where
  | type
  | int
  | bool
  deriving Inhabited, Lean.ToExpr, Repr, DecidableEq

inductive KindedId
  | kId (k : KId)
  | annotated (k : Kind) (k' : KId)
  deriving Repr, BEq

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
  | var (k : KId)
  | fn (args : Typ) (dom : Typ)
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
  | app (i : Id) (args : List TypArg)
  | var (k : KId)
  | true
  | false
  deriving Repr, BEq

end

inductive QuantItem
  | kindedId (k : KindedId)
  | nConstraint (n : NConstraint)
  deriving Repr, BEq

def TypQuant := List QuantItem
  deriving Repr

structure Typschm where
  quants : TypQuant
  typ : Typ
  deriving Repr

inductive Lit where
  | unit
  | zero
  | one
  | true
  | false
  | num
  | string
  | undefined
  | real

inductive Loop where
  | while
  | until

inductive TypPat where
  | wild
  | var (k : KId)
  | app (i : Id) (ps : List TypPat)

inductive Pat where
  | lit (l : Lit)
  | wild
  | or (p₁ p₂ : Pat)
  | not (p : Pat)
  | as (p : Pat) (i : Id)
  | typ (t : Typ) (p : Pat)
  | var (p : Pat) (tp : TypPat)
  | app (i : Id) (ps : List Pat)
  | vector (ps : List Pat)
  | vectorConcat (ps : List Pat)
  | vectorSubrange (i : Id) (n₁ n₂ : Nat)
  | tuple (ps : List Pat)
  | list (ps : List Pat)
  | cons (p₁ p₂ : Pat)
  | stringAppend (ps : List Pat)
  | struct (fps : List (Id × Pat))

mutual

inductive InternalLoopMeasure where
  | none
  | some (e : Exp)

inductive Exp where
  | block (es : List Exp)
  | id (i : Id)
  | lit (l : Lit)
  | typ (t : Typ) (e : Exp)
  | app (i : Id) (es : List Exp)
  | appInfix (e : Exp) (i : Id) (e' : Exp)
  | tuple (es : List Exp)
  | if (c t e : Exp)
  | loop (l : Loop) (i : InternalLoopMeasure)
  | for (i : Id) (f t b : Exp) (o : Order)
  | vector (es : List Exp)
  | vectorAccess (e e' : Exp)
  | vectorSubrange (e e₁ e₂ : Exp)
  | vectorUpdate (e e₁ e₂ : Exp)
  | vectorUPdateSubrange (e e₁ e₂ e₃ : Exp)
  | vectorAppend (e₁ e₂ : Exp)
  | list (es : List Exp)
  | cons (e₁ e₂ : Exp)
  | struct (fs : FExp)
  | structUpdate (e : Exp) (fs : FExp)
  | field (e : Exp) (i : Id)
  | match (e : Exp) (ps : PExp)
  | let (e : Exp)  --- TODO ???
  | assign (l : LExp) (e : Exp)
  | sizeof (n : NExp)
  | return (e : Exp)
  | exit (e : Exp)
  | ref (i : Id)
  | try (e : Exp) (ps : PExp)
  | assert (e e' : Exp)

inductive FExp where
  | fexp (i : Id) (e : Exp)

inductive PExp where
  | exp (p : Pat) (e : Exp)
  | when (p : Pat) (e₁ e : Exp)

inductive LExp where
  | id (i : Id)
  | deref (e : Exp)
  | app (i : Id) (es : List Exp)
  | typ (t : Typ) (i : Id)
  | tuple (ls : List LExp)
  | vectorConcat (ls : List LExp)
  | vector (l : LExp) (e : Exp)
  | vectorRange (l : LExp) (es : List Exp)
  | field (l : LExp) (e : Id)

end

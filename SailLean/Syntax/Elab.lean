import SailLean.Syntax.AST
import SailLean.Syntax.Parsers
import Batteries.Lean.HashSet

/-!
# Elaborating the embedded Sail syntax into the AST datatypes

-/

open Lean

namespace Sail

def elabId : TSyntax `id → Except String AST.Id
  | `(id| $i:ident) => .ok <| .ident i.getId.getRoot.toString
  | `(id| (operator $i)) => .ok <| .operator i.getId.getRoot.toString
  | _ => .error "failed to elab id"

def elabKId : TSyntax `Sail.kid → Except String AST.KId
  | `(kid| @$i:ident) => .ok i.getId
  | _ => .error "failed to elab kid"

def elabKind : TSyntax `kind → Except String AST.Kind
  | `(kind| Type) => .ok .type
  | `(kind| Int) => .ok .int
  | `(kind| Bool) => .ok .bool
  | _ => .error "failed to elab base_kind"

def elabOrder : TSyntax `order → Except String AST.Order
  | `(order| inc) => .ok .inc
  | `(order| dec) => .ok .dec
  | _ => .error "failed to elab order"

def elabKindedId : TSyntax `kinded_id → Except String AST.KindedId
  | `(kinded_id| $k:kid) => .kId <$> elabKId k
  | `(kinded_id| $k:kind $i:kid) => .annotated <$> elabKind k <*> elabKId i
  | _ => .error "failed to elab kinded_id"

mutual

partial def elabNExp : TSyntax `nexp → Except String AST.NExp
  | `(nexp| $i:id) => .id <$> elabId i
  | `(nexp| $k:kid) => .var <$> elabKId k
  | `(nexp| $n:num) => .ok <| .constant n.getNat
  | `(nexp| $i:id ( $ns,* )) => do
      let ns ← ns.getElems.mapM elabNExp
      let i ← elabId i
      .ok <| .app i ns.toList
  | `(nexp| if $c:n_constraint then $t:nexp else $e:nexp) =>
    .ifThenElse <$> elabNConstraint c <*> elabNExp t <*> elabNExp e
  | `(nexp| $m * $n) => .product <$> elabNExp m <*> elabNExp n
  | `(nexp| $m + $n) => .sum <$> elabNExp m <*> elabNExp n
  | `(nexp| $m - $n) => .subtraction <$> elabNExp m <*> elabNExp n
  | `(nexp| 2^ $n) => .exponential <$> elabNExp n
  | `(nexp| - $n) => .neg <$> elabNExp n
  | _ => .error "failed to elab nexp"

partial def elabTyp : TSyntax `typ → Except String AST.Typ
  | `(typ| $k:kid) => .var <$> (elabKId k)
  | `(typ| ( $as:typ,* ) -> $t:typ ) => do
      let as ← as.getElems.mapM elabTyp
      let t ← elabTyp t
      .ok <| .fn as.toList t
  | `(typ| $t:typ <-> $s:typ) => .bidir <$> elabTyp t <*> elabTyp s
  | `(typ| ($ts:typ,*)) => do
      let ts ← ts.getElems.mapM elabTyp
      .ok <| .tuple ts.toList
  | `(typ| $i:id $[( $as:typ_arg,* )]?) => do
      let i ← elabId i
      let as : TSyntaxArray `typ_arg := match as with
        | .some as => as.getElems
        | .none => #[]
      let as ← as.mapM elabTypArg
      .ok <| .app i as.toList
  | `(typ| { $is:kinded_id* , $c:n_constraint . $t:typ }) => do
      let is ← is.mapM elabKindedId
      let c ← elabNConstraint c
      let t ← elabTyp t
      .ok <| .exist is.toList c t
  | _ => .error "failed to elab typ"

partial def elabTypArg : TSyntax `typ_arg → Except String AST.TypArg
  /-| `(typ_arg| $n:nexp) => .nexp <$> elabNExp n
  | `(typ_arg| $t:typ) => .typ <$> elabTyp t-/
  | `(typ_arg| $c:n_constraint) => .bool <$> elabNConstraint c
  | _ => .error "failed to elab typ_arlkg"

partial def elabNConstraint : TSyntax `n_constraint → Except String AST.NConstraint
  | `(n_constraint| $t:typ_arg == $s:typ_arg) => .equal <$> elabTypArg t <*> elabTypArg s
  | `(n_constraint| $t:typ_arg != $s:typ_arg) => .not_equal <$> elabTypArg t <*> elabTypArg s
  /-| `(n_constraint| $m:nexp >= $n:nexp) => _
  | `(n_constraint| $m:nexp > $n:nexp) => _
  | `(n_constraint| $m:nexp <= $n:nexp) => _
  | `(n_constraint| $m:nexp < $n:nexp) => _
  | `(n_constraint| $k:kid IN { $ns,* }) => do
      let ns := ns.getElems.map (·.getNat)
      let k ← elabKId k
      .ok <| .set k (Std.HashSet.ofArray ns)
  | `(n_constraint| $c:n_constraint & $d:n_constraint) =>
      .and <$> elabNConstraint c <*> elabNConstraint d
  | `(n_constraint| $c:n_constraint | $d:n_constraint) =>
      .or <$> elabNConstraint c <*> elabNConstraint d
  | `(n_constraint| $i:id ( $as:typ_arg,* )) => do
      let i ← elabId i
      let as ← as.getElems.mapM elabTypArg
      .ok <| .app i as.toList
  | `(n_constraint| $i:id) => .app <$> elabId i <*> .ok []
  | `(n_constraint| $k:kid) => .var <$> elabKId k
  | `(n_constraint| true) => .ok .true
  | `(n_constraint| false) => .ok .false-/
  | _ => .error "failed to elab n_constraint"

end

def elabQuantItem : TSyntax `quant_item → Except String AST.QuantItem
  /-| `(quant_item| $k:kinded_id) => .kindedId <$> elabKindedId k-/
  | `(quant_item| $n:n_constraint) => .nConstraint <$> elabNConstraint n
  | _ => .error "failed to elab quant_item"

def elabTypQuant : TSyntax `typquant → Except String AST.TypQuant
  | `(typquant| forall $qs:quant_item,* .) => do
      let qs ← qs.getElems.mapM elabQuantItem
      .ok qs.toList
  | _ => .error "failed to elab typquant"

def elabTypschm : TSyntax `typschm → Except String AST.Typschm
  | `(typschm| $tq:typquant $t:typ) => do
      let tq ← elabTypQuant tq
      let t ← elabTyp t
      .ok { quants := tq, typ := t }
  | _  => .error "failed to elab typschm"

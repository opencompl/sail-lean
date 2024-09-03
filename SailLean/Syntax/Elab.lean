import SailLean.Syntax.AST
import SailLean.Syntax.Parsers
import Batteries.Lean.HashSet

/-!
# Elaborating the embedded Sail syntax into the AST datatypes

-/

open Lean

namespace Sail

def elabId : TSyntax `id → Except String AST.Id
  | `(id| bool) => .ok .bool
  | `(id| bit) => .ok .bit
  | `(id| unit) => .ok .unit
  | `(id| nat) => .ok .nat
  | `(id| string) => .ok .string
  | `(id| range) => .ok .range
  | `(id| atom) => .ok .atom
  | `(id| vector) => .ok .vector
  | `(id| list) => .ok .list
  | `(id| reg) => .ok .reg
  | `(id| to_num) => .ok .toNum
  | `(id| to_vec) => .ok .toVec
  | `(id| msb) => .ok .msb
  | `(id| $i:ident) => .ok <| .ident i.getId
  | _ => .error "failed to elab id"

def elabKId : TSyntax `kid → Except String AST.KId
  | `(kid| @$i:ident) => .ok i.getId
  | _ => .error "failed to elab kid"

def elabBaseKind : TSyntax `base_kind → Except String AST.BaseKind
  | `(base_kind| Type) => .ok .type
  | `(base_kind| Nat) => .ok .nat
  | `(base_kind| Order) => .ok .order
  | `(base_kind| Effect) => .ok .effect
  | _ => .error "failed to elab base_kind"

def elabKind : TSyntax `kind → Except String AST.Kind
  | `(kind| $a:base_kind -> $[$as:base_kind]->*) => do
      let bs ← (#[a].append as).mapM elabBaseKind
      .ok { args := bs.pop.toList, kind := bs.back }
  | _ => .error "failed to elab kind"

partial def elabNExp : TSyntax `nexp → Except String AST.NExp
  | `(nexp| $i:ident) => .ok <| .ident i.getId
  | `(nexp| $k:kid) => .kId <$> (elabKId k)
  | `(nexp| $n:num) => .ok <| .num n.getNat
  | `(nexp| $m * $n) => .mul <$> (elabNExp m) <*> (elabNExp n)
  | `(nexp| $m + $n) => .add <$> (elabNExp m) <*> (elabNExp n)
  | `(nexp| $m - $n) => .sub <$> (elabNExp m) <*> (elabNExp n)
  | `(nexp| 2** $n) => .exponential <$> (elabNExp n)
  | _ => .error "failed to elab nexp"

def elabOrder : TSyntax `order → Except String AST.Order
  | `(order| $k:kid) => .kId <$> (elabKId k)
  | `(order| inc) => .ok .inc
  | `(order| dec) => .ok .dec
  | _ => .error "failed to elab order"

def elabBaseEffect : TSyntax `base_effect → Except String AST.BaseEffect
  | `(base_effect| rreg) => .ok .rreg
  | `(base_effect| wreg) => .ok .wreg
  | `(base_effect| rmem) => .ok .rmem
  | `(base_effect| wmem) => .ok .wmem
  | `(base_effect| wmea) => .ok .wmea
  | `(base_effect| wmv) => .ok .wmv
  | `(base_effect| barr) => .ok .barr
  | `(base_effect| depend) => .ok .depend
  | `(base_effect| undef) => .ok .undef
  | `(base_effect| unspec) => .ok .unspec
  | `(base_effect| nondet) => .ok .nondet
  | `(base_effect| escape) => .ok .escape
  | `(base_effect| lset) => .ok .lset
  | `(base_effect| lret) => .ok .lret
  | _ => .error "failed to elab base_effect"

partial def elabEffect : TSyntax `effect' → Except String AST.Effect
  | `(effect'| $k:kid) => .kId <$> elabKId k
  | `(effect'| { $bs:base_effect,* }) => do
      let bs ← bs.getElems.mapM elabBaseEffect
      .ok <| .set <| Std.HashSet.ofArray bs
  | `(effect'| pure) => .ok .pure
  | _ => .error "failed to elab effect"

mutual

partial def elabTyp : TSyntax `typ → Except String AST.Typ
  | `(typ| _) => .ok .unspecified
  | `(typ| $i:id) => .id <$> (elabId i)
  | `(typ| $k:kid) => .kId <$> (elabKId k)
  --| `(typ| $cod:typ -> $dom:typ effect $e:effect) => _  produces stack overflows
  | `(typ| ($ts:typ,*)) => do
      let ts ← ts.getElems.mapM elabTyp
      .ok <| .tuple ts.toList
  | `(typ| $i:id<$tas:typ_arg,*>) => do
      let tas ← tas.getElems.mapM elabTypArg
      let i ← elabId i
      .ok <| .tconstructor i tas.toList
  | _ => .error "failed to elab typ"

partial def elabTypArg : TSyntax `typ_arg → Except String AST.TypArg
  | `(typ_arg| $n:nexp) => .nexp <$> elabNExp n
  | `(typ_arg| $t:typ) => .typ <$> elabTyp t
  | `(typ_arg| $o:order) => .order <$> elabOrder o
  | `(typ_arg| $e:effect') => .effect <$> elabEffect e
  | _ => .error "failt to elab typ_arg"

end

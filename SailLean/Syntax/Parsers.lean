import SailLean.Syntax.Cats
import Lean

/-!
# Declaring the Sail syntax
-/

open Lean Meta Parser Elab Command
namespace Sail

/- `id` (identifier) -/

syntax ident : id
syntax "bool" : id
syntax "bit" : id
syntax "unit" : id
syntax "nat" : id
syntax "string" : id
syntax "range" : id
syntax "atom" : id
syntax "vector" : id
syntax "list" : id
syntax "reg" : id
syntax "to_num" : id
syntax "to_vec" : id
syntax "msb" : id

syntax "`[id|" id "]" : term

/- `kid` (kinded IDs) -/

def singleSingleQuote : Parser := rawCh '@'  -- TODO exchange `@` for a `'` or work around

def singleSingleQuote' :=
{ singleSingleQuote with info := { collectKinds := fun s => s.insert `cat1
                                   collectTokens := fun ts => ts ++ ["'"]
                                   firstTokens := .tokens ["'"] } }

@[combinator_formatter singleSingleQuote]
def singleSingleQuote.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer singleSingleQuote]
def singleSingleQuote.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

syntax kid := singleSingleQuote noWs ident

/-declare_syntax_cat cat1
syntax (singleSingleQuote)? ident : cat1

syntax "`[cat1|" cat1 "]" : term

#eval `[cat1|'foo]

#check PrettyPrinter.Formatter.parseToken

#exit-/

/- `base_kind` -/

syntax "Type" : base_kind
syntax "Nat" : base_kind
syntax "Order" : base_kind
syntax "Effect" : base_kind

syntax "`[base_kind|" base_kind "]" : term

/- `kind` -/

syntax sepBy1(base_kind, "->") : kind

syntax "`[kind|" kind "]" : term

/- `nexp` (numeric expression, of kind `Nat`)-/

syntax ident : nexp  -- abbreviation identifier
syntax kid : nexp  -- variable
syntax num : nexp  -- constant
syntax nexp "*" nexp : nexp
syntax nexp "+" nexp : nexp
syntax nexp "-" nexp : nexp
syntax num noWs "**" nexp : nexp  -- TODO `num` must be `2`  -- exponential
syntax "(" nexp ")" : nexp

macro_rules | `(nexp|($x)) => `(nexp|$x)

syntax "`[nexp|" nexp "]" : term

/- `order` (vector order specifications, of kind `Order`)-/

syntax kid : order
syntax "inc" : order
syntax "dec" : order
syntax "(" order ")" : order

macro_rules | `(order|($x)) => `(order|$x)

syntax "`[order|" order "]" : term

/- `base_effect` -/

syntax "rreg" : base_effect
syntax "wreg" : base_effect
syntax "rmem" : base_effect
syntax "wmem" : base_effect
syntax "wmea" : base_effect
syntax "wmv" : base_effect
syntax "barr" : base_effect
syntax "depend" : base_effect
syntax "undef" : base_effect
syntax "unspec" : base_effect
syntax "nondet" : base_effect
syntax "escape" : base_effect
syntax "lset" : base_effect
syntax "lret" : base_effect

/- `effect` (effect set, of kind `Effect`)-/

syntax kid : effect'
syntax "{" base_effect,* "}" : effect'
syntax "pure" : effect'
-- syntax sepBy1(effect, "⊎") : effect  -- TODO problematic, turned off for now

syntax "`[effect|" effect' "]" : term

/- `typ` (type expressions, of kind `Type`)-/

syntax "_" : typ  -- unspecified type
syntax id : typ  -- specified type
syntax kid : typ  -- type variable
syntax typ "->" typ "effect" effect' : typ  -- function
syntax "(" typ,* ")" : typ  -- tuple
syntax id "<" typ_arg,* ">" : typ  -- type constructor application
syntax "(" typ ")" : typ
syntax "[|" nexp "|]" : typ
syntax "[|" nexp ":" nexp "|]" : typ
syntax "[:" nexp ":]" : typ

syntax "`[typ|" typ "]" : term

/- `typ_arg` (type constructor arguments of all kinds) -/
syntax nexp : typ_arg
syntax typ : typ_arg
syntax order : typ_arg
syntax effect' : typ_arg  -- ???

syntax "`[typ_arg|" typ_arg "]" : term

/- `n_constraint` (constraint over kind `Nat`) -/

syntax nexp "=" nexp : n_constraint
syntax nexp ">=" nexp : n_constraint
syntax nexp "<=" nexp : n_constraint
syntax kid "IN" "{" num,* "}" : n_constraint

syntax "`[n_constraint|" n_constraint "]" : term

/- `kinded_id` (optionally kind-annotated identifier) -/

syntax kid : kinded_id  -- identifier
syntax kind kid : kinded_id  -- kind-annotated variable

syntax "`[kinded_id|" kinded_id "]" : term

/- `quant_item` (kinded identifier or `Nat` constraint) -/

syntax kinded_id : quant_item
syntax n_constraint : quant_item

syntax "`[quant_item|" quant_item "]" : term

/- `typquant` (type quantifiers and constraints) -/

syntax "forall" quant_item,* "." : typquant

syntax "`[typquant|" typquant "]" : term

/- `typschm` (type scheme) -/

syntax typquant typ : typschm

syntax "`[typschm|" typschm "]" : typschm


/- Additional syntax sugar -/

macro_rules
  --| `(typ|($t:typ)) => `(typ|$t)  -- ???
  | `(typ|[|$n|]) => `(typ|range<0, $n:nexp>)
  | `(typ|[|$n : $n'|]) => `(typ|range<$n:nexp, $n':nexp>)
  | `(typ|[: $n :]) => `(typ|atom<$n:nexp>)
-- TODO vector syntax sugar

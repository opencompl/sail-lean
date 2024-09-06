import SailLean.Syntax.Cats
import Lean

/-!
# Declaring the Sail syntax
-/

open Lean Meta Parser Elab Command
namespace Sail

/- `id` (identifier) -/

syntax ident : id
syntax "(" "operator" ident ")" : id

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

/- `kind` -/

syntax "Type" : kind
syntax "Int" : kind
syntax "Bool" : kind

syntax "`[kind|" kind "]" : term

/- `nexp` (numeric expression, of kind `Nat`)-/

syntax id : nexp  -- abbreviation identifier
syntax kid : nexp  -- variable
syntax num : nexp  -- constant
syntax id "(" nexp,* ")" : nexp  -- app
syntax "if" n_constraint "then" nexp "else" nexp : nexp  -- if-then-else
syntax nexp "*" nexp : nexp  -- product
syntax nexp "+" nexp : nexp  -- sum
syntax nexp "-" nexp : nexp  -- subtraction
syntax num noWs "^" nexp : nexp  -- exponential TODO `num` must be `2`  -- exponential
syntax "-" nexp : nexp  -- unary negation
syntax "(" nexp ")" : nexp

macro_rules | `(nexp|($x)) => `(nexp|$x)

syntax "`[nexp|" nexp "]" : term

/- `order` (vector order specifications, of kind `Order`)-/

syntax "inc" : order
syntax "dec" : order
syntax "(" order ")" : order

macro_rules | `(order|($x)) => `(order|$x)

syntax "`[order|" order "]" : term

/- `typ` (type expressions, of kind `Type`)-/

-- TODO deal with unknown types
syntax id : typ  -- defined type
syntax kid : typ  -- type variable
syntax typ "->" typ : typ -- function
syntax "(" typ,* ")" : typ  -- tuple
syntax typ "->" typ : typ
syntax typ "<->" typ : typ  -- mapping
syntax id noWs ("(" typ_arg,* ")")? : typ  -- type constructor application
syntax "{" kinded_id* "," n_constraint "." typ "}" : typ  -- exist

syntax "`[typ|" typ "]" : term

/- `typ_arg` (type constructor arguments of all kinds) -/
syntax nexp : typ_arg
--syntax typ : typ_arg
--syntax n_constraint : typ_arg

syntax "`[typ_arg|" typ_arg "]" : term

/- `n_constraint` (constraint over kind `Nat`) -/

syntax typ_arg "==" typ_arg : n_constraint
syntax typ_arg "!=" typ_arg : n_constraint
syntax nexp ">=" nexp : n_constraint
syntax nexp ">" nexp : n_constraint
syntax nexp "<=" nexp : n_constraint
syntax nexp "<" nexp : n_constraint
syntax nexp "IN" "{" num,* "}" : n_constraint
syntax n_constraint "&" n_constraint : n_constraint
syntax n_constraint "|" n_constraint : n_constraint
syntax id "(" typ_arg,* ")" : n_constraint
syntax id : n_constraint
syntax kid : n_constraint
syntax "true" : n_constraint
syntax "false" : n_constraint

syntax "`[n_constraint|" n_constraint "]" : term

/- `kinded_id` (optionally kind-annotated identifier) -/

syntax kind kid : kinded_id  -- kind-annotated variable
syntax kid : kinded_id  -- identifier

syntax "`[kinded_id|" kinded_id "]" : term

/- `quant_item` (kinded identifier or `Nat` constraint) -/

syntax kinded_id : quant_item
syntax n_constraint : quant_item

syntax "`[quant_item|" quant_item "]" : term

/- `typquant` (type quantifiers and constraints) -/

-- TODO can be `epsilon`
syntax "forall" quant_item,* "." : typquant

syntax "`[typquant|" typquant "]" : term

/- `typschm` (type scheme) -/

syntax (typquant)? typ : typschm

syntax "`[typschm|" typschm "]" : typschm

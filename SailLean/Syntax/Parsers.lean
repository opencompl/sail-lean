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
syntax typ : typ_arg
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

/- `type_def` (type definition body) -/

syntax "type" id typquant "=" typ_arg : type_def  -- type abbreviation
syntax "typedef" id "=" "const" "struct" typquant "{" sepBy1((typ id), ";", ";", allowTrailingSep) "}" : type_def  -- struct type definition
syntax "typedef" id "=" "const" "union" typquant "{" sepBy1((typ id), ";", ";", allowTrailingSep) "}" : type_def  -- taged union type definition
syntax "typedef" id "=" "enumerate" "{" sepBy1((typ id), ";", ";", allowTrailingSep) "}" : type_def  -- enumeration type definition
syntax "typedef" id ":" kind : type_def  -- abstract type
syntax "bitfield" id ":" typ "=" "{" (id ":" index_range),* "}" : type_def  -- register mutable bitfield type definition

syntax "`[type_def|" type_def "]" : term

/- `type_union` (type union constructors) -/

syntax typ id : type_union

syntax "`[type_union|" type_union "]" : term

/- `index_range` (index specification, for bitfields in register types) -/

syntax nexp : index_range  -- single index
syntax nexp ".." nexp : index_range  -- index range
syntax index_range "," index_range : index_range  -- concatenation of index ranges

syntax "`[index_range|" index_range "]" : term

/- `lit` (literal constant) -/

syntax "()" : lit  -- unit
syntax "bitzero" : lit  -- zero
syntax "bitone" : lit  -- one
syntax "true" : lit  -- true
syntax "false" : lit  -- false
syntax num : lit  -- natural number constant
syntax str : lit  -- string constant
syntax "undefined" : lit  -- undefined-value constant
syntax "real" : lit  -- real

syntax "`[lit|" lit "]" : term

/- `typ_pat` (type pattern) -/

syntax "_" : typ_pat
syntax kid : typ_pat
syntax id "(" typ_pat,* ")" : typ_pat

syntax "`[typ_pat|" typ_pat "]" : term

/- `pat` (pattern) -/

syntax lit : pat  -- literal constant pattern
syntax "_" : pat  -- wildcard
syntax pat "|" pat : pat  -- pattern disjunction
syntax "~" pat : pat  -- pattern negation
syntax "(" pat "as" id ")" : pat  -- named pattern
syntax "(" typ ")" pat : pat  -- typed pattern
syntax id : pat  -- identifier
syntax pat typ_pat : pat  -- bind pattern to type variable
syntax id "(" pat,* ")" : pat  -- union constructor pattern
syntax "[" pat,* "]" : pat  -- vector pattern
syntax sepBy1(pat, "@") : pat  -- concatenated vector pattern
syntax "[" num ".." num "]" : pat  -- vector subrange pattern
syntax "(" pat,* ")" : pat  -- tuple pattern
syntax "[|" pat,* "|]" : pat  -- list pattern
syntax pat "::" pat : pat  -- Cons pattern
syntax sepBy1(pat, "^^") : pat  -- string append pattern, x ^^ y
syntax "struct" "{" sepBy1(id "=" pat, ",", ",", allowTrailingSep) "}" : pat  -- struct pattern

syntax "`[pat|" pat "]" : term

/- `loop` -/

syntax "while" : loop
syntax "until" : loop

syntax "`[loop|" loop "]" : term

/- `internal_loop_measure` (internal syntax for an optional termination measure for a loop) -/

syntax "termination_measure" "{" exp "}" : internal_loop_measure

syntax "`[internal_loop_measure|" internal_loop_measure "]" : term

/- `exp` (expression) -/

syntax "{" sepBy1(exp, ";") "}" : exp  -- sequential block
syntax id : exp  -- identifier
syntax lit : exp  -- literal constant
syntax "(" typ ")" exp : exp  -- cast
syntax exp id exp : exp  -- infix function application
syntax "(" exp,* ")" : exp  -- tuple
syntax "if" exp "then" exp "else" exp : exp  -- conditional
syntax loop internal_loop_measure exp exp : exp  -- loop
syntax "foreach" "(" id "from" exp "to" exp "by" exp "in" order ")" exp : exp  -- for loop

syntax "[" exp,* "]" : exp  -- vector (indexed from 0)
syntax exp "[" exp "]" : exp  -- vector access
syntax exp "[" exp ".." exp "]" : exp  -- subvector extraction
syntax "[" exp "with" exp "=" exp "]" : exp  -- vector functional update
syntax "[" exp "with" exp ".." exp "=" exp "]" : exp  -- vector subrange update, with vector
syntax exp "@" exp : exp  -- vector concatenation

syntax "[|" exp,* "|]" : exp  -- list
syntax exp "::" exp : exp  -- cons

syntax "struct" "{" fexp,* "}" : exp  -- struct
syntax "{" exp "with" fexp,* "}" : exp  -- functional update of struct
syntax exp "." id : exp  -- field projection from struct

syntax "match" exp "{" pexp,* "}" : exp  -- pattern matching

syntax "letbind" "in" exp : exp  -- let expression

syntax lexp "=" exp : exp  -- imperative assignment

syntax "sizeof" nexp : exp  -- the value of `nexp` at run time

syntax "return" exp : exp  -- return `exp` from current function
syntax "exit" exp : exp  -- halt all current execution
syntax "ref" id : exp
syntax "throw" exp : exp
syntax "try" exp "catch" "{" pexp,* "}" : exp
syntax "assert" "(" exp "," exp ")" : exp  -- halt with error message when not `exp`
syntax "(" exp ")" : exp
syntax "constraint" n_constraint : exp

syntax "`[exp|" exp "]" :term

/- `lexp` (lvalue expression) -/

syntax id : lexp  -- identifier
syntax "deref" exp : lexp
syntax id "(" exp,* ")" : lexp  -- memory or register write via function call
syntax "(" typ ")" id : lexp
syntax "(" lexp,* ")" : lexp  -- multiple (non-memory) assignments
syntax sepBy1(lexp, "@") : lexp  -- vector concatenation L-exp
syntax lexp "[" exp "]" : lexp  -- vector element
syntax lexp "[" exp ".." exp "]" : lexp  -- subvector
syntax lexp "." id : lexp  -- struct field

syntax "`[lexp|" lexp "]" : term

/- `fexp` (field expression) -/

syntax id "=" exp : fexp

syntax "`[fexp|" fexp "]" : term

/- `pexp` (pattern match) -/

syntax pat "=>" exp : pexp
syntax pat "if" exp "=>" exp : pexp

syntax "`[pexp|" pexp "]" : term

import SailLean.Syntax.Cats

/-!
# Declaring the Sail syntax
-/

open Lean.Parser
namespace Sail

/- `operator` -/

syntax "!" : operator
syntax "%" : operator
syntax "&" : operator
syntax "*" : operator
syntax "+" : operator
syntax "." : operator
syntax "/" : operator
syntax ":" : operator
syntax "<" : operator
syntax ">" : operator
syntax "=" : operator
syntax "@" : operator
syntax operator noWs "_" noWs ident : operator
-- TODO

syntax "`[operator|" operator "]" : term

/- `type_variable` -/
-- syntax "'" noWs ident : type_variable -- TODO add `'` to token list

syntax "`[type_variable|" type_variable "]" : term

/- `op` -/

syntax operator : op
-- TODO

syntax "`[op|" op "]" : term

/- `typ_var` -/

syntax typ_var := type_variable

/- `tyarg` -/

syntax tyarg := "(" typ,+ ")"

/- `prefix_typ_op` -/

-- syntax "2^" : prefix_typ_op -- TODO add `2^` to token list
syntax "-" : prefix_typ_op
syntax "*" : prefix_typ_op

syntax "`[prefix_typ_op|" prefix_typ_op "]" : term

/- `typ_no_caret` -/

syntax (prefix_typ_op)? atomic_typ (op_no_caret prefix_typ_op prefix_typ_op)* : typ_no_caret

syntax "`[typ_no_caret|" typ_no_caret "]" : term

/- `typ` -/

syntax "if" infix_typ "then" infix_typ "else" : typ
syntax infix_typ : typ

syntax "`[typ|" typ "]" : term

/- `infix_typ` -/

syntax (prefix_typ_op)? atomic_typ (op prefix_typ_op prefix_typ_op)* : infix_typ

syntax "`[infix_typ" infix_typ "]" : term

/- `atomic_typ` -/

syntax ident : atomic_typ
syntax "_" : atomic_typ
-- syntax typ_var : atomic_typ
syntax "dec" : atomic_typ
syntax "inc" : atomic_typ
-- syntax id tyarg : atomic_typ
syntax "register (" typ ")" : atomic_typ
syntax "(" typ,+ ")" : atomic_typ -- uh oh
syntax "{" num "}" : atomic_typ
-- syntax "{" kopt "." typ "}"
-- syntax "{" kopt "," typ "." typ "}"

syntax "`[atomic_typ|" atomic_typ "]" : term

/- `kind` -/

syntax "Int" : kind
syntax "Type" : kind
syntax "Order" : kind
syntax "Bool" : kind

syntax "`[kind|" kind "]" : term

/- `kopt` -/

syntax "(" "constant" typ_var ":" kind ")" : kopt

syntax "`[kopt|" kopt "]" : term


/- `typschm` -/

syntax ("forall" quantifier ".")? typ ("->" <|> "<->") typ : typschm

syntax "`[typschm|" typschm "]" : term

/- `lit` -/

syntax "true" : lit
syntax "false" : lit
syntax "()" : lit
syntax num : lit
syntax str : lit
syntax "undefined" : lit
syntax "bitzero" : lit
syntax "bitone" : lit

syntax "`[lit|" lit "]" : term

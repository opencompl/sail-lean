import SailLean.Syntax.Cats

/-!
# Declaring the Sail syntax
-/

open Lean.Parser
namespace Sail

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

syntax operator : op
-- TODO

syntax "`[op|" op "]" : term

syntax "true" : lit
syntax "false" : lit
-- TODO

syntax "`[lit|" lit "]" : term

syntax "if" infix_typ "then" infix_typ "else" : typ
syntax infix_typ : typ

syntax "`[typ|" typ "]" : term

syntax prefix_typ_op postfix_typ (op prefix_typ_op prefix_typ_op)* : infix_typ

syntax "`[infix_typ" infix_typ "]" : term

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

syntax "Int" : kind
syntax "Type" : kind
syntax "Order" : kind
syntax "Bool" : kind

syntax "`[kind|" kind "]" : term

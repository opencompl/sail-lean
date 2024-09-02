import Lean.Parser.Basic

/-!
# Declaration of syntax categories

As listed on the [Sail documentation](https://alasdair.github.io/manual.html#_the_sail_grammar).

Categories not needed from the Sail grammar:
* `typ_list` is `typ,+`
* `postfix_typ` is `atomic_typ`

# TODO
* add remaining syntax cats
* consider putting them in a dedicated namespace

-/

namespace Sail

declare_syntax_cat operator
declare_syntax_cat type_variable
declare_syntax_cat op_no_caret
declare_syntax_cat op
declare_syntax_cat lit
declare_syntax_cat prefix_typ_op
declare_syntax_cat postfix_typ
declare_syntax_cat typ_no_caret
declare_syntax_cat typ
declare_syntax_cat infix_typ
declare_syntax_cat atomic_typ
declare_syntax_cat kind
declare_syntax_cat kopt
declare_syntax_cat quantifier
declare_syntax_cat typschm

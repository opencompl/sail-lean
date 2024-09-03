import Lean.Parser.Basic

/-!
# Declaration of syntax categories

As listed on the [Sail documentation](https://alasdair.github.io/manual.html#_the_sail_grammar).

Categories not needed from the Sail grammar:
* `typ_list` is `typ,+`
* `postfix_typ` is `atomic_typ`
* `kid` will be defined as being `'` followed by an `ident`

# TODO
* add remaining syntax cats
* consider putting them in a dedicated namespace

-/

namespace Sail

declare_syntax_cat id
declare_syntax_cat base_kind
declare_syntax_cat kind
declare_syntax_cat nexp
declare_syntax_cat order
declare_syntax_cat base_effect
declare_syntax_cat effect'
declare_syntax_cat typ
declare_syntax_cat typ_arg
declare_syntax_cat n_constraint
declare_syntax_cat kinded_id
declare_syntax_cat quant_item
declare_syntax_cat typquant
declare_syntax_cat typschm

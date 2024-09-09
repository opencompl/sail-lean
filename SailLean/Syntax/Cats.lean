import Lean.Parser.Basic

/-!
# Declaration of syntax categories

As listed on the [Sail documentation](https://alasdair.github.io/manual.html#_the_sail_grammar).

Categories not needed from the Sail grammar:
* `typ_list` is `typ,+`
* `postfix_typ` is `atomic_typ`
* `kid` will be defined as being `'` followed by an `ident`
* `semi_opt` is just `(";")?`
* `type_def` and `type_def_aux` are merged

# TODO
* add remaining syntax cats
* consider putting them in a dedicated namespace

-/

namespace Sail

declare_syntax_cat id

/- Kinds and types -/

declare_syntax_cat kind
declare_syntax_cat nexp
declare_syntax_cat order
declare_syntax_cat typ
declare_syntax_cat typ_arg
declare_syntax_cat n_constraint
declare_syntax_cat kinded_id
declare_syntax_cat quant_item
declare_syntax_cat typquant
declare_syntax_cat typschm

/- Type definitions -/

declare_syntax_cat type_def
declare_syntax_cat type_union
declare_syntax_cat index_range

/- Literals -/

declare_syntax_cat lit

/- Patterns -/

declare_syntax_cat typ_pat
declare_syntax_cat pat

/- Expressions -/

declare_syntax_cat loop
declare_syntax_cat internal_loop_measure
declare_syntax_cat exp
declare_syntax_cat lexp
declare_syntax_cat fexp
declare_syntax_cat opt_default
declare_syntax_cat pexp

import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

package «SailLean» {
  -- add package configuration options here
}

@[default_target]
lean_lib «SailLean» {
  -- add library configuration options here
}

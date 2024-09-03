import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "main"

package «SailLean» {
  -- add package configuration options here
}

@[default_target]
lean_lib «SailLean» {
  -- add library configuration options here
}

import Lake
open Lake DSL

package ista {
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib ISTA {
  globs := #[.submodules `ISTA]
  moreLeanArgs := #["-DautoImplicit=false"]
}

import Lake
open Lake DSL

package asGinzburg where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

@[default_target]
lean_lib ASGinzburg

@[default_target]
lean_lib AxiomAudit

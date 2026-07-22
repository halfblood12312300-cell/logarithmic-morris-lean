import Lake

open Lake DSL

package logarithmicmorris where
  version := v!"1.0.0"
  keywords := #["combinatorics", "constant terms", "Lean", "Morris identity"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, 3⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

@[default_target]
lean_lib logarithmicmorris where
  globs := #[`logarithmicmorris, .submodules `logarithmicmorris]

lean_lib laurent where
  globs := #[`laurent, .submodules `laurent]

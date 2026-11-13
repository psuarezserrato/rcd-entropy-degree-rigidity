import Lake
open Lake DSL

package «RCDEntropyDegree» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.backward.isDefEq.respectTransparency, false⟩
  ]

require «BCG» from git
  "https://github.com/psuarezserrato/formalized-barycenter-methods.git" @ "main"

@[default_target]
lean_lib «RCDEntropyDegree» where
  -- Entropy-degree rigidity for closed orientable non-collapsed RCD(K, N) and Alexandrov spaces

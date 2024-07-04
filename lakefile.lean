import Lake
open Lake DSL

package «formal-web» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  , ⟨`relaxedAutoImplicit, false⟩
  , ⟨`pp.proofs, true⟩
  -- , ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  -- , ⟨`pp.proofs.withType, false⟩
  ]

lean_lib ES2023 where
  -- add library configuration options here

@[default_target]
lean_exe es2023 where
  root := `Main

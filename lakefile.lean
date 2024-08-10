import Lake
open Lake DSL

package «concreteSemantics» where
  -- add package configuration options here
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]

lean_lib «ConcreteSemantics» where
  -- add library configuration options here

@[default_target]
lean_exe «concretesemantics» where
  root := `Main

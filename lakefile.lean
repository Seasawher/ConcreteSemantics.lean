import Lake
open Lake DSL

package «concreteSemantics» where
  -- add package configuration options here
  leanOptions := #[
    -- autoImplicit は悪
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,

    -- ドキュメントコマンドを書くことを強制する
    ⟨`linter.missingDocs, true⟩,

    -- ラムダ式で `=>` の代わりに `↦` を使う
    ⟨`pp.unicode.fun, true⟩
  ]

require aesop from git "https://github.com/leanprover-community/aesop"

@[default_target]
lean_lib «ConcreteSemantics» where
  -- add library configuration options here
  globs := #[.submodules `ConcreteSemantics]

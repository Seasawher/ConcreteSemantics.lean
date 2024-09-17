import ConcreteSemantics.Stmt

/- ## 7.3 Small Step Semantics -/

/-- #### SmallStep 意味論
コマンドと状態の組 `Stmt × State` を二つ受け取る。(コマンドと状態の組のことは configuration と呼ぶ)
`SmallStep (c₁, s₁) (c₂, s₂)` は、コマンド `c₁` を初期状態 `s₁` から始めて実行して、
1ステップだけ進めると状態は `s₂` になって、残りの実行すべきコマンドが `c₂` であることを表す。

引数をカリー化しないと帰納法が上手くいかない恐れがあるので注意。
-/
inductive SmallStep : Stmt → State → Stmt → State → Prop
  /-- 代入文 `x := a s` の意味論 -/
  | assign {x a s} : SmallStep (assign x a) s skip (s[x ↦ a s])

  /-- seq の意味論 -/
  | seq_step {S S' T s s'} (hS : SmallStep S s S' s') :
    SmallStep (S ;; T) s (S' ;; T) s'

  /-- skip の意味論。skip を seq してもコマンドの意味は変わらない -/
  | seq_skip {T s} : SmallStep (skip ;; T) s T s


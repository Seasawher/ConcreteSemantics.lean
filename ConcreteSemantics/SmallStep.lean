import ConcreteSemantics.Stmt
import ConcreteSemantics.Tactic.SmallStep

/- ## 7.3 Small Step Semantics -/

/-- #### SmallStep 意味論
コマンドと状態の組 `Stmt × State` を二つ受け取る。(コマンドと状態の組のことは configuration と呼ぶ)
`SmallStep (c₁, s₁) (c₂, s₂)` は、コマンド `c₁` を初期状態 `s₁` から始めて実行して、
1ステップだけ進めると状態は `s₂` になって、残りの実行すべきコマンドが `c₂` であることを表す。

引数をカリー化しないと帰納法が上手くいかない恐れがあるので注意。
-/
inductive SmallStep : Stmt → State → Stmt → State → Prop
  /-- 代入文 `x := a s` の意味論 -/
  | protected assign {x a s} : SmallStep (assign x a) s skip (s[x ↦ a s])

  /-- seq の意味論 -/
  | protected seq_step {S S' T s s'} (hS : SmallStep S s S' s') :
    SmallStep (S ;; T) s (S' ;; T) s'

  /-- skip の意味論。skip を seq してもコマンドの意味は変わらない -/
  | protected seq_skip {T s} : SmallStep (skip ;; T) s T s

  /-- 条件式が true のときの if の意味論。状態は変化せず、実行するコマンドが変化する。-/
  | protected if_true {B S T s} (hcond : B s) :
    SmallStep (ifThenElse B S T) s S s

  /-- 条件式が false のときの if の意味論。状態は変化せず、実行するコマンドが変化する。-/
  | protected if_false {B S T s} (hcond : ¬ B s) :
    SmallStep (ifThenElse B S T) s T s

  /-- while の意味論。`whileDo B S` は、`B` が真なら `S ;; whileDo B S` に等しく、
  `B` が偽なら `skip` に等しい。-/
  | protected whileDo {B S s} :
    SmallStep (whileDo B S) s (ifThenElse B (S ;; whileDo B S) skip) s


-- `small_step` タクティクにコンストラクタを登録する
add_aesop_rules safe apply [
  SmallStep.assign,
  SmallStep.seq_skip,
  SmallStep.whileDo (rule_sets := [SmallStepRules])
]
add_aesop_rules unsafe 70% apply [
  SmallStep.seq_step (rule_sets := [SmallStepRules])
]
add_aesop_rules safe tactic [
  (by apply SmallStep.if_true (hcond := by assumption)),
  (by apply SmallStep.if_false (hcond := by assumption))
  (rule_sets := [SmallStepRules])
]

-- SmallStep のための見やすい記法を用意する
@[inherit_doc] notation:55 "(" c1:55 "," s1:55 ")" " =>ₛ " "(" c2:55 "," s2:55 ")" => SmallStep c1 s1 c2 s2

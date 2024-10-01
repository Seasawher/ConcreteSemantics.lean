import ConcreteSemantics.Stmt
import ConcreteSemantics.Tactic.SmallStep
import Mathlib.Logic.Relation

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

set_option linter.unusedTactic false

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


/-- コマンドと状態を組にしたもの。configuration -/
abbrev Config := Stmt × State

-- /-- SmallStep の二項関係バージョン -/
-- abbrev smallStepBin (conf₁ conf₂ : Config) : Prop := SmallStep conf₁.1 conf₁.2 conf₂.1 conf₂.2

-- add_aesop_rules safe tactic [(by dsimp [smallStepBin]) (rule_sets := [SmallStepRules])]

open Relation

/-- `smallStepBin` という二項関係の反射的推移的閉包 -/
@[reducible] def smallStepStar : Config → Config → Prop :=
  ReflTransGen (fun conf₁ conf₂ => SmallStep conf₁.1 conf₁.2 conf₂.1 conf₂.2)

@[inherit_doc] infix:30 " ⇒* " => smallStepStar

#check sillyLoop

example : (sillyLoop, (fun _ => 0)["x" ↦ 1]) ⇒* (skip, (fun _ => 0)) := by
  dsimp [sillyLoop]

  generalize hB : (fun s : State ↦ s "x" > s "y") = B0
  generalize hS : (skip;; assign "x" (fun s ↦ s "x" - 1)) = S0
  generalize hs : (fun v ↦ (if v = "x" then 1 else 0)) = s0

  have : (whileDo B0 S0, s0) ⇒* (skip, fun x ↦ 0) := calc
    _ ⇒* (ifThenElse B0 (S0 ;; whileDo B0 S0) skip, s0) := ?step1
    _ ⇒* (S0 ;; whileDo B0 S0, s0) := ?step2
    _ ⇒* (whileDo B0 S0, fun _ ↦ 0) := ?step3
    _ ⇒* (skip, fun x ↦ 0) := by sorry

  case step1 =>
    apply ReflTransGen.head (a := (whileDo B0 S0, s0)) (hbc := ReflTransGen.refl)
    apply SmallStep.whileDo

  case step2 =>
    apply ReflTransGen.head (a := (ifThenElse B0 (S0 ;; whileDo B0 S0) skip, s0)) (hbc := ReflTransGen.refl)
    apply SmallStep.if_true
    rw [← hB, ← hs]
    simp

  case step3 =>
    have : (S0,s0) =>ₛ (skip, fun x ↦ 0) := by sorry
    have := @SmallStep.seq_step (S := S0) (s := s0) (S' := skip) (s' := fun _ ↦ 0)
    sorry

  sorry

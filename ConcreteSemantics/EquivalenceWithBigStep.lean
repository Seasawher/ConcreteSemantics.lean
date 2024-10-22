/- ### 7.3.1 Equivalence with Big-Step Semantics
BigStep 意味論を、SmallStep に翻訳できる。
-/
import ConcreteSemantics.BigStep
import ConcreteSemantics.SmallStep

open Relation

/-- BigStep と SmallStep の等価性を示す際に使う補題 -/
theorem smallStepStar_skip_seq
  {S s t T}
  (hS : (S, s) ⇒* (skip, t))
  : (S ;; T, s) ⇒* (skip;; T, t) := by
  -- hS を `S = skip` のケースと `(S, s) ⇒ (S', s') ∧ (S', s') ⇒* (skip, t)` のケースに分けて考える

  -- induction時のエラーを避けるため、一時的に(S₁, s₁)を変数csに一般化する
  generalize hcs : (S, s) = cs at hS

  -- tail ではなく head の方を使う
  induction hS using ReflTransGen.head_induction_on generalizing S s
  case refl => simp_all; rfl
  case head _ «S', s'» hS₂ _ ih =>
    -- 一時的に置いた変数を消す
    simp [← hcs] at *; clear hcs

    -- Config を Stmt と State にバラす
    rcases «S', s'» with ⟨S', s'⟩

    specialize ih rfl

    calc
      _ ⇒ (S';; T, s') := by small_step
      _ ⇒* (skip;; T, t) := by apply ih

/-- BigStep 意味論の式を、SmallStep star に翻訳することができる。 -/
theorem big_step_to_small_step_star {S : Stmt} {s t : State} (h : (S, s) ==> t) : (S, s) ⇒* (skip, t) := by
  induction h
  case skip =>
    rfl
  case assign x a s₁ =>
    calc
      _ ⇒ (_, _) := by small_step
      _ ⇒* (_, _) := by rfl
  case seq S₁ T s₁ t₁ u₁ _hS₁ _hT hS_ih hT_ih => calc
    (S₁;; T, s₁) ⇒* (skip;; T, t₁) := smallStepStar_skip_seq hS_ih
    _ ⇒ (T, t₁) := by small_step
    _ ⇒* (skip, u₁) := hT_ih
  case if_true B s t hCond S T _h ih => calc
    _ ⇒ (S, s) := by small_step
    _ ⇒* (skip, t) := ih
  case if_false B s t hCond S T _h ih => calc
    _ ⇒ (T, s) := by small_step
    _ ⇒* (skip, t) := ih
  case while_true B S s t u hCond _h₁ _h₂ ih₁ ih₂ => calc
    _ ⇒ (ifThenElse B (S ;; whileDo B S) skip, s) := by small_step
    _ ⇒ (S ;; whileDo B S, s) := by small_step
    _ ⇒* (skip ;; whileDo B S, t) := smallStepStar_skip_seq ih₁
    _ ⇒ (whileDo B S, t) := by small_step
    _ ⇒* (skip, u) := ih₂
  case while_false B S s hCond => calc
    _ ⇒ (ifThenElse B (S ;; whileDo B S) skip, s) := by small_step
    _ ⇒ (skip, s) := by small_step
    _ ⇒* (skip, s) := by rfl

theorem small_step_star_to_big_step {S : Stmt} {s t : State} (h : (S, s) ⇒* (skip, t)) : (S, s) ==> t := by
  -- induction時のエラーを避けるため、一時的に(S₁, s₁)を変数csに一般化する
  generalize hcs : (S, s) = cs at h

  induction h using ReflTransGen.head_induction_on generalizing S s
  case refl => big_step
  case head _ «S', s'» h₁ h₂ ih =>
    -- 一時的に置いた変数を消す
    simp [← hcs] at *; clear hcs

    -- Config を Stmt と State にバラす
    rcases «S', s'» with ⟨S', s'⟩
    replace h₂ : (S', s') ⇒* (skip, t) := h₂
    specialize ih rfl

    cases h₁
    case assign => cases ih; big_step
    case seq_step S S' T h₁ =>
      simp at h₁
      -- `h₁ : (S,s) ⇒ (S',s')` と `ih : (S';; T,s') ==> t` から `(S;; T,s) ==> t` を示す補題がいるかも
      sorry

    all_goals sorry

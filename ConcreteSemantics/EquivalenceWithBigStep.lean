/- ### 7.3.1 Equivalence with Big-Step Semantics
BigStep 意味論を、SmallStep に翻訳できる。
-/
import ConcreteSemantics.BigStep
import ConcreteSemantics.SmallStep

open Relation

/-- BigStep 意味論の式を、SmallStep star に翻訳することができる。 -/
theorem big_step_to_small_step_star {S : Stmt} {s t : State} (h : (S, s) ==> t) : (S, s) ⇒* (skip, t) := by
  induction h
  case skip =>
    rfl
  case assign x a s₁ =>
    calc
      _ ⇒ (_, _) := by small_step
      _ ⇒* (_, _) := by rfl
  case seq S₁ T s₁ t₁ u₁ hS₁ hT hS_ih hT_ih =>
    calc
      _ ⇒* (skip;; T, t₁) := ?step1
      _ ⇒* (_, _) := by sorry
      _ ⇒* (_, _) := by small_step

    case step1 =>
      generalize hct : (skip, t₁) = ct
      rw [hct] at hS_ih
      induction hS_ih
      case refl => sorry
      case tail _ _ _ =>
        sorry
  all_goals sorry

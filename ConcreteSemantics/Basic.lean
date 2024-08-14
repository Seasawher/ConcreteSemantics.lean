import ConcreteSemantics.BigStep

/- ### 7.2.3 Rule Inversion
逆向きの推論ルールを与えることができる。
-/

/-- skip に関する inversion rule -/
@[simp] theorem BigStep.skip_iff {s t : State} : (Stmt.skip, s) ==> t ↔ t = s := by
  constructor <;> intro h
  · cases h
    rfl
  · rw [h]
    big_step

/-- seq に関する inversion rule -/
@[simp] theorem BigStep.seq_iff {S T s u} :
    (S;; T, s) ==> u ↔ (∃t, (S, s) ==> t ∧ (T, t) ==> u) := by
  constructor <;> intro h

  case mp =>
    cases h
    case seq t hS hT =>
      exact ⟨t, hS, hT⟩

  case mpr =>
    obtain ⟨t, hS, hT⟩ := h
    big_step

/-- if に関する inversion rule -/
@[simp] theorem BigStep.if_iff {B S T s t} : (ifThenElse B S T, s) ==> t ↔
    (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by
  constructor <;> intro h
  · cases h <;> simp_all
  · rcases h with ⟨hcond, hbody⟩ | ⟨hcond, hbody⟩
    · big_step
    · big_step

/-- while に関する inversion rule -/
theorem BigStep.while_iff {B S s u} : (whileDo B S, s) ==> u ↔
    (∃ t, B s ∧ (S, s) ==> t ∧ (whileDo B S, t) ==> u) ∨ (¬ B s ∧ u = s) := by
  constructor <;> intro h
  · by_cases hcond : B s
    case pos =>
      left
      simp_all only [true_and]
      sorry
    case neg =>
      sorry
  sorry

import ConcreteSemantics.BigStep

/- ### 7.2.3 Rule Inversion
逆向きの推論ルールを与えることができる。
-/

/-- skip に関する inversion rule -/
@[simp] theorem BigStep.skip_iff {s t : State} : (Stmt.skip, s) ==> t ↔ t = s := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    apply BigStep.skip

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
    exact BigStep.seq _ _ _ _ u hS hT

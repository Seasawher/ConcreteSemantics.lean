import ConcreteSemantics.Equivalence

/- ### 7.2.5 Execution in IMP is Deterministic -/

/-- IMP は決定的 -/
theorem imp_deterministic (S : Stmt) (s t u : State) (h1 : (S, s) ==> t) (h2 : (S, s) ==> u) : t = u := by
  induction S generalizing u t s

  -- S が skip の場合
  case skip =>
    aesop

  -- S が assign の場合
  case assign v a =>
    cases h1 <;> cases h2
    simp

  -- S が seq の場合
  case seq c c' hc hc' =>
    simp [BigStep.seq_iff] at h1 h2
    rcases h1 with ⟨t', h1, h1'⟩
    rcases h2 with ⟨u', h2, h2'⟩
    have eq' : t' = u' := by
      apply hc <;> assumption
    rw [eq'] at h1' h1; clear h1 h2 eq' hc
    apply hc' (s := u') <;> assumption

  all_goals sorry

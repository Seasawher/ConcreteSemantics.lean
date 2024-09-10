import ConcreteSemantics.Equivalence

/- ### 7.2.5 Execution in IMP is Deterministic -/

/-- IMP は決定的 -/
theorem imp_deterministic (S : Stmt) (s t u : State) (ht : (S, s) ==> t) (hu : (S, s) ==> u) : t = u := by
  induction S generalizing u t s

  -- S が skip の場合
  case skip =>
    aesop

  -- S が assign の場合
  case assign v a =>
    cases ht <;> cases hu
    simp

  -- S が seq の場合
  case seq c c' hc hc' =>
    simp [BigStep.seq_iff] at ht hu
    rcases ht with ⟨t', ht, ht'⟩
    rcases hu with ⟨u', hu, hu'⟩

    -- 帰納法の仮定から、`t' = u'` であることがわかる
    have eq' : t' = u' := by
      apply hc <;> assumption
    rw [eq'] at ht' ht
    clear ht hu eq' hc

    -- 再び帰納法の仮定を使う
    apply hc' (s := u') <;> assumption

  all_goals sorry

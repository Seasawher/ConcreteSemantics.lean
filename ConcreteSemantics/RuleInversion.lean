import ConcreteSemantics.BigStep

/- ### 7.2.3 Rule Inversion
逆向きの推論ルールを与えることができる。
-/

namespace BigStep

/-- skip に関する BigStep から状態の簡単な式を導く -/
theorem cases_of_skip {s t : State} : (Stmt.skip, s) ==> t → t = s := by
  intro h
  cases h
  rfl

-- skip に関する BigStep が仮定にあるときに big_step で扱えるようにする
add_aesop_rules safe [destruct cases_of_skip (rule_sets := [BigStepRules])]

/-- skip に関する inversion rule -/
@[simp] theorem skip_iff {s t : State} : (Stmt.skip, s) ==> t ↔ t = s := by
  big_step

/-- seq に関する BigStep から状態の簡単な式を導く -/
theorem cases_of_seq {S T s u} :
    (S;; T, s) ==> u → (∃t, (S, s) ==> t ∧ (T, t) ==> u) := by
  intro h
  cases h
  big_step

-- seq に関する BigStep が仮定にあるときに big_step で扱えるようにする
add_aesop_rules safe [destruct cases_of_seq (rule_sets := [BigStepRules])]

/-- seq に関する inversion rule -/
@[simp] theorem seq_iff {S T s u} :
    (S;; T, s) ==> u ↔ (∃t, (S, s) ==> t ∧ (T, t) ==> u) := by
  big_step

/-- if に関する BigStep から簡単な条件式を導く (条件式が真の場合) -/
theorem cases_if_of_true {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
  intro h
  cases h <;> try contradiction
  assumption

/-- if に関する BigStep から簡単な条件式を導く (条件式が偽の場合) -/
theorem cases_if_of_false {B S T s t} (hcond : ¬ B s) : (ifThenElse B S T, s) ==> t → (T, s) ==> t := by
  intro h
  cases h <;> try contradiction
  assumption

-- if に関する BigStep が仮定にあるときに big_step で扱えるようにする
add_aesop_rules safe [destruct cases_if_of_true (rule_sets := [BigStepRules])]
add_aesop_rules safe [destruct cases_if_of_false (rule_sets := [BigStepRules])]

/-- ifThenElse の分解時に現れる式を分解するための命題論理の補題 -/
theorem and_excluded {P Q R : Prop} (hQ : P → Q) (hR : ¬ P → R) : (P ∧ Q ∨ ¬ P ∧ R) := by
  by_cases h : P
  · left
    exact ⟨h, hQ h⟩
  · right
    exact ⟨h, hR h⟩

add_aesop_rules unsafe 30% [apply and_excluded (rule_sets := [BigStepRules])]

/-- if に関する inversion rule -/
@[simp] theorem if_iff {B S T s t} : (ifThenElse B S T, s) ==> t ↔
    (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by
  big_step

/-- while に関する inversion rule。
条件式が真か偽かで場合分けをする

TODO: aesop に自動的に使用してもらう方法を見つける -/
theorem while_iff {B S s u} : (whileDo B S, s) ==> u ↔
    (∃ t, B s ∧ (S, s) ==> t ∧ (whileDo B S, t) ==> u) ∨ (¬ B s ∧ u = s) := by
  constructor <;> intro h

  case mp =>
    -- 条件式が成り立つかどうかで場合分けする
    by_cases hcond : B s

    -- 成り立つ場合
    case pos =>
      left
      -- `(whileDo B S,s) ==> u` という仮定を条件式が真ということを使って分解
      cases h <;> try contradiction

      -- 変数が死ぬが、aesop は rename_i を使ってくれるので通る
      big_step

    -- 成り立たない場合
    case neg =>
      right

      -- 条件式が成立しないことと `(whileDo B S,s) ==> u` という仮定から、
      -- `u = s` であることがわかる
      cases h <;> try contradiction
      simp_all

  case mpr => big_step

/-- while の条件式が真のときの inversion rule -/
@[simp] theorem while_true_iff {B S s u} (hcond : B s) : (whileDo B S, s) ==> u ↔
    (∃ t, (S, s) ==> t ∧ (whileDo B S, t) ==> u) := by
  -- 条件式の真偽で場合分けをする
  rw [while_iff]

  -- 条件式が成り立つ場合のみ残す
  simp [hcond]

/-- while の条件式が偽のときの inversion rule -/
@[simp] theorem while_false_iff {B S s t} (hcond : ¬ B s) : (whileDo B S, s) ==> t ↔ t = s := by
  -- 条件式の真偽で場合分けをする
  rw [while_iff]

  -- 条件式が成り立たない場合のみ残す
  simp [hcond]

/- inversion rule を使って次のような命題が証明できる -/

example (c₁ c₂ : Stmt) (s₁ s₃ : State) : (c₁;; c₂, s₁) ==> s₃ →
    ∃s₂, (c₁, s₁) ==> s₂ ∧ (c₂, s₂) ==> s₃ := by
  big_step

/-- seq `;;` を左結合にしても右結合にしても意味論の観点からは変化がない。 -/
theorem seq_assoc (c₁ c₂ c₃ : Stmt) (s u : State) :
    ((c₁;; c₂);; c₃, s) ==> u ↔ (c₁;; (c₂;; c₃), s) ==> u := by
  big_step

end BigStep

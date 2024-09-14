import ConcreteSemantics.BigStep

/- ### 7.2.3 Rule Inversion
逆向きの推論ルールを与えることができる。
-/

namespace BigStep

/-- skip に関する BigStep から状態の簡単な式を導く -/
theorem eq_of_skip {s t : State} : (Stmt.skip, s) ==> t → t = s := by
  intro h
  cases h
  rfl

-- eq_of_skip を使って仮定を言い換える
add_aesop_rules safe [destruct eq_of_skip (rule_sets := [BigStepRules])]

/-- skip に関する inversion rule -/
@[simp] theorem skip_iff {s t : State} : (Stmt.skip, s) ==> t ↔ t = s := by
  big_step

/-- seq に関する inversion rule -/
@[simp] theorem seq_iff {S T s u} :
    (S;; T, s) ==> u ↔ (∃t, (S, s) ==> t ∧ (T, t) ==> u) := by
  -- 両方向示す
  constructor <;> intro h

  -- 左から右を示す
  case mp =>
    -- BigStep.seq の定義から仮定を分解する
    cases h
    case seq t hS hT =>
      exists t

  -- 右から左を示す
  case mpr => big_step

/-- if に関する inversion rule (条件式が真の場合) -/
theorem if_iff_of_true {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t ↔ (S, s) ==> t := by
  constructor <;> intro h
  · cases h <;> simp_all
  · big_step

add_aesop_rules norm [simp if_iff_of_true (rule_sets := [BigStepRules])]

/-- if に関する inversion rule (条件式が偽の場合) -/
theorem if_iff_of_false {B S T s t} (hcond : ¬ B s) : (ifThenElse B S T, s) ==> t ↔ (T, s) ==> t := by
  constructor <;> intro h
  · cases h <;> simp_all
  · big_step

add_aesop_rules norm [simp if_iff_of_false (rule_sets := [BigStepRules])]

/-- if に関する inversion rule -/
@[simp] theorem if_iff {B S T s t} : (ifThenElse B S T, s) ==> t ↔
    (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by
  -- 同値の両方向を示す
  constructor <;> intro h

  -- 左から右を示す
  case mp =>
    -- BigStep.ifThenElse の定義から従う
    cases h <;> simp_all

  -- 右から左を示す
  case mpr =>
    rcases h with ⟨hcond, hbody⟩ | ⟨hcond, hbody⟩
    · big_step
    · big_step

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
      aesop

    -- 成り立たない場合
    case neg =>
      right

      -- 条件式が成立しないことと `(whileDo B S,s) ==> u` という仮定から、
      -- `u = s` であることがわかる
      cases h <;> try contradiction
      simp_all

  case mpr =>
    -- 条件式が成り立つかどうかで場合分けする
    rcases h with ⟨t, hcond, hbody, hrest⟩ | ⟨hcond, rfl⟩
    · apply BigStep.while_true hcond hbody hrest
    · apply BigStep.while_false (hcond := by assumption)

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

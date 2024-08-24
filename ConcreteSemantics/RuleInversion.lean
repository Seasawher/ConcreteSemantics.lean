import ConcreteSemantics.BigStep

/- ### 7.2.3 Rule Inversion
逆向きの推論ルールを与えることができる。
-/

namespace BigStep

/-- skip に関する inversion rule -/
@[simp] theorem skip_iff {s t : State} : (Stmt.skip, s) ==> t ↔ t = s := by
  -- 両方向示す
  constructor <;> intro h

  -- 左から右を示す
  case mp =>
    -- BigStep.skip の定義から、s = t であることがわかる
    cases h
    rfl

  -- 右から左を示す
  case mpr =>
    -- s = t なので、BigStep.skip の定義から従う
    rw [h]

    apply BigStep.skip

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
  case mpr =>
    obtain ⟨t, hS, hT⟩ := h

    -- big_step タクティクを使わない証明
    apply BigStep.seq <;> assumption

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
    · apply BigStep.if_true hcond <;> assumption
    · apply BigStep.if_false hcond <;> assumption

/-- while に関する inversion rule -/
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

end BigStep

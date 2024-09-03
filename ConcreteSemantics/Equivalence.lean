/- ### 7.2.4 Equivalence of Commands -/
import ConcreteSemantics.Stmt
import ConcreteSemantics.BigStep
import ConcreteSemantics.RuleInversion

namespace BigStep

/-- コマンドの BigStep 意味論における同値性 -/
def equivCmd (S T : Stmt) : Prop := ∀s t : State, (S, s) ==> t ↔ (T, s) ==> t

/-- `equivCmd` は反射的である -/
theorem equivCmd_refl (S : Stmt) : equivCmd S S := by
  intro s t
  rfl

/-- `equivCmd` は対称的である -/
theorem equivCmd_symm {S T : Stmt} (h : equivCmd S T) : equivCmd T S := by
  intro s t
  rw [h]

/-- `equivCmd` は推移的である -/
theorem equivCmd_trans {S T U : Stmt} (hST : equivCmd S T) (hTU : equivCmd T U) : equivCmd S U := by
  intro s t
  rw [hST, hTU]

/-- `equivCmd` は同値関係である -/
def equivCmd_equiv : Equivalence equivCmd := ⟨equivCmd_refl, equivCmd_symm, equivCmd_trans⟩

/-- `Stmt` という型に同値関係 `equivCmd` が付随しているということを宣言した -/
instance : Setoid Stmt where
  r := equivCmd
  iseqv := equivCmd_equiv

-- このように、`Stmt` の要素が同値であることを示すために `≈` を使うことができる
#check skip ≈ skip

/-- `≈` 記号の中身を展開するタクティク -/
syntax "unfold" "≈" : tactic
macro_rules
  | `(tactic|unfold ≈) => `(tactic|dsimp only [(· ≈ ·), Setoid.r, equivCmd])

/-- ### Lemma 7.3
`while` 文の意味は、
* 条件式が真なら `S` を実行して再び `while` ループを実行
* 条件式が偽なら `skip`
というコマンドに等しい。 -/
theorem while_eq_if_then_skip (B : State → Prop) (S : Stmt) :
  whileDo B S ≈ ifThenElse B (S;; whileDo B S) skip := by
  -- ≈ の定義を展開する
  unfold ≈

  -- 状態 `s, t` が与えられたとする
  intro s t

  -- 両方向を示す
  constructor <;> intro h

  case mp =>
    -- B が真かどうかで分岐
    rw [while_iff] at h
    -- aesop で片を付ける
    aesop

  case mpr =>
    -- 条件が真かどうかで分岐する
    -- while_iff を追加
    aesop (add safe [while_iff])

    done

/-- ### Lemma 7.4
IF 文の両方の分岐が同じコマンド `c` なら、それは `c` と同じ -/
theorem if_both_eq (B : State → Prop) (c : Stmt) : ifThenElse B c c ≈ c := by
  -- ≈ の定義を展開する
  unfold ≈

  -- 状態 `s, t` が与えられたとする
  intro s t

  -- 両方向を示す
  constructor <;> intro h

  case mp =>
    -- ifThenElse の定義を展開する
    rw [if_iff] at h
    -- aesop で片を付ける
    aesop

  case mpr =>
    -- ifThenElse の定義を展開する
    rw [if_iff]
    -- 条件式が成り立つかどうかで場合分けをする
    by_cases h : B s <;> simp_all

/-- ### Lemma 7.6
`(while b do c, s) ==> t` かつ `c ≈ c` ならば `(while b do c', s) ==> t` -/
theorem while_congr {B : State → Prop} {c c' : Stmt} {s t : State} (h : c ≈ c') (h_while : (whileDo B c, s) ==> t) :
    (whileDo B c', s) ==> t := by
  -- cases h_while

  -- case while_true w hcond hbody hrest =>
  --   -- 帰納法の仮定からわかることを書いておく
  --   have self := while_congr h hrest

  --   have := h s w |>.mp hbody
  --   apply BigStep.while_true (hcond := hcond) (hbody := this) (hrest := self)

  -- case while_false hcond =>
  --   apply BigStep.while_false
  --   assumption
  sorry

/-- ### Lemma 7.5
コマンド `c` と `c'` が同値ならば、`While` を付けても同値 -/
theorem while_eq_of_eq (B : State → Prop) (c c' : Stmt) (h : c ≈ c') : whileDo B c ≈ whileDo B c' := by
  -- ≈ の定義を展開する
  unfold ≈

  -- 状態 `s, t` が与えられたとする
  intro s t

  -- 両方向を示す
  constructor <;> intro h'

  case mp =>
    -- whileDo の定義を展開する
    rw [while_iff] at h'
    obtain ⟨w, hb, hw, hwh⟩ := h'

    have := h s w |>.mp hw
    apply BigStep.while_true (hcond := hb) (hbody := this)

    specialize h s w

    -- aesop で片を付ける
    aesop
    all_goals sorry

  case mpr =>
    -- whileDo の定義を展開する
    rw [while_iff]
    -- aesop で片を付ける
    aesop
    sorry

end BigStep
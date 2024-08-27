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

/-- `while` 文の意味は、
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

end BigStep

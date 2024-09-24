/- # small step に応用するための aesop ラッパーを作る

`aesop` をカスタマイズして、`small_step` というタクティクを作成する。
-/
import Aesop

-- SmallStepRules という名前のルールセットを登録する
declare_aesop_rule_sets [SmallStepRules]

/-- `SmallStep` 用の aesop ラッパー -/
macro "small_step" : tactic => do `(tactic| aesop (rule_sets := [SmallStepRules]))

/-- `small_step` が使用した補題を生成する -/
macro "small_step?" : tactic => `(tactic| aesop? (rule_sets := [SmallStepRules]))

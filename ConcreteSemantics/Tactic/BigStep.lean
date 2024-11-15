/- # big step に応用するための aesop ラッパーを作る

`aesop` をカスタマイズして、`big_step` というタクティクを作成する。
-/
import Aesop

-- BigStepRules という名前のルールセットを登録する
declare_aesop_rule_sets [BigStepRules]


/-- `BigStep` 用の aesop ラッパー -/
macro "big_step" : tactic => do `(tactic| aesop (rule_sets := [BigStepRules]))

/-- `big_step` が使用した補題を生成する -/
macro "big_step?" : tactic => `(tactic| aesop? (rule_sets := [BigStepRules]))

open Lean Parser Category

-- macro "add_big_step_rules" e:Aesop.rule_expr : command =>
--   `(add_aesop_rules $e )

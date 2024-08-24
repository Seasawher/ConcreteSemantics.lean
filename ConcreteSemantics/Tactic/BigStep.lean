import ConcreteSemantics.BigStep

/-! BigStep の形をしたゴールを証明するタクティク `big_step` を定義する

便利なタクティクを作ろうとおもったが、デバッグが思ったより大変だったので後回しになっている。 -/

/-- `(S, s) ==> t` の形をしたゴールを示すためのタクティク -/
syntax "big_step" : tactic

-- 以下の変換ルールは下から順番に試されてゆき、失敗した時点で次のものに移る。成功したときに展開先が確定する

macro_rules
  | `(tactic| big_step) => `(tactic| apply BigStep.skip)

macro_rules
  | `(tactic| big_step) => `(tactic| apply BigStep.assign)

macro_rules
  | `(tactic| big_step) => `(tactic| apply BigStep.seq)

macro_rules
  | `(tactic| big_step) => `(tactic| apply BigStep.seq (by assumption) (by assumption))

-- hcond を引数として渡して apply することにより、
-- if_true を使うべき場面で if_false へ展開してしまうバグを防止している
macro_rules
  | `(tactic| big_step) => `(tactic| apply BigStep.if_true (hcond := by assumption) <;> assumption)

macro_rules
  | `(tactic| big_step) => `(tactic| apply BigStep.if_false (hcond := by assumption) <;> assumption)

macro_rules
  | `(tactic| big_step) => `(tactic| apply BigStep.while_true (hcond := by assumption) <;> try simp_all)

macro_rules
  | `(tactic| big_step) => `(tactic| apply BigStep.while_false (hcond := by assumption) <;> try simp_all)

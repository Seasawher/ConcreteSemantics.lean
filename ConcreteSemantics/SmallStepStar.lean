import ConcreteSemantics.SmallStep
import Mathlib.Logic.Relation

/-- コマンドと状態を組にしたもの。configuration -/
abbrev Config := Stmt × State

/-- SmallStep の二項関係バージョン -/
abbrev smallStepBin (conf₁ conf₂ : Config) : Prop := SmallStep conf₁.1 conf₁.2 conf₂.1 conf₂.2

open Relation

/-- `smallStepBin` という二項関係の反射的推移的閉包 -/
def smallStepStar : Config → Config → Prop := ReflTransGen smallStepBin

@[inherit_doc] infix:30 " ⇒* " => smallStepStar

#check sillyLoop

example : (sillyLoop, (fun _ => 0)["x" ↦ 1]) ⇒* (skip, (fun _ => 0)) := by
  sorry

import ConcreteSemantics.Ch08Compiler.S02ReasoningAboutMachineExecutions

namespace Compiler

/-- 数値計算式 -/
inductive AExp where
  /-- 定数 -/
  | n (v : Int)
  /-- 変数 -/
  | v (name : Vname)
  /-- 足し算 -/
  | plus (a₁ a₂ : AExp)

/-- AExp を 命令列にコンパイルする -/
def acomp : AExp → List Instr
  | .n n => [.Loadi n]
  | .v x => [.Load x]
  | .plus a₁ a₂ => acomp a₁ ++ acomp a₂ ++ [Instr.Add]

/-- AExp を評価する -/
def aval : AExp → State → Val
  | .n n, _ => n
  | .v x, s => s x
  | .plus a₁ a₂, s => aval a₁ s + aval a₂ s

#check exec_append_trans
theorem acomp_correct (a : AExp) (s : State) (stk : List Int) :
  (acomp a) ⊢ ⟨0, s, stk⟩ →* ⟨(acomp a).length, s, aval a s :: stk⟩ := by
  induction a generalizing stk
  case plus a₁ a₂ a₁_ih a₂_ih =>
    dsimp [acomp]
    specialize a₂_ih (aval a₁ s :: stk)
    have := @exec_append_trans (c__c' := a₁_ih stk) (P' := acomp a₂)
    simp at this; specialize this _ a₂_ih; simp at this
    replace this := exec_appendR this (P' := [.Add])
    have indexH : (acomp a₁ ++ (acomp a₂ ++ [.Add]))[((acomp a₁).length : Int) + ↑(acomp a₂).length]! = .Add := by
      sorry
    let c' : Config := { pc := ↑(acomp a₁ ++ acomp a₂ ++ [Instr.Add]).length, s := s, stk := aval (a₁.plus a₂) s :: stk }
    replace this := execStar_exec1 (c := c') this (by simp [exec1, indexH, iexec]; sorry)
    sorry
  all_goals
    apply execStar.step (h₂ := execStar.refl ..)
    simp [acomp, exec1]
    rfl

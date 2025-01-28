import ConcreteSemantics.Ch08Compiler.S01InstAndStackMachine

/- ## Reasoning About Machine Executions -/
namespace Compiler

/-- プログラム P を機械状態 c で実行した結果 c' に遷移するなら, P にプログラムを付け足しても c' になる. -/
theorem exec_appendR {P c c' P'} (h : P ⊢ c →* c') : (P ++ P') ⊢ c →* c' := by
  induction h
  case refl => apply execStar.refl
  case step c c' c'' h₁ h₂ ih =>
    apply execStar.step (h₂ := ih)
    dsimp [exec1] at h₁ ⊢
    apply And.intro (right := by cases h₁; simp only [List.length_append]; omega)
    rw [h₁.left.symm]

    have : P[c.pc]! = (P ++ P')[c.pc]! := by
      simp only [List.getElem!_eq_getElem?_getD]
      rw [List.getElem?_append_left h₁.right]
    rw [this]

theorem iexec_shift {x c c' n} :
  (iexec x { c with pc := n + c.pc } = { c' with pc := n + c'.pc }) ↔ iexec x c = c' := by
  constructor <;> intro h
  · cases x <;> (simp [iexec] at h ⊢)
    -- panic!する分岐があるケースをどう処理したらいい？
    case Add => sorry
    case Store => sorry
    case Jmpless => sorry
    case Jmpge => sorry
    all_goals
      rcases h with ⟨h₁, h₂, h₃⟩
      simp_all
      congr
      try omega
    -- ↓ h₁からゴールを導きたいが, IntとNatの変換でややこしくなっている
    · rename_i intN
      sorry
  · sorry

theorem exec_appendL {P c c' P'}
  (h : P ⊢ c →* c')
  : (P' ++ P) ⊢ { c with pc := P'.length + c.pc } →* { c' with pc := P'.length + c'.pc } := by
  induction h
  case refl => apply execStar.refl
  case step c c' c'' h₁ h₂ ih =>
    apply execStar.step (h₂ := ih)
    dsimp [exec1] at h₁ ⊢
    apply And.intro (right := by cases h₁; simp only [List.length_append]; omega)
    -- rw [h₁.left.symm]

    -- この先はiexec_shiftを使って証明する
    sorry

  done

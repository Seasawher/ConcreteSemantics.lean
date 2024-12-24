/- ## Instructions and Stack Machine -/

variable {α : Type} [Inhabited α] (xs ys : List α)

/-- ### lemma 8.1
自然数ではなくて、整数によるインデックスアクセスを考えて、
インデックスアクセスの分配法則を証明する。
-/
example (i : Int) (pos : i ≥ 0)
    : (xs ++ ys)[i.toNat]! = (if h : i < xs.length then xs[i.toNat] else ys[i.toNat - xs.length]!) := by
  -- `i : Int` を自然数に翻訳する
  have ⟨n, hn⟩ : ∃ n : Nat, i.toNat = n := by
    exists i.toNat
  simp only [hn]
  have hi : i < ↑xs.length ↔ n < xs.length := by
    simp [← hn]
    omega
  simp only [hi]

  -- `n` が `xs` の範囲内にあるかどうかで場合分けをする
  by_cases h : n < xs.length
  · simp [h]
    rw [List.getElem?_append_left h]
    have : xs[n]? = some xs[n] := by
      exact (List.getElem?_eq_some_getElem_iff xs n h).mpr trivial
    simp [this]
  · simp [h]

    -- `n` が `xs ++ ys` の範囲内にあるかどうかで場合分けをする
    by_cases valid : n < (xs ++ ys).length
    case neg =>
      simp [show (xs ++ ys)[n]? = none from by simp_all]
      have : n - xs.length ≥ ys.length := by
        simp at valid h
        omega
      simp [show ys[n - xs.length]? = none from by simp_all]
    case pos =>
      simp at h
      have := List.getElem?_append_right (l₁ := xs) (l₂ := ys) (n := n) h
      simp [this]

/-- 変数名 -/
abbrev Vname := String

/-- machine の命令 -/
inductive Instr where
  | Loadi (n : Int)
  | Load (x : Vname)
  | Add
  | Store (x : Vname)
  | Jmp (n : Int)
  | Jmpless (n : Int)
  | Jmpge (n : Int)

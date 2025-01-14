import ConcreteSemantics.Ch07IMP.S01IMPCommands

/- ## Instructions and Stack Machine -/
namespace Compiler

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

/-- メモリやスタックに格納されている値 -/
abbrev Val := Int

/-- machine の命令 -/
inductive Instr where
  /-- スタックのn番目を取得する -/
  | Loadi (n : Int)
  /-- 変数名が指すメモリアドレスの値を取得する -/
  | Load (x : Vname)
  /-- スタックの一番上とその下を足す -/
  | Add
  /-- 変数名が指すメモリアドレスにスタックの一番上の値を格納する -/
  | Store (x : Vname)
  /-- 今実行している命令の場所を基準に n だけジャンプする -/
  | Jmp (n : Int)
  /-- スタックの一番上とその下を比較し、二つ目の方が小さければ ジャンプする -/
  | Jmpless (n : Int)
  /-- スタックの一番上とその下を比較し、二つ目の方が大きいか等しければ ジャンプする -/
  | Jmpge (n : Int)

/-- スタック -/
abbrev Stack := List Val

/-- メモリ -/
abbrev State := Vname → Val

/-- マシンの状態 -/
abbrev Config := Int × State × Stack

/-- 機械語の実行 -/
def iexec : Instr → Config → Config
  | .Loadi n, (i, s, stk) => (i + 1, s, n :: stk)
  | .Load x, (i, s, stk) => (i + 1, s, s x :: stk)
  | .Add, (i, s, hd :: hd₂ :: stk) => (i + 1, s, (hd₂ + hd) :: stk)
  | .Add, _ => panic! "スタックの数が2個未満だった (Add命令)"
  | .Store x, (i, s, hd :: stk) => (i + 1, s[x ↦ hd], stk)
  | .Store _, _ => panic! "スタックの数が2個未満だった (Store命令)"
  | .Jmp n, (i, s, stk) => (i + 1 + n, s, stk)
  | .Jmpless n, (i, s, hd :: hd₂ :: stk) =>
    (if hd₂ < hd then i + 1 + n else i + 1, s, stk)
  | .Jmpless _, _ => panic! "スタックの数が2個未満だった (Jmpless命令)"
  | .Jmpge n, (i, s, hd :: hd₂ :: stk) =>
    (if hd ≤ hd₂ then i + 1 + n else i + 1, s, stk)
  | .Jmpge _, _ => panic! "スタックの数が2個未満だった (Jmpge命令)"

import ConcreteSemantics.Stmt

/- ## 7.2 Big-Step Semantics

### 7.2.1 Definition
-/
set_option quotPrecheck false in

/-- 状態 `s : State` があったとき、変数 `x` に対してだけ値を更新したものを表す記法 -/
notation s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)

/-- BigStep 意味論。操作的意味論の一種。コマンドの実行前と実行後の状態だけを見て中間状態を見ないので big step と呼ばれる。
* 1つめの引数の `(c, s) : Stmt × State` は、初期状態 `s` のもとでコマンド `c` を実行することに対応。
* 2つめの引数の `t : State` は、コマンドが終了したときの状態に対応。

`BigStep (c, s) t` を、`(c, s) ==> t` と書く。
-/
inductive BigStep : Stmt × State → State → Prop where
  /-- skip コマンドの意味論。
  skip コマンドの実行前に状態が `s` であったなら、実行後も `s` のまま変わらない。-/
  | skip (s : State) : BigStep (skip, s) s

  /-- assign コマンドの意味論。
  代入文 `x := a` の実行前に状態が `s` であったなら、代入文の実行後には状態は変数 `x` についてだけ更新される。
  `x` の値は、式 `a` を状態 `s` において評価したものに変わる。 -/
  | assign (x : Variable) (a : State → Nat) (s : State) : BigStep (assign x a, s) (s[x ↦ a s])

  /-- seq コマンドの意味論。
  コマンド `S` により状態が `s` から `t` に変わり、 コマンド `T` により状態が `t` から `u` に変わるのであれば、
  コマンド `S;; T` により状態は `s` から `u` に変わる。-/
  | seq {S T : Stmt} {s t u : State} (hS : BigStep (S, s) t) (hT : BigStep (T, t) u) :
    BigStep (S;; T, s) u

  /-- if 文の、条件式が true のときの意味論。
  コマンド `S` により状態が `s` から `t` に変わり、かつ条件式が真であるとき
  `ifThenElse B S T` により状態は `s` から `t` に変わる。 -/
  | if_true {B : State → Prop} {s t : State} (hcond : B s) (S T : Stmt) (hbody : BigStep (S, s) t) :
    BigStep (ifThenElse B S T, s) t

  /-- if 文の、条件式が false のときの意味論。
  コマンド `T` により状態が `s` から `t` に変わり、かつ条件式が偽であるとき
  `ifThenElse B S T` により状態は `s` から `t` に変わる。 -/
  | if_false {B : State → Prop} {s t : State} (hcond : ¬ B s) (S T : Stmt) (hbody : BigStep (T, s) t) :
    BigStep (ifThenElse B S T, s) t

  /-- while 文の、条件式が真のときの意味論。
  `whileDo B S` は、開始時に `B` が成り立っているなら、
  `S` を実行してから `whileDo B S` を実行するのと同じ意味になる。

  * 前提1: コマンド `S` により状態が `s` から `t` に変わり、
  * 前提2: かつ `whileDo B S` により状態が `t` から `u` に変わるのであれば、
  * 帰結: `whileDo B S` により状態は `s` からスタートさせても `u` に変わる。

  #### 例
  たとえば `while x < 10 do x := x + 1` というプログラムを考えて、
  状態をそれぞれ `s := [x ↦ 3]`, `t := [x ↦ 4]`, `u := [x ↦ 10]` としてみると具体例になる。

  #### 補足
  `while_true` の評価は「終わらないかもしれない」ものである必要がある。だから `BigStep` を再帰関数ではなく帰納的命題として定義する必要があった。
  -/
  | while_true {B S s t u} (hcond : B s) (hbody : BigStep (S, s) t) (hrest : BigStep (whileDo B S, t) u) :
    BigStep (whileDo B S, s) u

  /-- while 文の、条件式が偽のときの意味論。条件文 `B` が偽のとき、コマンド `S` の内容に関わらず、
  コマンド `whileDo B S` は状態を変化させない。-/
  | while_false {B S s} (hcond : ¬ B s) : BigStep (whileDo B S, s) s

-- BigStep のための見やすい記法を用意する
@[inherit_doc] notation:55 "(" S:55 "," s:55 ")" " ==> " t:55 => BigStep (S, s) t

/-- `B`が真の時、 `whileDo B S` は `S;; whileDo B S` と同じ意味であることを示す -/
theorem while_true_seq_self {B S s t} (hcond : B s) : (whileDo B S, s) ==> t ↔ (S;; whileDo B S, s) ==> t := by
  -- 両方向示す
  constructor <;> intro h

  -- 左から右を示す
  case mp =>
    -- `whileDo` が当てはまる評価規則は `BigStep.while_true` と `BigStep.while_false` しかない
    cases h

    -- while_false の場合は仮定`hcond`と矛盾するので考えない
    case while_false => contradiction

    -- while_true の場合、 `hbody` と `hrest` から `BigStep.seq` を適用できる
    case while_true _ hbody hrest =>
      apply BigStep.seq hbody hrest

  -- 右から左を示す
  case mpr =>
    -- 文が `S;; T` の形なので、当てはまる評価規則は`BigStep.seq`だけ
    cases h

    -- `hS` `hT` がそれぞれ `BigStep.while_true` の `hbody` `hrest` に対応している
    case seq _ hS hT =>
      exact BigStep.while_true hcond hS hT

/-- `B`が偽の時、 `whileDo B S` は `skip` と同じ意味であることを示す -/
theorem while_false_skip {B S s t} (hcond : ¬ B s) : (whileDo B S, s) ==> t ↔ (skip, s) ==> t := by
  -- 両方向示す
  constructor <;> intro h

  -- 左から右を示す
  case mp =>
    cases h

    -- while_true の場合は仮定`hcond`と矛盾するので考えない
    case while_true => contradiction

    case while_false =>
      apply BigStep.skip

  -- 右から左を示す
  case mpr =>
    cases h

    case skip =>
      exact BigStep.while_false hcond

/-- `whileDo B S` と `ifThenElse B (S;; whileDo B S) skip` は同じ
(SmallStep 意味論では`whileDo`の意味をこのように定義できる)
-/
theorem while_if {B S s t} : (whileDo B S, s) ==> t ↔ (ifThenElse B (S;; whileDo B S) skip, s) ==> t := by
  constructor <;> intro h

  case mp =>
    cases h
    case while_true hcond hbody hrest =>
      apply BigStep.if_true hcond
      apply BigStep.seq hbody hrest

    case while_false hcond =>
      apply BigStep.if_false hcond
      apply BigStep.skip

  case mpr =>
    cases h
    case if_true hcond hbody =>
      cases hbody
      case seq hbody hrest =>
        apply BigStep.while_true hcond hbody hrest

    case if_false hcond hbody =>
      cases hbody
      apply BigStep.while_false hcond

/-- `sillyLoop` コマンドにより、`x = 1, y = 0` という状態は `x = y = 0` という状態に変わる。 -/
example : (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ==> (fun _ ↦ 0) := by
  -- sillyLoop の定義を展開する
  dsimp [sillyLoop]

  -- 状態が `x ↦ 1, y ↦ 0` なので条件式は真になる。
  -- したがって while_true の条件を書き下す
  apply BigStep.while_true

  -- 条件式 `x > y` が真であること
  case hcond =>
    simp

  case hbody =>
    -- `;` でつながっているのを分解する
    apply BigStep.seq
    · apply BigStep.skip
    · apply BigStep.assign

  case hrest =>
    simp only [gt_iff_lt, ↓reduceIte, Nat.sub_self]

    -- 状態が複雑なラムダ式になっているので簡約する
    generalize hs : (fun v ↦ if v = "x" then 0 else if v = "x" then 1 else 0) = s
    replace hs : s = (fun v ↦ 0) := by
      ext v
      rw [← hs]
      simp
    rw [hs]

    -- このとき状態は `x ↦ 0, y ↦ 0` なので条件式は偽。
    -- したがって while_false を使う
    apply BigStep.while_false
    simp

/-! BigStep の形をしたゴールを証明するタクティク `big_step` を定義する -/
section bigstep_tactic

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

end bigstep_tactic

/- ### 7.2.2 Deriving IMP Executions -/

/-- `x := 5; y := x` という代入を続けて行うプログラム -/
def set_to_five : Stmt :=
  assign "x" (fun _ ↦ 5);; assign "y" (fun s ↦ s "x")

/-- `set_to_five` コマンドにより、任意の状態 `s` は `x = 5, y = 5` とセットされた状態に変わる。 -/
example (s : State) : (set_to_five, s) ==> (s["x" ↦ 5]["y" ↦ 5]) := by
  -- set_to_five の定義を展開する
  dsimp [set_to_five]

  -- big_step タクティクを使う証明
  try
    big_step <;> big_step
    done
    fail

  -- big_step タクティクを使わずに証明する
  apply BigStep.seq <;> apply BigStep.assign
  done

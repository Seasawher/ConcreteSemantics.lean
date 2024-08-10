/-- 変数（の名前）。
ここでは簡単のために、すべての文字列が変数として存在するものとする -/
abbrev Variable := String

/-- プログラムの状態。すべての変数の値を保持したもの。
ここでは簡単にするために、変数の値はすべて自然数だとしている。 -/
def State := Variable → Nat

/-- 考察対象の言語 のコマンド -/
inductive Stmt : Type where
  /-- 何もしないコマンド。else 部分がない if 文などを実現するために必要。 -/
  | skip : Stmt
  /-- `x := a` のような代入文。
  * 最初の引数 `v : Variable` は代入対象の変数を表す。
  * 2つめの引数 `a : State → Nat` は arithmetic expression を表していて、
    変数への値の割り当て（つまり `State`）が与えられるごとに何か値を返すものとされる。-/
  | assign : Variable → (State → Nat) → Stmt
  /-- 2つのコマンドを続けて実行する -/
  | seq : Stmt → Stmt → Stmt
  /-- if 文。`ifThenElse B S T` は、`B` が真のとき `S` を実行して `B` が偽のとき `T` を実行することに対応。-/
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  /-- while 文 -/
  | whileDo : (State → Prop) → Stmt → Stmt

@[inherit_doc] infix:60 "; " => Stmt.seq


open Stmt

/-- `x > y` が成り立つ間、`x := x - 1` という代入文を実行し続けるプログラム -/
def sillyLoop : Stmt :=
  whileDo (fun s => s "x" > s "y")
    (skip; assign "x" (fun s => s "x" - 1))

set_option quotPrecheck false in

/-- 状態 `s : State` があったとき、変数 `x` に対してだけ値を更新したものを表す記法 -/
notation:70 s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)

/-- BigStep 意味論。操作的意味論の一種。コマンドの実行前と実行後の状態だけを見て中間状態を見ないので big step と呼ばれる。
* 1つめの引数の `(c, s) : Stmt × State` は、初期状態 `s` のもとでコマンド `c` を実行することに対応。
* 2つめの引数の `t : State` は、コマンドが終了したときの状態に対応。
-/
inductive BigStep : Stmt × State → State → Prop where
  /-- skip コマンドの意味論。
  skip コマンドの実行前に状態が `s` であったなら、実行後も `s` のまま変わらない。-/
  | skip (s : State) : BigStep (skip, s) s

  /-- assign コマンドの意味論。
  代入文 `x := a` の実行前に状態が `s` であったなら、代入文の実行後には状態は変数 `x` についてだけ更新される。
  `x` の値は、式 `a` を状態 `s` において評価したものに変わる。 -/
  | assign (x : Variable)(a : State → Nat)(s : State) : BigStep (assign x a, s) (s[x ↦ a s])

  /-- seq コマンドの意味論。
  コマンド `S` により状態が `s` から `t` に変わり、 コマンド `T` により状態が `t` から `u` に変わるのであれば、
  コマンド `S; T` により状態は `s` から `u` に変わる。-/
  | seq (S T : Stmt)(s t u : State) (hS : BigStep (S, s) t) (hT : BigStep (T, t) u):
    BigStep (S; T, s) u

  /-- if 文の、条件式が true のときの意味論。
  コマンド `S` により状態が `s` から `t` に変わり、かつ条件式が真であるとき
  `ifThenElse B S T` により状態は `s` から `t` に変わる。 -/
  | if_true (B : State → Prop)(S T : Stmt)(s t : State) (hcond : B s) (hbody : BigStep (S, s) t) :
    BigStep (ifThenElse B S T, s) t

  /-- if 文の、条件式が false のときの意味論。
  コマンド `T` により状態が `s` から `t` に変わり、かつ条件式が偽であるとき
  `ifThenElse B S T` により状態は `s` から `t` に変わる。 -/
  | if_false (B : State → Prop)(S T : Stmt)(s t : State) (hcond : ¬ B s) (hbody : BigStep (T, s) t) :
    BigStep (ifThenElse B S T, s) t

  /-- while 文の、条件式が真のときの意味論。
  * 前提1: コマンド `S` により状態が `s` から `t` に変わり、
  * 前提2: かつ `whileDo B S` により状態が `t` から `u` に変わるのであれば、
  * 帰結: `whileDo B S` により状態は `s` からスタートさせても `u` に変わる。

  #### 例
  たとえば `while x < 10 do x := x + 1` というプログラムを考えて、
  状態をそれぞれ `s := [x ↦ 3]`, `t := [x ↦ 4]`, `u := [x ↦ 10]` としてみると具体例になる。

  #### 補足
  `while_true` の評価は「終わらないかもしれない」ものである必要がある。だから `BigStep` を再帰関数ではなく帰納的命題として定義する必要があった。
  -/
  | while_true (B S s t u) (hcond : B s) (hbody : BigStep (S, s) t) (hrest : BigStep (whileDo B S, t) u) :
    BigStep (whileDo B S, s) u

  /-- while 文の、条件式が偽のときの意味論。条件文 `B` が偽のとき、コマンド `S` の内容に関わらず、
  コマンド `whileDo B S` は状態を変化させない。-/
  | while_false (B S s) (hcond : ¬ B s) : BigStep (whileDo B S, s) s
def hello := "world"
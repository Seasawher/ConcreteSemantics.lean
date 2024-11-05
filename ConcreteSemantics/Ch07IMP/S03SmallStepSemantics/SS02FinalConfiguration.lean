import ConcreteSemantics.Ch07IMP.S03SmallStepSemantics.SS01EquivalenceWithBigStep

/--
`final (S, s)` は `(S, s)` がこれ以上評価を進めることができないことを表す.
IMPでは `S = skip` に限られるが, より複雑な言語では `1 + true` のような例がある.
-/
def final (S : Stmt) (s : State) : Prop :=
  ¬ ∃ S' s', (S, s) ⇒ (S', s')

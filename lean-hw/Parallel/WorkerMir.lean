namespace ParallelWorkerMir

/-- A block in the normalized normal-return MIR. The label identifies its complete
sequence of operations, including the terminator and its ordered branch cases. -/
structure Block where
  ops : Nat
  successors : List Nat
  deriving DecidableEq

abbrev Graph := List Block

/-- The interpreter supplies the meaning of a block's operations, including
the branch taken, cell effects and state change. A path can end at any prefix. -/
inductive Run {S E : Type} (eval : Nat → S → Nat → List E → S → Prop)
    (graph : Graph) : Nat → S → List E → Nat → S → Prop where
  | stop (pc s) : Run eval graph pc s [] pc s
  | step {pc s b choice effects s' next rest finish final}
      (fetch : graph[pc]? = some b)
      (exec : eval b.ops s choice effects s')
      (jump : b.successors[choice]? = some next)
      (tail : Run eval graph next s' rest finish final) :
      Run eval graph pc s (effects ++ rest) finish final

theorem same_runs {left right : Graph} (checked : left = right)
    {S E : Type} (eval : Nat → S → Nat → List E → S → Prop)
    (pc : Nat) (s : S) (log : List E) (finish : Nat) (final : S) :
    Run eval left pc s log finish final ↔ Run eval right pc s log finish final := checked ▸ Iff.rfl

end ParallelWorkerMir

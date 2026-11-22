import Ideal.Direct.Engine
import Ideal.Core.HPTable

/-!
# The toy game of the direct proof (milestone M0 of `status/DIRECT.md`)

A random compression table `g : St × Blk → St` (lazily sampled), a public chaining value `cv`,
an output map `out : St → Y` (the 128-bit truncation), one secret `k : K`, and `m` hash chains of
length `w`:

`v a 0 = out (g (cv, P a k))`,  `v a (j+1) = out (g (cv, F a j (v a j)))`.

The adversary has compression queries and adaptive reveal queries `reveal (a, b)` (answer
`v a (min b w)`; any number per chain).  It wins with `(a, j, x)` if `j` is below every revealed
position of chain `a` and the chain from `x` at position `j` reaches `v a w`, the chain from `x`
being evaluated by the experiment over the same table.

The block maps `P` (a "PRF" block, keyed by the secret) and `F` (a "chain" block, keyed by the
tweak `(a, j)` and the input) are injective and disjoint; this is expressed by a parser
`parse : Blk → Shape` that recognises them.

* `Params`: the parameters; `Params.realWin T A`: the winning probability, as the lazy-table
  experiment `(simulateQ romImpl (realProg A)).run' ∅`.
* The deferred game (`H2`, `walkX`, `compX`, `G2P`): the same adversary against a table in which
  the honest cells are replaced by an independent table `s` of honest values that is read only at
  revealed positions; the secret `k` is drawn by a third lazy table.  Its output is the event
  `Efin` (a hidden value guessed, the secret guessed, a hit on an honest value, or the forged
  value equal to a hidden value).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.Direct.Toy

/-- What a message block is: the secret-keyed block of chain `a`, the chain block of chain `a`
at position `j` with input `x`, or anything else. -/
inductive Shape (m : ℕ) (K Y : Type) where
  | key (a : Fin m) (k : K)
  | chn (a : Fin m) (j : ℕ) (x : Y)
  | other

/-- Parameters of the toy game. -/
structure Params (St Blk K Y : Type) where
  /-- number of chains -/
  m : ℕ
  /-- chain length -/
  w : ℕ
  /-- the public chaining value -/
  cv : St
  /-- the output truncation -/
  out : St → Y
  /-- the secret-keyed block of chain `a` -/
  P : Fin m → K → Blk
  /-- the chain block of chain `a` at position `j` with input `x` -/
  F : Fin m → ℕ → Y → Blk
  /-- recognises the two block shapes -/
  parse : Blk → Shape m K Y
  parse_key : ∀ b a k, parse b = .key a k ↔ b = P a k
  parse_chn : ∀ b a j x, parse b = .chn a j x ↔ b = F a j x

namespace Params

variable {St Blk K Y : Type} (T : Params St Blk K Y)

theorem parse_P (a : Fin T.m) (k : K) : T.parse (T.P a k) = .key a k :=
  (T.parse_key _ a k).2 rfl

theorem parse_F (a : Fin T.m) (j : ℕ) (x : Y) : T.parse (T.F a j x) = .chn a j x :=
  (T.parse_chn _ a j x).2 rfl

/-- Clamp a reveal position to the chain. -/
def cl (b : ℕ) : ℕ := min b T.w

/-- A chain position as an index of the honest-value table. -/
def ix (j : ℕ) : Fin (T.w + 1) := ⟨min j T.w, by omega⟩

/-- The lowest revealed position of every chain after revealing `(a, b)`. -/
def rUpd (r : Fin T.m → ℕ) (a : Fin T.m) (b : ℕ) : Fin T.m → ℕ :=
  Function.update r a (min (r a) (T.cl b))

/-- Index of the honest-value table: a chain and a position. -/
abbrev HIdx := Fin T.m × Fin (T.w + 1)

/-- Nothing revealed. -/
def r0 : Fin T.m → ℕ := fun _ => T.w + 1

/-- The reveal oracle. -/
abbrev revS : OracleSpec (Fin T.m × ℕ) := (Fin T.m × ℕ) →ₒ Y

/-- The adversary's interface: coins, compression queries, reveals. -/
abbrev advSpec := unifSpec + (hS St Blk + T.revS)

/-- The adversary's compression queries. -/
def isHash : ℕ ⊕ ((St × Blk) ⊕ (Fin T.m × ℕ)) → Bool
  | .inr (.inl _) => true
  | _ => false

/-! ## The real game -/

/-- The honest chain of chain `a` up to position `j`, by compression queries; returns the full
chaining value of the last cell. -/
def chainQ (k : K) (a : Fin T.m) : ℕ → OracleComp (unifSpec + hS St Blk) St
  | 0 => (unifSpec + hS St Blk).query (.inr (T.cv, T.P a k))
  | j + 1 => do
      let u ← chainQ k a j
      (unifSpec + hS St Blk).query (.inr (T.cv, T.F a j (T.out u)))

/-- The chain from `x` at position `j`, `n` steps, by compression queries. -/
def walkQ (a : Fin T.m) : ℕ → ℕ → Y → OracleComp (unifSpec + hS St Blk) Y
  | _, 0, x => pure x
  | j, n + 1, x => do
      let u ← (unifSpec + hS St Blk).query (.inr (T.cv, T.F a j x))
      walkQ a (j + 1) n (T.out u)

/-- The real game's handler: compression queries go to the table, a reveal computes the honest
chain by compression queries; the state is the lowest revealed position of every chain. -/
def realImpl (k : K) :
    QueryImpl T.advSpec (StateT (Fin T.m → ℕ) (OracleComp (unifSpec + hS St Blk))) := fun
  | .inl n => StateT.mk fun r =>
      (fun u => (u, r)) <$> (liftM ((unifSpec + hS St Blk).query (.inl n)) :
        OracleComp (unifSpec + hS St Blk) (Fin (n + 1)))
  | .inr (.inl q) => StateT.mk fun r =>
      (fun u => (u, r)) <$> (liftM ((unifSpec + hS St Blk).query (.inr q)) :
        OracleComp (unifSpec + hS St Blk) St)
  | .inr (.inr ab) => StateT.mk fun r =>
      (fun u => (T.out u, T.rUpd r ab.1 ab.2)) <$> T.chainQ k ab.1 (T.cl ab.2)

variable [SampleableType K] [DecidableEq Y]

/-- The real experiment as a program over the table. -/
def realProg (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) :
    OracleComp (unifSpec + hS St Blk) Bool := do
  let k ← (liftM ($ᵗ K : ProbComp K) : OracleComp (unifSpec + hS St Blk) K)
  let z ← (simulateQ (T.realImpl k) A).run T.r0
  let y ← T.walkQ z.1.1 z.1.2.1 (T.w - z.1.2.1) z.1.2.2
  let v ← T.chainQ k z.1.1 T.w
  pure (decide (z.1.2.1 < z.2 z.1.1 ∧ y = T.out v))

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-- **The toy game's winning probability**, over the lazily sampled table. -/
noncomputable def realWin (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) : ℝ≥0∞ :=
  HP.prT ((simulateQ (hS St Blk).romImpl (T.realProg A)).run' ∅)

end Params

end Ideal.Direct.Toy

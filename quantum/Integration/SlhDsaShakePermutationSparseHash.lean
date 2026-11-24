import Integration.SlhDsaShakePermutationSparsePhase

/-! The phase-one program for an actual tweakable SHAKE hash, including
messages of arbitrary arity and arbitrarily many absorbed blocks. -/
namespace Reduction.ShakePermutation.SparsePort.Phase
open Classical SetOracle OracleComp OracleSpec SLHDSA MLink ShakeXof
noncomputable section
variable (S : Sha2Set) (pk : S.Node) (ar : ℕ) (bound : ar ≤ 2)

def absorb {T : Type} (d : T) (w : Words) : List Rate → OracleComp (Tagged T) Words
  | [] => pure w
  | r :: rs => do
    let y ← (Tagged T).query (.inr (d,join (rateXor r (rateOf w)) (capOf w)))
    absorb d y rs

def evalHash (d : Bytes 32) (xs : List S.Node) : OracleComp (Tagged (Bytes 32)) S.Node := do
  let w ← absorb d 0 (messageBlocks (sp (thBytes S pk d xs)))
  pure (SkFormat.split S w).1

private theorem later (d : Bytes 32) (rs : List Rate) (w : Words) (h : ¬Trace.zeroCap w) :
    valid (Arity.input S ar pk bound) Prod.fst (absorb d w rs) := by
  induction rs generalizing w with
  | nil => trivial
  | cons r rs ih =>
    constructor
    · intro j eq
      exact False.elim (Arity.later_miss S pk ar bound w _ h j eq)
    · exact fun y hy => ih y hy

theorem evalHash_valid (d : Bytes 32) (xs : List S.Node) :
    valid (Arity.input S ar pk bound) Prod.fst (evalHash S pk d xs) := by
  unfold evalHash
  apply valid_bind
  swap
  · intro r; trivial
  unfold messageBlocks
  rw [List.ofFn_succ]
  constructor
  · intro j eq
    apply Arity.first_tweak S pk ar bound d xs j
    apply eq.trans
    apply congrArg₂ join _ rfl
    funext i
    exact UInt64.xor_zero
  · exact fun y hy => later S pk ar bound d _ y hy

private theorem run_absorb {T : Type} (f : T → Words → Words) (d : T)
    (ev : Words → ENNReal) (w : Words) (rs : List Rate) :
    run f ev (absorb d w rs) =
      ev (rs.foldl (fun z r => f d (join (rateXor r (rateOf z)) (capOf z))) w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem run_bind {T α β : Type} (f : T → Words → Words) (ev : β → ENNReal)
    (p : OracleComp (Tagged T) α) (k : α → OracleComp (Tagged T) β) :
    run f ev (p >>= k) = run f (fun r => run f ev (k r)) p := by
  induction p using OracleComp.inductionOn with
  | pure x => rw [pure_bind]; rfl
  | query_bind i g ih =>
    rw [bind_assoc]
    rcases i with n|⟨d,w⟩
    · exact congrArg uniformMean (funext ih)
    · exact ih _

theorem run_hash (π : Permutation) (d : Bytes 32) (xs : List S.Node) (ev : S.Node → ENNReal) :
    run (fun _ : Bytes 32 => π) ev (evalHash S pk d xs) =
      ev ((primitives (lanes π) S.vp.params).Thash pk d xs) := by
  simp only [evalHash,run_bind,run_absorb]
  apply congrArg ev
  change (SkFormat.split S (Fix.ordinary π _)).1 = hash (lanes π) (nd pk ++ nd d ++ nds xs) S.vp.params.n
  rw [← Arity.fmt S pk,← hash_prefix,answer_blocks,← head_eq_prefix (node_le_digest S),SkFormat.split_fst]
  apply Vector.ext; intro i hi; simp [head]

theorem run_hash_local {J Y Z : Type} (e : Words ≃ Y × Z) (a : J ↪ Words)
    (π : Permutation) (s : J → Z) (tag : J → Bytes 32) (F G : J → Y)
    (d : Bytes 32) (xs : List S.Node) (ev : S.Node → ENNReal)
    (h : ∀ j, tag j = d → F j = G j) :
    run (shadow e a π s tag F) ev (evalHash S pk d xs) =
      run (shadow e a π s tag G) ev (evalHash S pk d xs) := by
  simp only [evalHash,run_bind,run_absorb]
  simp only [shadow_local e a π s tag F G d _ h]
  rfl

end
end Reduction.ShakePermutation.SparsePort.Phase
#print axioms Reduction.ShakePermutation.SparsePort.Phase.evalHash_valid
#print axioms Reduction.ShakePermutation.SparsePort.Phase.run_hash

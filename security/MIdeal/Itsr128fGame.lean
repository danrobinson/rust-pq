import MIdeal.Itsr128f
import Ideal.Inst.Itsr128

namespace MIdeal.Hmsg.Fast128
open MLink Ideal Ideal.Itsr Ideal.HP SLHDSA SLHDSA.Concrete OracleComp OracleSpec KeyedHash

abbrev Key := Bytes 16
abbrev Msg := Bytes 16 × Bytes 16 × List Byte
abbrev Prog := OracleComp (unifSpec + mS St Blk)

def hash (x : Input) : Prog (Bytes 34) := do
  let s ← mdMF IV128 (innerBlocks x)
  let row ← cq IV128 (counterPrefix x.1 x.2.1 s) true
  let a ← cq row (counterFinal 0) true
  let b ← cq row (counterFinal 1) true
  pure (digest128f (a,b))

theorem hash_at (g : CF St Blk) (x : Input) :
    simulateQ (markImpl g) (hash x) = pure (rowDigest g (g (prefixCell g x))) := by
  simp only [hash, simulateQ_bind, simulateQ_mdMF, simulateQ_cq, pure_bind, simulateQ_pure]
  rfl

theorem hash_count (x : Input) :
    IsQueryBoundP (hash x) (fun i => i.isRight = true) ((x.2.2.2.length + 56)/64 + 4) := by
  unfold hash
  have len : (innerBlocks x).length = (x.2.2.2.length + 56)/64 + 1 := iblocksH_length _ _ _ _
  rw [show (x.2.2.2.length + 56)/64 + 4 = (innerBlocks x).length + 3 by omega]
  apply isQueryBoundP_bind (mdMF_bound _ _)
  intro s _
  apply isQueryBoundP_cq_bind_succ
  intro row
  apply isQueryBoundP_cq_bind_succ
  intro a
  exact isQueryBoundP_cq_bind_succ _ _ _ _ 0 (fun _ => by simp)

def hashes : List Input → Prog (List (Bytes 34))
  | [] => pure []
  | x :: xs => do
    let v ← hash x
    let vs ← hashes xs
    pure (v :: vs)

theorem hashes_at (g : CF St Blk) (xs : List Input) :
    simulateQ (markImpl g) (hashes xs) = pure (xs.map (fun x => rowDigest g (g (prefixCell g x)))) := by
  induction xs with
  | nil => simp [hashes]
  | cons x xs ih => simp only [hashes, simulateQ_bind, hash_at, pure_bind, ih, simulateQ_pure, List.map_cons]

def finish (z : Input × List Input) : Prog Bool := do
  let ds ← hashes z.2
  let d ← hash z.1
  pure (decide (z.1 ∉ z.2 ∧ ∀ i ∈ idxOf Sha2Set.s128f.vp d, i ∈ ds.flatMap (idxOf Sha2Set.s128f.vp)))

def game (A : ItsrAdvI St Blk Key Msg) : Prog Bool :=
  (simulateQ tgtImpl A).run [] >>= finish

def lengthOK (L : ℕ) (x : Input) := x.2.2.2.length ≤ L

theorem hash_count_limit {x : Input} {L : ℕ} (h : lengthOK L x) :
    IsQueryBoundP (hash x) (fun i => i.isRight = true) ((L+56)/64 + 4) := by
  apply (hash_count x).mono
  unfold lengthOK at h
  omega

theorem hashes_count (xs : List Input) (L : ℕ) (hs : ∀ x ∈ xs, lengthOK L x) :
    IsQueryBoundP (hashes xs) (fun i => i.isRight = true) (xs.length * ((L+56)/64 + 4)) := by
  induction xs with
  | nil => simp [hashes]
  | cons x xs ih =>
    unfold hashes
    apply (isQueryBoundP_bind (hash_count_limit (hs x (by simp))) (fun v _ =>
      isQueryBoundP_bind (m := 0) (ih fun t h => hs t (by simp [h])) (fun vs _ => by simp))).mono
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_zero]
    omega

theorem game_count (A : OracleComp (unifSpec + (hS St Blk + ITSRTargetSpec Msg Key)) Input) (q qs L : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompI i = true) q)
    (hs : IsQueryBoundP A (fun i => isTgtI i = true) qs)
    (ht : AllQueriesSatisfy A (tgtOK (lengthOK L))) (ho : ∀ x ∈ support A, lengthOK L x) :
    IsQueryBoundP (game A) (fun i => i.isRight = true) (q + (qs + 1) * ((L+56)/64 + 4)) := by
  apply targetRun_bound (fun n => by simp) _ (lengthOK L) finish _ A q qs [] hq hs ht ho (by simp)
  intro x s hx hs'
  unfold finish
  apply (isQueryBoundP_bind (hashes_count s L hs') (fun ds _ =>
    isQueryBoundP_bind (m := 0) (hash_count_limit hx) (fun d _ => by simp))).mono
  simp [Nat.add_mul]

noncomputable section
local instance (g : CompressionTables) : SampleableType (tablePrimitives g Sha2Set.s128f.vp.params).Y :=
  inferInstanceAs (SampleableType Key)

theorem game_eq (g : CompressionTables) (A : ItsrAdvI St Blk Key Msg) :
    simulateQ (markImpl g.1) (game A) =
      ITSRExperiment (A.inst (Reduction.itsrProblem Sha2Set.s128f.vp (tablePrimitives g Sha2Set.s128f.vp.params)) g.1) := by
  let prob := Reduction.itsrProblem Sha2Set.s128f.vp (tablePrimitives g Sha2Set.s128f.vp.params)
  have run : (simulateQ (ITSROracles prob) (simulateQ (instImpl g.1) A)).run [] =
      simulateQ (markImpl g.1) ((simulateQ tgtImpl A).run []) := by
    exact run_tgt_eq (Index := Unit) IV128 innerBlocks (fun _ _ => []) id (fun _ => []) g.1 A []
  simp only [game, finish, simulateQ_bind, hashes_at, hash_at, pure_bind, simulateQ_pure,
    ITSRExperiment, ITSRAdversary.run, ItsrAdvI.inst]
  rw [← run]
  refine bind_congr fun z => ?_
  apply congrArg pure
  apply decide_eq_decide.mpr
  have hidx : prob.indexSet = (fun x : Input => idxOf Sha2Set.s128f.vp (rowDigest g.1 (g.1 (prefixCell g.1 x)))) := by
    funext x
    exact congrArg (idxOf Sha2Set.s128f.vp) (hmsg_128f_cells g x.1 x.2.1 x.2.2.1 x.2.2.2)
  change _ ↔ z.1 ∉ z.2 ∧ ∀ i ∈ prob.indexSet z.1, i ∈ z.2.flatMap prob.indexSet
  rw [hidx]
  have lists (l : List Input) : (l.map (fun x => rowDigest g.1 (g.1 (prefixCell g.1 x)))).flatMap
      (idxOf Sha2Set.s128f.vp) = l.flatMap (fun x => idxOf Sha2Set.s128f.vp (rowDigest g.1 (g.1 (prefixCell g.1 x)))) := by
    induction l with
    | nil => rfl
    | cons x l ih => exact congrArg (List.append _) ih
  rw [lists]
  exact Iff.rfl

end
end MIdeal.Hmsg.Fast128

#print axioms MIdeal.Hmsg.Fast128.game_eq
#print axioms MIdeal.Hmsg.Fast128.hash_count

#print axioms MIdeal.Hmsg.Fast128.game_count

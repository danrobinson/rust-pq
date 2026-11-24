import Integration.SlhDsaShakePermutationLongSelectHistory

/-! Reading target digests from the classical selection transcript fixes one search goal for all posterior permutations. -/
namespace Reduction.ShakePermutation.Long.SelectTrace
open Classical Classic SparsePort OracleSpec OracleComp MLink SLHDSA PermutationConditioning PQ.Interactive
noncomputable section
set_option maxRecDepth 8192
variable (S : Sha2Set) (pk : S.Node) (ar : ℕ)

private def accepted (l : List (Arity.Row S ar)) (t : Trace) (d : Bytes 32) (r : Arity.Msg S ar × Words) :=
  (d,r.1) ∈ l ∧ Trail t (blocks S pk d r.1.val) r.2

def targetMap (l : List (Arity.Row S ar)) (t : Trace) : Targets S ar := fun d =>
  if h : ∃ r, accepted S pk ar l t d r then some (h.choose.1,(SkFormat.split S h.choose.2).1) else none

theorem safe {h t L} (ok : Ledger S pk ar h t L) :
    ¬bad (SkFormat.split S) (goal S pk ar (targetMap S pk ar h.1 t)) t := by
  apply initially_clear S pk ar _ L t ok.paths ok.cover
  intro d m v hit xs logged
  unfold targetMap at hit
  split at hit
  next yes =>
    obtain ⟨hm,_⟩ := Prod.mk.inj (Option.some.inj hit)
    exact hm ▸ ok.messages (d,yes.choose.1) yes.choose_spec.1 xs logged
  next => contradiction

def row (π : Permutation) (j : Arity.Row S ar) : S.Node :=
  (SkFormat.split S (Fix.ordinary π (blocks S pk j.1 j.2.val))).1

theorem row_native (π : Permutation) (j : Arity.Row S ar) : row S pk ar π j =
    (primitives (lanes π) S.vp.params).Thash pk j.1 j.2.val := Select.value_actual S π pk j.1 j.2.val

def path (l : List (Arity.Row S ar)) (jm : ℕ × Arity.Msg S ar) := blocks S pk (tweakAt l jm.1) jm.2.val

theorem path_length (h : ar ≤ 67) (l : List (Arity.Row S ar)) (jm : ℕ × Arity.Msg S ar) :
    (path S pk ar l jm).length ≤ 17 := by
  unfold path blocks
  rw [messageBlocks_length]
  have n : S.vp.params.n ≤ 32 := by cases S <;> decide
  have m := Nat.mul_le_mul n (jm.2.property.le.trans h)
  simp only [sp,List.length_map,ShakeXof.thBytes,List.length_append,Vector.length_toList,MIdeal.Sha512.payload_length]
  omega

theorem winner {h t L} (ok : Ledger S pk ar h t L) (π : Extensions t) (jm : ℕ × Arity.Msg S ar)
    (win : PQ.Interactive.tcrWin h.1 (row S pk ar π.val) jm) :
    goal S pk ar (targetMap S pk ar h.1 t) (path S pk ar h.1 jm) =
      some (SkFormat.split S (Fix.ordinary π.val (path S pk ar h.1 jm))).1 := by
  obtain ⟨⟨d,m⟩,idx,ne,eq⟩ := win
  have mem := List.mem_of_getElem? idx
  obtain ⟨w,trail⟩ := ok.target _ mem
  have yes : ∃ r, accepted S pk ar h.1 t d r := ⟨(m,w),mem,trail⟩
  have msg : yes.choose.1=m := Subtype.ext (ok.messages (d,m) mem _ (ok.logged _ yes.choose_spec.1))
  have val := yes.choose_spec.2.eval π.val (fun x y he => π.property (x,y) he)
  have mv : row S pk ar π.val (d,m) = (SkFormat.split S yes.choose.2).1 := by
    rw [← msg]; exact congrArg (fun z => (SkFormat.split S z).1) val
  have lookup : targetMap S pk ar h.1 t d = some (m,row S pk ar π.val (d,m)) := by simp only [targetMap,dite_eq_left yes,msg,mv]
  have addr : tweakAt h.1 jm.1 = d := by simp [tweakAt,idx]
  simp only [path,addr]
  exact (goal_candidate S pk ar _ d jm.2 m _ lookup ne).trans (congrArg some eq.symm)
end
end Reduction.ShakePermutation.Long.SelectTrace
#print axioms Reduction.ShakePermutation.Long.SelectTrace.winner

import Integration.SlhDsaShakePermutationLongBankHistory
import Integration.SlhDsaShakePermutationLongTargetEndpoint
import Integration.SlhDsaShakePermutationLongBankRisk

namespace Reduction.ShakePermutation.Long.BankRun
open Classical ItsrLabel SparsePort MLink SLHDSA Tails PQ.Interactive
noncomputable section
set_option maxRecDepth 11000
set_option maxHeartbeats 1500000

theorem fix_first (f : List Rate → Rate) (xs : List Rate) : (Fix.fix f xs).head? = xs.head? := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    rw [Fix.fix_append]
    cases xs with
    | nil => rfl
    | cons a bs =>
      cases h : Fix.fix f (a::bs) with
      | nil => simp [h] at ih
      | cons r rs => simpa only [List.cons_append,List.head?_cons,h] using ih

theorem overwrite_eq (π : Permutation) (H : Table) (p : List Rate) :
    (report π H p).path.reverse = Fix.fix (rateOf ∘ Fix.overwrite (perm π H)) p := by
  simpa only [report,List.reverse_reverse] using Target.replay_overwrite π H p.reverse

theorem result_eq (π : Permutation) (H : Table) (p : List Rate) :
    result (report π H p) = Fix.ordinary (perm π H) p := by
  simpa only [report,List.reverse_reverse] using replay_result π H p.reverse

theorem known_congr (π : Permutation) {H F : Table} {D : Bank} (pin : Pins D F) {p : List Rate}
    (known : Known π H D p) : report π F p = report π H p := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p b ih =>
    let w := report π H p
    let r := rateXor b (rateOf (result w))
    let a := H (ItsrLabel.mask false r)
    let mid := (layout π).middle r w.cap (capOf a)
    let v := H (ItsrLabel.mask true mid.1)
    let z := (layout π).finish mid.2 (capOf v)
    unfold Known at known
    rw [report_snoc] at known
    change Matches D ((ItsrLabel.mask false r,a)::(ItsrLabel.mask true mid.1,v)::(tailHead z,H (tailHead z))::w.log) at known
    have prev : Known π H D p := fun i y h => known i y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
    have eq₁ := pin _ a (known (ItsrLabel.mask false r) a (by simp))
    have eq₂ := pin _ v (known (ItsrLabel.mask true mid.1) v (by simp))
    have eq₃ := pin _ (H (tailHead z)) (known (tailHead z) (H (tailHead z)) (by simp))
    rw [report_snoc,report_snoc,ih prev]
    unfold step
    change push π w b (F (ItsrLabel.mask false r)) _ _ = push π w b a v (H (tailHead z))
    rw [eq₁]
    change push π w b a (F (ItsrLabel.mask true mid.1)) _ = _
    rw [eq₂]
    exact congrArg (push π w b a v) eq₃

theorem same_tweak (S : Sha2Set) (pk : S.Node) (d e : Bytes 32) (xs ys : List S.Node)
    (he : (Long.blocks S pk d xs).head? = (Long.blocks S pk e ys).head?) : d=e := by
  simp only [Long.blocks,messageBlocks,List.ofFn_succ,List.head?_cons,Option.some.injEq] at he
  apply Vector.ext; intro i hi
  let w : Fin 32 := ⟨i,hi⟩
  have byte := congrArg (fun r => blockByte r ⟨S.vp.params.n+w.val,by
    have : S.vp.params.n ≤ 32 := by cases S <;> decide
    omega⟩) he
  exact UInt8.toBitVec_inj.mp ((Arity.tweak_byte S pk d xs w).symm.trans (byte.trans (Arity.tweak_byte S pk e ys w)))

theorem same_length (S : Sha2Set) (pk : S.Node) (ar : ℕ) (e d : Bytes 32) (a b : Arity.Msg S ar) :
    (Long.blocks S pk e a.val).length = (Long.blocks S pk d b.val).length := by
  simp only [Long.blocks,messageBlocks_length,sp,List.length_map,ShakeXof.thBytes,List.length_append,Vector.length_toList,
    MIdeal.Sha512.payload_length,a.property,b.property]

end
end Reduction.ShakePermutation.Long.BankRun

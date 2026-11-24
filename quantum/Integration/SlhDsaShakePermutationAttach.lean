import Integration.SlhDsaShakePermutationRegular

namespace Reduction.ShakePermutation
open Classical

/-- Candidate rate/capacity pairs awaiting a fresh capacity mask value.
An attach occurs if one of their updated images hits a forbidden rate. -/
def badAttach (π : Permutation) (pending : Finset (Rate × Capacity)) (forbidden : Finset Rate) :
    Finset Capacity := pending.biUnion fun xz => forbidden.biUnion fun s =>
      (Finset.univ.filter fun c : Capacity => rateOf (π (join xz.1 c)) = s).image
        (fun c => fun i => c i ^^^ xz.2 i)

theorem mem_badAttach (π : Permutation) (pending : Finset (Rate × Capacity)) (forbidden : Finset Rate) (y : Capacity) :
    y ∈ badAttach π pending forbidden ↔
      ∃ p ∈ pending, rateOf (π (join p.1 (fun i => y i ^^^ p.2 i))) ∈ forbidden := by
  classical
  simp only [badAttach,Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp,s,hs,c,he,rfl⟩
    exact ⟨p,hp,by simpa only [UInt64.xor_assoc,UInt64.xor_self,UInt64.xor_zero,he] using hs⟩
  · rintro ⟨p,hp,hs⟩
    refine ⟨p,hp,_,hs,fun i => y i ^^^ p.2 i,rfl,?_⟩
    funext i
    simp [UInt64.xor_assoc]

theorem badAttach_card (π : Permutation) (hπ : ¬irregular π)
    (pending : Finset (Rate × Capacity)) (forbidden : Finset Rate) :
    (badAttach π pending forbidden).card ≤ pending.card * forbidden.card * 4 := by
  classical
  have h (p : Rate × Capacity) (s : Rate) :
      ((Finset.univ.filter fun c : Capacity => rateOf (π (join p.1 c)) = s).image
        (fun c => fun i => c i ^^^ p.2 i)).card ≤ 4 := by
    apply Finset.card_image_le.trans
    simpa only [slice,Fintype.card_subtype] using slice_card π hπ p.1 s
  calc
    _ ≤ ∑ p ∈ pending, ∑ s ∈ forbidden, ((Finset.univ.filter fun c : Capacity =>
      rateOf (π (join p.1 c)) = s).image (fun c => fun i => c i ^^^ p.2 i)).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ _p ∈ pending, ∑ _s ∈ forbidden, 4 :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun s _ => h p s
    _ = _ := by simp [Nat.mul_assoc]

/-- Conditional count in a good database with at most t entries in each
mask table. There are at most t+1 pending tails for a new left query,
t(t+1) intermediate rates and t queried right rates. -/
theorem badAttach_step (π : Permutation) (hπ : ¬irregular π)
    (pending : Finset (Rate × Capacity)) (forbidden : Finset Rate) (t : Nat)
    (hp : pending.card ≤ t+1) (hf : forbidden.card ≤ t*(t+1)+t) :
    (badAttach π pending forbidden).card ≤ 4*(t+1)*(t*(t+1)+t) := by
  obtain h := (badAttach_card π hπ pending forbidden).trans
    (Nat.mul_le_mul_right 4 (Nat.mul_le_mul hp hf))
  simpa only [Nat.mul_comm 4 _,Nat.mul_assoc] using h

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.badAttach_step

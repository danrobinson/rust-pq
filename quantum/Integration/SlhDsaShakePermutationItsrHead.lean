import Integration.SlhDsaShakePermutationItsrLabel
import Integration.SlhDsaShakePermutationClassicalPublicRisk
import Integration.SlhDsaShakePermutationManifest

namespace Reduction.ShakePermutation.ItsrLabel
open Classical Tails MLink SLHDSA Classic SetOracle ENNReal
set_option maxRecDepth 9000
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local irreducible] Graph.support Fintype.card
noncomputable section

def preHead (π : Permutation) (L : ℕ) (k k' : Db) (z : Capacity) : Rate :=
  ((Relabel.chosen π k k' L z).map Prod.snd).getD (fun _ => 0)

def targets (S : Sha2Set) (π : Permutation) (L : ℕ) (k k' : Db) (h : Heads) : Finset (ShakeSingle.Decoded S) :=
  (Graph.support h).image fun z => key S (preHead π L k k' z) ((h z).getD (fun _ => 0))

theorem targets_card (S π L k k' h) : (targets S π L k k' h).card ≤ (Graph.support h).card :=
  Finset.card_image_le

set_option allowUnsafeReducibility true in
attribute [local irreducible] key Good Seen preHead targets

theorem seen_key {S : Sha2Set} {π : Permutation} {L : ℕ} {k k' : Db} {h : Heads} {z : Capacity} {d : ShakeSingle.Decoded S} (graph : Graph.Good (layout π) k k')
    (s : Seen S π L k k' h z d) :
    z ∈ Graph.support h ∧ key S (preHead π L k k' z) ((h z).getD (fun _ => 0)) = d := by
  unfold Seen at s
  obtain ⟨p,r,y,visit,hy,hd⟩ := s
  exact ⟨(Graph.mem_support h z).mpr (Option.isSome_iff_exists.mpr ⟨y,hy⟩),
    by simpa only [preHead,Relabel.chosen_of_visit π k k' graph visit,hy,Option.map_some,Option.getD_some] using hd⟩

theorem mem_targets {S : Sha2Set} {π : Permutation} {L : ℕ} {k k' : Db} {h : Heads} {z : Capacity} {d : ShakeSingle.Decoded S} (graph : Graph.Good (layout π) k k')
    (s : Seen S π L k k' h z d) : d ∈ targets S π L k k' h :=
  by
    obtain ⟨mem,eq⟩ := seen_key graph s
    unfold targets
    exact Finset.mem_image.mpr ⟨z,mem,eq⟩

theorem good_head {S : Sha2Set} {π : Permutation} {L : ℕ} {k k' : Db} {h : Heads} {x : Capacity} {y : Rate} (g : Good S π L k k' h)
    (miss : key S (preHead π L k k' x) y ∉ targets S π L k k' h) :
    Good S π L k k' (Function.update h x (some y)) := by
  unfold Good at g ⊢
  have back {z d} (ne : z ≠ x) (s : Seen S π L k k' (Function.update h x (some y)) z d) :
      Seen S π L k k' h z d := by
    unfold Seen at s ⊢
    obtain ⟨p,r,v,hp,hv,hd⟩ := s
    exact ⟨p,r,v,hp,(Function.update_of_ne ne ..).symm.trans hv,hd⟩
  have at_x {d} (s : Seen S π L k k' (Function.update h x (some y)) x d) :
      key S (preHead π L k k' x) y = d := by
    simpa only [Function.update_self,Option.getD_some] using (seen_key g.1 s).2
  refine ⟨g.1,fun z w d a b => ?_⟩
  by_cases hz : z = x
  · subst z
    by_contra ne
    exact miss ((at_x a).symm ▸ mem_targets g.1 (back (Ne.symm ne) b))
  · by_cases hw : w = x
    · subst w
      exact False.elim (miss ((at_x b).symm ▸ mem_targets g.1 (back hz a)))
    · exact g.2 z w d (back hz a) (back hw b)

private theorem prefix_mean {n m : ℕ} (hb : n ≤ m) (f : Bytes n → ℝ≥0∞) :
    uniformMean (fun v : Bytes m => f (ShakeXof.head hb v)) = uniformMean f := by
  have swap : Function.Involutive (fun z : Bytes m × Bytes n =>
      (ShakeXof.replaceHead z.1 z.2,ShakeXof.head hb z.1)) := by
    rintro ⟨u,v⟩
    exact Prod.ext (ShakeXof.replace_undo hb _ _) (ShakeXof.head_replace hb _ _)
  have h := SetOracle.avg_resample ShakeXof.replaceHead (ShakeXof.head hb) swap (fun v => f (ShakeXof.head hb v))
  exact h.trans (by simp only [ShakeXof.head_replace]; exact Classic.avg_const (U := Bytes m) (uniformMean f))

private theorem digest_mean (S : Sha2Set) (B : Finset (ShakeSingle.Decoded S)) :
    uniformMean (fun y : Bytes S.vp.params.m => Classic.hit (DigestTransport.coveringDigest S.vp y ∈ B)) =
      (B.card : ℝ≥0∞)/2^(S.vp.params.h+S.vp.params.a*S.vp.params.k) := by
  let D := Finset.univ.filter (fun y : Bytes S.vp.params.m => DigestTransport.coveringDigest S.vp y ∈ B)
  have m := mean_hit D
  simp only [D,Finset.mem_filter,Finset.mem_univ,true_and] at m
  rw [m]
  have h₁ : (Fintype.card (Bytes S.vp.params.m) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h₂ : (2:ℝ≥0∞)^(S.vp.params.h+S.vp.params.a*S.vp.params.k) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) h₁)
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) h₂)).mp
  simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofNat,D]
    using ShakeSingle.fraction S B

theorem key_mean (S : Sha2Set) (pre : Rate) (B : Finset (ShakeSingle.Decoded S)) :
    uniformMean (fun y => Classic.hit (key S pre y ∈ B)) =
      (B.card : ℝ≥0∞)/2^(S.vp.params.h+S.vp.params.a*S.vp.params.k) := by
  let tr : Rate ≃ Rate := ⟨(fun x => rateXor x pre),(fun x => rateXor x pre),(fun x => rateXor_cancel x pre),(fun x => rateXor_cancel x pre)⟩
  let e := tr.trans Completion.equiv
  let f (v : Bytes S.vp.params.m) := Classic.hit (DigestTransport.coveringDigest S.vp v ∈ B)
  have he (y : Rate) : Completion.bytes (rateXor pre y) = e y := by
    rw [Manifest.xor_comm pre y]; rfl
  simp only [key,he]
  exact (mean_equiv e (fun v => f (ShakeXof.head (output_sizes S).2 v))).trans
    ((prefix_mean (output_sizes S).2 f).trans (digest_mean S B))
end
end Reduction.ShakePermutation.ItsrLabel

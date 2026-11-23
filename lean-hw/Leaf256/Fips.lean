import Leaf256.LeafLayout
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open Spec.SHA256

theorem digest_fips (p : Spec.Params) (pk sk : Spec.Bytes) (a : LeafRust.address.Adrs) (i n : Nat)
    (shape : n = 16 ∨ n = 24 ∨ n = 32) (family : p.family = .sha2) (width : p.n = n)
    (hpk : pk.length = n) (hsk : sk.length = n) (hi : i < 2^32) (ht : a.typ = 3#u32) :
    (ser (leafDigest (seedState n pk) (fun k => word (template a sk) (4*k)) (BitVec.ofNat 32 i)
      (typeChange a) n)).take n = Spec.forsNode p sk i 0 pk (adrsS (addressOf a)) := by
  letI : Fact (p.family = .sha2) := ⟨family⟩
  let A := adrsS (addressOf a)
  let P := padFrom 64 ((prfAddress A i).compress ++ sk)
  let ws := Spec.SHA256.compress (seedState n pk) P
  have hw : ws.length = 8 := sha_compress_length _ _
  have hs : ((ser ws).take n).length = n := by simp [ser_length,hw]; omega
  have secret : (ser ws).take n = Spec.forsSkGen p sk pk A i := by
    unfold Spec.forsSkGen
    rw [PRF_eq,width]
    exact th256_one n pk hpk (by omega) _ _ (by omega)
  unfold leafDigest
  rw [prf_layout _ _ _ (by omega) hi]
  change (ser (Spec.SHA256.compress (seedState n pk) (blockOf (leafWords _ (fun k => ws[k]!) _ _ _)))).take n = _
  rw [leaf_layout a sk i n ws shape hsk hw hi ht,seedState,th256_one n pk hpk (by omega) _ _ (by omega),secret]
  simp only [Spec.forsNode,F_eq,width]
  rfl

theorem fors_node_spec (p : Spec.Params) (N : Usize) (s : Array U32 8#usize) (pk : Spec.Bytes)
    (sk : Array U8 N) (a : LeafRust.address.Adrs) (first : U32) (out : Nodes N)
    (shape : N.val = 16 ∨ N.val = 24 ∨ N.val = 32) (family : p.family = .sha2) (width : p.n = N.val)
    (hpk : pk.length = N.val) (seed : s.val.map (·.bv) = seedState N.val pk)
    (cpu : GatherRust.avx512Available = true) (bound : first.val+out.length ≤ 2^32) (ht : a.typ = 3#u32) :
    LeafRust.sha256.x86.fors_leaves s sk a first out ⦃ r => r.length = out.length ∧ ∀ k, k < out.length →
      bytes r.val[k]!.val = Spec.forsNode p (bytes sk.val) (first.val+k) 0 pk (adrsS (addressOf a)) ⦄ := by
  apply WP.spec_mono (fors_leaves_spec N s sk a first out shape cpu bound)
  rintro r ⟨hlen,hr⟩
  refine ⟨hlen, fun k hk => ?_⟩
  rw [← digest_fips p pk (bytes sk.val) a (first.val+k) N.val shape family width hpk (by simp) (by omega) ht]
  let ws := leafDigest (seedState N.val pk) (fun t => word (template a (bytes sk.val)) (4*t))
    (BitVec.ofNat 32 (first.val+k)) (typeChange a) N.val
  change _ = (ser ws).take N.val
  have hws : ws.length = 8 := sha_compress_length _ _
  apply List.ext_getElem
  · simp [ser_length,hws]; omega
  · intro t ht1 ht2
    have hi : t < N.val := by simpa using ht1
    simp only [bytes,List.getElem_map,List.getElem_take]
    have actual := hr k hk t hi
    rw [getElem!_pos _ _ (by simpa using hi),seed] at actual
    have encoded := Digest.ser_byte ws t (by omega)
    rw [getElem!_pos _ _ (by rw [ser_length,hws]; omega)] at encoded
    exact actual.trans encoded.symm

#print axioms fors_node_spec
end slhdsa.X86.Leaf

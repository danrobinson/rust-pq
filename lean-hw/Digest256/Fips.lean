import Digest256.Top
import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Digest

theorem ser_byte (words : List (BitVec 32)) (k : Nat) (hk : k < 4*words.length) :
    (ser words)[k]! = words[k/4]!.extractLsb' (8*(3-k%4)) 8 := by
  induction words generalizing k with
  | nil => simp at hk
  | cons w ws ih =>
    change (Spec.toByte w.toNat 4 ++ ser ws)[k]! = _
    have len : (Spec.toByte w.toNat 4).length = 4 := by simp [Spec.toByte]
    by_cases small : k < 4
    · rw [List.getElem!_eq_getElem?_getD,List.getElem?_append_left (by omega), ← List.getElem!_eq_getElem?_getD,
        getElem!_pos _ _ (by omega), show k/4 = 0 by omega, Nat.mod_eq_of_lt small]
      simp [Spec.toByte, BitVec.extractLsb']
    · rw [List.getElem!_eq_getElem?_getD,List.getElem?_append_right (by omega), ← List.getElem!_eq_getElem?_getD,len,
        ih (k-4) (by simp only [List.length_cons] at hk; omega)]
      rw [show k/4 = (k-4)/4+1 by omega, List.getElem!_cons_succ, show (k-4)%4 = k%4 by omega]

private theorem hash_length (st : List (BitVec 32)) (data : Spec.Bytes) :
    (hashed st data 10).length = 8 := by
  unfold hashed
  rw [show 10 = 9+1 by decide]
  rw [List.range_succ,List.foldl_append]
  apply sha_compress_length

theorem tweakable_digest_spec (p : Spec.Params) (N L : Usize) (seed : Array U32 8#usize)
    (rows : Slice (Array U8 L)) (out : Slice (Array U8 N)) (pk : Spec.Bytes)
    (adrs : Fin 16 → Spec.Adrs) (endpoints : Fin 16 → Spec.Bytes)
    (cpu : GatherRust.avx512Available = true) (hN : N.val = 16) (hL : L.val = 640)
    (family : p.family = .sha2) (width : p.n = N.val) (hpk : pk.length = p.n)
    (hn : 0 < rows.length) (h16 : rows.length ≤ 16) (heq : out.length = rows.length)
    (hs : seed.val.map (·.bv) = Spec.SHA256.compress Spec.SHA256.H0 (pk ++ Spec.toByte 0 (64-p.n)))
    (hp : ∀ j : Fin 16, j.val < rows.length → bytes rows.val[j.val]!.val =
      padFrom 64 ((adrs j).compress ++ endpoints j)) :
    DigestRust.sha256.x86.key_digests seed rows out ⦃ r => r.length = out.length ∧ ∀ j : Fin 16,
      j.val < rows.length → bytes r.val[j.val]!.val = Spec.T p pk (adrs j) (endpoints j) ⦄ := by
  apply WP.spec_mono (key_digests_spec N L seed rows out cpu hN hL hn h16 heq)
  rintro r ⟨hl,hr⟩
  refine ⟨hl,fun j hj => ?_⟩
  let B := pk ++ Spec.toByte 0 (64-p.n)
  let msg := (adrs j).compress ++ endpoints j
  let data := bytes rows.val[j.val]!.val
  let st := hashed (seed.val.map (·.bv)) data 10
  have padded : data = padFrom 64 msg := hp j hj
  have hB : B.length = 64 := by simp [B,Spec.toByte,hpk]; omega
  have length : data.length = 640 := by simp [data,hL]
  have words : st = hashFrom (Spec.SHA256.compress Spec.SHA256.H0 B) (padFrom 64 msg) := by
    simp only [st,hashed,hashFrom,← padded,length,hs,B]
  have eq : Spec.T p pk (adrs j) (endpoints j) = (ser st).take N.val := by
    have h := sha256_prefix64 B msg hB
    rw [← words] at h
    simp only [Spec.T,family,width,hN,↓reduceIte]
    simpa only [B,msg,List.append_assoc,width,hN] using congrArg (List.take 16) h
  rw [eq]
  have hst : st.length = 8 := hash_length _ _
  apply List.ext_getElem
  · simp [ser_length,hst,hN]
  · intro k hk hk'
    have bound : k < N.val := by simpa using hk
    simp only [bytes,List.getElem_map,List.getElem_take]
    have actual := hr j hj k bound
    have ref := ser_byte st k (by omega)
    rw [getElem!_pos _ _ (by simpa using bound)] at actual
    rw [getElem!_pos (ser st) k (by rw [ser_length,hst]; omega)] at ref
    exact actual.trans ref.symm

#print axioms tweakable_digest_spec
end slhdsa.X86.Digest

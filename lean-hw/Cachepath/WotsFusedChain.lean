import Cachepath.WotsFusedLayout
open Aeneas Aeneas.Std Result
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

/-- Chain tags and payloads are overwritten on each call. All other header cells persist across chains. -/
def Stable {N : Usize} (seed : Array U8 N) (addresses : Array address.Adrs machine.width) (s : Matrix machine.width) :=
  ∀ k<25, k ≠ N.val/8+4-1 → ¬(N.val/8+4 ≤ k ∧ k < N.val/8+4+N.val/8) →
    ∀ j<machine.width.val, cell s k j = baseWord seed addresses.val[j]! k

def DigestIs {N : Usize} (s : Matrix machine.width) (want : Nat → Spec.Bytes) :=
  ∀ j<machine.width.val, Spec.Keccak.squeeze (ShakeBatch.lane s j) 0 N.val = want j

theorem hashed_short {N : Usize} (seed value : Array U8 N) (a : address.Adrs) (chain index : U32)
    (packed hashed : Matrix machine.width) (j : Nat) (small : N.val≤32) (align : N.val%8=0)
    (permuted : ShakeBatch.lane hashed j=Spec.Keccak.permute (ShakeBatch.lane packed j))
    (cells : ∀ k<25, cell packed k j =
      if N.val/8+4 ≤ k ∧ k<N.val/8+4+N.val/8 then inputWord value.val (k-(N.val/8+4))
      else if k=N.val/8+4-1 then addressLow chain ||| wordTag index else baseWord seed a k) :
    Spec.Keccak.squeeze (ShakeBatch.lane hashed j) 0 N.val =
      Spec.shake256 (bytes seed.val ++ ((adrsS {a with word2:=chain,word3:=index}).bytes ++ bytes value.val)) N.val := by
  rw [permuted,Spec.shake256,Spec.Keccak.padded_fips _ (by simp [address_length];omega) (by simp [address_length];omega)]
  apply congrArg (fun s => Spec.Keccak.squeeze (Spec.Keccak.permute s) 0 N.val)
  apply Spec.Keccak.ext25 _ _ (by simp [ShakeBatch.lane]) (by simp [Spec.Keccak.padded])
  intro k hk
  simp only [ShakeBatch.lane,Spec.Keccak.padded,Spec.Keccak.ofFnAt _ _ hk,cells k hk]
  exact packed_layout seed value a chain index small align k

theorem chain_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (count offset : Usize) (countEq : count.val=N.val/8) (offsetEq : offset.val=N.val/8+4)
    (id : U64) (chain : U32) (idEq : id.bv=addressLow chain)
    (seed : Array U8 N) (addresses : Array address.Adrs machine.width)
    (x : Nat → Spec.Bytes) (input state : Matrix machine.width)
    (stable : Stable seed addresses input) (start : DigestIs (N:=N) state x) (permutes : PermutationCorrect) :
    generate_loop0_loop0 count ⟨0#u32,15#u32⟩ offset input id state ⦃ next hashed =>
      Stable seed addresses next ∧ DigestIs (N:=N) hashed (fun j => Spec.chain (Shake.params p) (x j) 0 15
        (bytes seed.val) (adrsS {addresses.val[j]! with word2:=chain})) ⦄ := by
  let inv := fun (n : Nat) (st dig : Matrix machine.width) => Stable seed addresses st ∧ DigestIs (N:=N) dig
    (fun j => Spec.chain (Shake.params p) (x j) 0 n (bytes seed.val) (adrsS {addresses.val[j]! with word2:=chain}))
  apply rounds (P:=inv)
  · exact ⟨stable,by simpa [DigestIs,Spec.chain] using start⟩
  intro ix st dig _ ⟨header,before⟩
  have small := hp.le32
  have align := aligned_hash hp
  obtain ⟨values,digest,words⟩ := digest_words (N:=N) dig (by omega) align
  apply WP.spec_mono (round_spec count offset id ix st dig (by omega) (by omega) permutes)
  rintro ⟨packed,hashed⟩ ⟨cells,permed⟩
  constructor
  · intro k hk notTag notPayload j hj
    rw [cells k hk j hj,compose,countEq,offsetEq,ite_eq_right notPayload,ite_eq_right notTag,header k hk notTag notPayload j hj]
  intro j hj
  have hash := hashed_short seed values.val[j]! addresses.val[j]! chain ix packed hashed j small align (permed j hj) (by
    intro k hk
    rw [cells k hk j hj,compose,idEq,countEq,offsetEq]
    split_ifs with payload tag
    · exact (words j hj _ (by omega)).symm
    · rfl
    · exact header k hk tag payload j hj)
  let a := {addresses.val[j]! with word2:=chain}
  change _ = Spec.chain (Shake.params p) (x j) 0 (ix.val+1) (bytes seed.val) (adrsS a)
  have prior : Spec.Keccak.squeeze (ShakeBatch.lane dig j) 0 N.val =
      Spec.chain (Shake.params p) (x j) 0 ix.val (bytes seed.val) (adrsS a) := before j hj
  rw [hash,chain_succ,← prior,← digest j hj]
  simp [a,Spec.F,Shake.params,adrsS,paramsS_n,hp.n_eq,List.append_assoc]

end slhdsa.cache.builder.nativeShake.Vector.Fused

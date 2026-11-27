import Fused.Program
open Aeneas Aeneas.Std Result
namespace slhdsa.Fused
open ShakeBatch NativeVerify NativeVerify.Wots NativeShakeWots cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [kernel : Kernel]
local instance chainValuesMachine : Machine := machine kernel

abbrev Permutes (k : Kernel) := @PermutationCorrect (machine k)

def chainValue {N : Usize} (p : params.Params) (seed : Array U8 N) (addr : Nat → address.Adrs)
    (id : U32) (initial : Nat → Spec.Bytes) (step lane : Nat) : Spec.Bytes :=
  Spec.chain (Shake.params p) (initial lane) 0 step (bytes seed.val) (adrsS {(addr lane) with word2:=id})

/-- The physical word-2 register can differ in all eight lanes. This is the
fused signer's layout, where lanes carry different WOTS keys at one chain. -/
structure Header {N : Usize} (seed : Array U8 N) (addr : Nat → address.Adrs)
    (sw : Array U64 4#usize) (w0 w1 : U64) (w2 : Array U64 8#usize) : Prop where
  seedWords : ∀ k<N.val/8, sw.val[k]!.bv=inputWord seed.val k
  lo : ∀ l<8, w0.bv=addressWord (addr l) 0
  hi : ∀ l<8, w1.bv=addressWord (addr l) 1
  lane : ∀ l<8, w2.val[l]!.bv=addressWord (addr l) 2

theorem initial_permutation {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (addr : Nat → address.Adrs) (id : U32) (sw skw : Array U64 4#usize) (w0 w1 : U64)
    (w2 : Array U64 8#usize) (tag : U64) (state : Matrix 8#usize)
    (header : Header seed addr sw w0 w1 w2) (key : ∀ k<N.val/8, skw.val[k]!.bv=inputWord sk.val k)
    (tagged : tag.bv=addressLow id) (perms : Permutes kernel) :
    (do let packed ← fill_prf N state sw skw w0 w1 w2 (Array.repeat 8#usize tag)
        kernel.permute packed) ⦃ out => ∀ l<8, digest N out l=Spec.PRF (Shake.params p)
          (bytes seed.val) (bytes sk.val) {adrsS (addr l) with word2:=id.val,word3:=0} ⦄ := by
  step with fill_layout N state sw skw w0 w1 w2 (Array.repeat 8#usize tag) hp.le32 as ⟨st,cells⟩
  step with perms st as ⟨out,permed⟩
  rename_i l live
  have tagOk : (Array.repeat 8#usize tag).val[l]!.bv=addressLow id ||| wordTag 0#u32 := by
    simp only [Array.repeat_val,List.getElem!_replicate _ (show l<(8#usize).val from live),tagged,show wordTag 0#u32=0#64 by decide,BitVec.or_zero]
  have hash := packed_fips seed sk (addr l) id 0#u32 sw w0 w1 w2 (Array.repeat 8#usize tag) (fun k _ => skw.val[k]!.bv)
    st out l hp.le32 (aligned_hash hp) header.seedWords (header.lo l live) (header.hi l live) (header.lane l live)
    tagOk key (fun k hk => cells k hk l live) (permed l live)
  simpa [Spec.PRF,Shake.params,adrsS,paramsS_n,hp.n_eq,List.append_assoc] using hash

theorem next_permutation {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (addr : Nat → address.Adrs) (id step : U32) (initial : Nat → Spec.Bytes)
    (sw : Array U64 4#usize) (w0 w1 : U64) (w2 : Array U64 8#usize) (tag : U64) (state : Matrix 8#usize)
    (header : Header seed addr sw w0 w1 w2) (tagged : tag.bv=addressLow id ||| wordTag step)
    (prior : ∀ l<8, digest N state l=chainValue p seed addr id initial step.val l)
    (perms : Permutes kernel) :
    (do let packed ← refill_short_inplace N state sw w0 w1 w2 (Array.repeat 8#usize tag)
        kernel.permute packed) ⦃ out => ∀ l<8, digest N out l=chainValue p seed addr id initial (step.val+1) l ⦄ := by
  step with refill_layout N state sw w0 w1 w2 (Array.repeat 8#usize tag) hp.le32 as ⟨st,cells⟩
  step with perms st as ⟨out,permed⟩
  rename_i l live
  obtain ⟨raw,dig,stored⟩ := digest_words (N:=N) state (by have := hp.le32;omega) (aligned_hash hp)
  have tagOk : (Array.repeat 8#usize tag).val[l]!.bv=addressLow id ||| wordTag step := by
    simp only [Array.repeat_val,List.getElem!_replicate _ (show l<(8#usize).val from live),tagged]
  have computed := packed_fips seed raw.val[l]! (addr l) id step sw w0 w1 w2 (Array.repeat 8#usize tag)
    (cell state) st out l hp.le32 (aligned_hash hp) header.seedWords (header.lo l live) (header.hi l live)
    (header.lane l live) tagOk (fun k hk => (stored l live k hk).symm) (fun k hk => cells k hk l live) (permed l live)
  unfold chainValue at prior ⊢
  rw [chain_succ,←prior l live,computed,dig l live]
  simp [digest,Spec.F,Shake.params,paramsS_n,hp.n_eq,adrsS,List.append_assoc]

end slhdsa.Fused

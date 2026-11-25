import Fused.Addresses
import Fused.Prefix
import Fused.Stream
import Shakebatch.Short

open Aeneas Aeneas.Std Result
namespace slhdsa.Fused.Stream
open ShakeBatch Spec.Keccak cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [kernel : Kernel]
local instance : Machine := machine kernel

def init (n : Usize) (sw : Array U64 4#usize) (w0 w1 : U64) (w2 : Array U64 8#usize) := do
  let pk := Array.repeat 25#usize (Array.repeat 8#usize 0#u64)
  let pk1 ← xmss_sign_batch_loop1 ⟨0#usize,n⟩ sw pk
  let pk2 ← Array.update pk1 n (Array.repeat 8#usize w0)
  let i4 ← n + 1#usize
  let pk3 ← Array.update pk2 i4 (Array.repeat 8#usize w1)
  let i5 ← n + 2#usize
  Array.update pk3 i5 w2

theorem row (s : Matrix 8#usize) (idx : Usize) (value : Array U64 8#usize) (k l : Nat)
    (hi : idx.val<25) :
    cell (s.set idx value) k l = if k=idx.val then value.val[l]!.bv else cell s k l := by
  unfold cell
  rw [Array.set_val_eq]
  by_cases h : k=idx.val
  · subst k; rw [setSame _ _ _ (by simpa using hi)]; simp
  · rw [setOther _ _ _ _ (Ne.symm h)]; simp [h]

theorem init_spec {N : Usize} (seed : Array U8 N) (addr : Nat → address.Adrs) (n pos : Usize)
    (sw : Array U64 4#usize) (w0 w1 : U64) (w2 : Array U64 8#usize)
    (width : n.val=N.val/8) (off : pos.val=n.val+4) (small : N.val≤32) (align : N.val%8=0)
    (seedWords : ∀ k<n.val, sw.val[k]!.bv=inputWord seed.val k)
    (front : ∀ l<8, w0.bv=addressWord (addr l) 0 ∧ w1.bv=addressWord (addr l) 1)
    (tag : ∀ l<8, w2.val[l]!.bv=addressWord (addr l) 2)
    (zero : ∀ l<8, (addr l).word2=0#u32 ∧ (addr l).word3=0#u32) :
    init n sw w0 w1 w2 ⦃ out => ∀ l<8, (ShakeBatch.lane out l,8*pos.val) =
      (bytes seed.val ++ (adrsS (addr l)).bytes).foldl feed initial ⦄ := by
  unfold init
  step with seed_prefix n sw _ (by omega) as ⟨seeded,seedEq⟩
  step as ⟨low,store0⟩
  step as ⟨n1,plus1⟩
  step as ⟨high,store1⟩
  step as ⟨n2,plus2⟩
  step as ⟨out,store2⟩
  rename_i l hl
  let msg := bytes seed.val ++ (adrsS (addr l)).bytes
  have len : msg.length=8*pos.val := by simp [msg,address_length]; omega
  have ref := aligned_prefix msg pos.val (by omega) (by omega)
  rw [←len,List.take_length] at ref
  refine Eq.trans ?_ ref.symm
  apply Prod.ext _ len.symm
  change ShakeBatch.lane out l=prefixState msg pos.val
  apply ext25 _ _ (by simp [ShakeBatch.lane]) (by simp [prefixState])
  intro k hk
  have rep (w : U64) : (Array.repeat 8#usize w).val[l]!.bv=w.bv := by
    rw [Array.repeat_val,List.getElem!_replicate _ (show l<(8#usize).val from hl)]
  rw [show (ShakeBatch.lane out l)[k]! = _ from ofFnAt _ k hk,
    store2,row _ _ _ _ _ (by omega),store1,row _ _ _ _ _ (by omega),rep w1,
    store0,row _ _ _ _ _ (by omega),rep w0,seedEq k l hl]
  have tailZero : addressWord (addr l) 3 = 0 := by
    have eq := packed_address (addr l) 0#u32 0#u32 3 (by decide)
    have same : {(addr l) with word2:=0#u32,word3:=0#u32} = addr l := by
      have h := zero l hl
      generalize addr l = a at h ⊢
      rcases a with ⟨_,_,_,_,x,y⟩
      obtain ⟨rfl,rfl⟩ := h
      rfl
    rw [same] at eq
    exact eq.trans (by rfl)
  have size8 : (bytes seed.val).length=8*n.val := by simp; omega
  have cleared : cell (Array.repeat 25#usize (Array.repeat 8#usize 0#u64)) k l=0 := by
    unfold cell
    rw [Array.repeat_val,List.getElem!_replicate _ (show k<(25#usize).val from hk),rep]
    rfl
  simp only [prefixState,ofFnAt _ k hk,msg,messageWord_append _ _ _ _ size8,cleared,plus1,plus2,off]
  by_cases hs : k<n.val
  · simp [hs,show k≠n.val+2 by omega,show k≠n.val+1 by omega,show k≠n.val by omega,
      show k<n.val+4 by omega]
    simpa using (seedWords k hs).trans (inputWord_eq _ _)
  · simp only [hs,ite_false]
    rw [← addressWord_eq]
    by_cases stop : k<n.val+4
    · simp only [stop,ite_true]
      obtain h|h|h|h : k=n.val ∨ k=n.val+1 ∨ k=n.val+2 ∨ k=n.val+3 := by omega
      all_goals subst k
      all_goals simp [(front l hl).1,(front l hl).2,tailZero]
      simpa using tag l hl
    · simp [stop,show k≠n.val+2 by omega,show k≠n.val+1 by omega,show k≠n.val by omega]

theorem init_keys {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (a : address.Adrs) (base : Nat) (n pos : Usize) (sw : Array U64 4#usize)
    (w0 w1 : U64) (w2 : Array U64 8#usize) (width : n.val=N.val/8) (off : pos.val=n.val+4)
    (seedWords : ∀ k<n.val, sw.val[k]!.bv=inputWord seed.val k)
    (lo : w0.bv=addressWord a 0) (hi : w1.bv=addressWord a 1)
    (tag : ∀ l<8, w2.val[l]!.bv=addressWord (laneAddress a address.WOTS_PK base l) 2) :
    init n sw w0 w1 w2 ⦃ out => ∀ l<8, (ShakeBatch.lane out l,8*pos.val) =
      (bytes seed.val ++ (Spec.wotsPkAdrs (adrsS (laneAddress a address.WOTS_HASH base l))).bytes).foldl feed initial ⦄ := by
  apply WP.spec_mono (init_spec seed (laneAddress a address.WOTS_PK base) n pos sw w0 w1 w2
    width off hp.le32 (aligned_hash hp) seedWords (fun l _ => ⟨lo,hi⟩) tag (fun _ _ => ⟨rfl,rfl⟩))
  intro out words l hl
  rw [words l hl,WOTS_PK_eq]
  rfl

/-- Complete WOTS public keys at the actual fused final read, for the eight lane
addresses, after streaming all chain endpoints in specification order. -/
theorem finish_keys {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (addr : Nat → Spec.Adrs) (pk : Matrix 8#usize) (pos : Usize) (rate : pos.val<17)
    (permutes : PermutationCorrect)
    (streamed : ∀ l<8, (ShakeBatch.lane pk l,8*pos.val) =
      ((bytes seed.val ++ (Spec.wotsPkAdrs (addr l)).bytes) ++
       (List.range (Shake.params p).len).flatMap (pkGenStep (Shake.params p) (bytes sk.val) (bytes seed.val) (addr l))).foldl feed initial) :
    (do let padded ← xmss_sign_batch_loop3 ⟨0#usize,8#usize⟩ pk pos
        let final ← kernel.permute padded
        NativeVerify.ActiveHash.read_active N final 8#usize) ⦃ out => ∀ l<8,
      bytes out.val[l]!.val = Spec.wotsPkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (addr l) ⦄ := by
  apply WP.spec_mono (finish_read N pk pos rate permutes (by have := hp.le32; omega) (aligned_hash hp))
  intro out h l hl
  rw [h l hl,streamed l hl]
  change Spec.shake256 _ N.val = Spec.shake256 _ (Shake.params p).n
  rw [show (Shake.params p).n=N.val from hp.n]
  rfl

end slhdsa.Fused.Stream

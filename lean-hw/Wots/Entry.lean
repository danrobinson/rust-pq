import Wots.Endpoint
import Wots.Input
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open Spec.SHA256

set_option maxHeartbeats 1600000 in
/-- The public kernel establishes the inputs to the batch proof, then runs the
outer iterator across exactly the number of requested chain endpoints. -/
theorem entry_spec {N L : Usize} (P : Spec.Params) (state : Array U32 8#usize) (sk : Array U8 N)
    (a : WotsRust.address.Adrs) (first : U32) (out : Slice (Array U8 L)) (pk : Spec.Bytes)
    (hn : N.val = P.n) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32)
    (seed : state.val.map (·.bv) = seedState P.n pk)
    (fits : (2*N.val+3)*out.length ≤ Usize.max) (post : Slice (Array U8 L) → Prop)
    (finish : ∀ (base : Words) (iv two : Hash) (len total : Usize),
      len.val = 2*N.val+3 → total.val = len.val*out.length →
      (∀ j, stateWords (laneState iv j) = seedState P.n pk) →
      (∀ j k, k < 16 → base.val[k]! j = word (padFrom 64
        (((adrsS (WotsRust.addressOf a)).setTypeAndClear Spec.WOTS_PRF).compress ++ bytes sk.val)) (4*k)) →
      Trace two (fun j => schedule (laneBlock base j)) (laneState iv) 2 →
      wots_endpoints_loop1 N ⟨⟨0#usize,total⟩,16#usize⟩ first out base iv
        (fun j => BitVec.ofNat 32 j.val) (fun _ => 0xffff) (fun _ => 0x50000) len two ⦃ post ⦄) :
    wots_endpoints state sk a first out ⦃ post ⦄ := by
  unfold wots_endpoints
  simp only [WotsRust.address.Adrs.with_type,WotsRust.address.WOTS_PRF,lift,bind_ok]
  step with short_block_spec _ (Array.to_slice sk) (by simp; omega) as ⟨b,hb⟩
  step with words_spec N L b as ⟨w,hw⟩
  step with broadcast_spec N L state as ⟨iv,hiv⟩
  simp only [WotsRust.core.core_arch.x86.avx512f._mm512_set_epi32,
    DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32,
    _root_.core.core_arch.x86.avx512f._mm512_set1_epi32,bind_ok,WotsRust.address.WOTS_HASH,
    WotsRust.params.LEN2]
  step as ⟨chg,hchg⟩
  step as ⟨twice,htwice⟩
  · scalar_tac +nonLin
  step as ⟨len,hlen⟩
  all_goals try scalar_tac
  have lenOK : len.val = 2*N.val+3 := by scalar_tac
  step with first_two iv w (laneBlock w) (fun k hk j =>
    (Leaf.word_blockOf (chainWords w j) k (by omega)).symm) as ⟨two,htwo⟩
  step as ⟨total,htotal⟩
  all_goals try (change len.val*out.length ≤ Usize.max; simpa only [lenOK] using fits)
  step as ⟨it,hit,hstep⟩
  have eit : it = ⟨⟨0#usize,total⟩,16#usize⟩ := by cases it; simp_all
  rw [eit]
  have lanes : (fun j : Fin 16 => [(0#i32).bv,(1#i32).bv,(2#i32).bv,(3#i32).bv,(4#i32).bv,
      (5#i32).bv,(6#i32).bv,(7#i32).bv,(8#i32).bv,(9#i32).bv,(10#i32).bv,(11#i32).bv,
      (12#i32).bv,(13#i32).bv,(14#i32).bv,(15#i32).bv][j.val]!) = fun j => BitVec.ofNat 32 j.val := by
    funext j; fin_cases j <;> decide
  rw [lanes]
  have val : chg = 327680#u32 := by apply UScalar.eq_of_val_eq; rw [hchg,UScalar.val_xor]; simp [U32.size,U32.numBits]
  rw [val]
  apply finish w iv two len total lenOK htotal _ _ htwo
  · intro j
    rw [Leaf.initial_words _ _ hiv,seed]
  · intro j k hk
    rw [hw k hk j,hb]
    simp only [Array.val_to_slice,WotsRust.addressOf,adrsS,Spec.Adrs.setTypeAndClear,Spec.WOTS_PRF]; rfl

end slhdsa.X86.Wots

import Wots.Fips
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open WotsRust.core.core_arch.x86.avx512f

def compressRound (N : Usize) (iv pre hash : Hash) (w : Words) (counter half : Reg) := do
  let high ← _mm512_slli_epi32 16#u32 counter
  let packed ← packHigh N w hash high half
  let digest ← PlatformRust.sha256.x86.avx512.compress iv pre packed
  ok (packed,digest)

def recoveryBlock (N : Usize) (w : Words) (h : Hash) (counter : Reg) (j : Fin 16) :=
  Leaf.blockOf (packedWord (fun i => w.val[i]! j) (fun i => h.val[i]! j) N.val (counter j))

theorem compress_round_spec (N : Usize) (iv pre h : Hash) (w : Words) (counter : Reg)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (prefixOK : Trace pre (fun j => Spec.SHA256.schedule (recoveryBlock N w h counter j)) (laneState iv) 4) :
    compressRound N iv pre h w counter (fun _ => 0xffff) ⦃ words out =>
      (∀ k < 16, ∀ j, words.val[k]! j = packedWord (fun i => w.val[i]! j) (fun i => h.val[i]! j) N.val (counter j) k) ∧
      ∀ j, stateWords (laneState out j) = Spec.SHA256.compress (stateWords (laneState iv j)) (recoveryBlock N w h counter j) ⦄ := by
  unfold compressRound
  simp only [_mm512_slli_epi32,LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,bind_ok]
  rw [show (16#u32).bv.toNat % 256 = 16 by decide]
  step with pack_high_spec N w h counter shape as ⟨words,hw⟩
  step with compress_block_spec iv pre words (recoveryBlock N w h counter) prefixOK
    (fun k hk j => by rw [hw k hk j,recoveryBlock,Leaf.word_blockOf _ _ hk]) as ⟨out,hh⟩
  exact ⟨hw,hh⟩

open Spec.SHA256

set_option maxHeartbeats 1500000 in
/-- For a live lane, a recovery compression computes F at that lane's own chain step. -/
theorem recovery_f_spec (P : Spec.Params) [Fact (P.family = .sha2)] (N : Usize) (pk : Spec.Bytes)
    (iv pre h : Hash) (w : Words) (counter : Reg) (width : N.val = P.n)
    (shape : P.n=16 ∨ P.n=24 ∨ P.n=32) (hpk : pk.length = P.n)
    (seed : ∀ j, stateWords (laneState iv j) = seedState P.n pk)
    (prefixOK : Trace pre (fun j => schedule (recoveryBlock N w h counter j)) (laneState iv) 4) :
    compressRound N iv pre h w counter (fun _ => 0xffff) ⦃ words out =>
      ∀ j (A : Spec.Adrs) (m : Spec.Bytes), m.length = P.n → (counter j).toNat < 15 →
      (∀ g t k, k < 16 → packedWord (chainWords w j) g P.n t k =
        packedWord (fun i => word (template A m) (4*i)) g P.n t k) →
      (ser (stateWords (laneState out j))).take P.n =
        Spec.F P pk { A with word3 := (counter j).toNat } ((ser (stateWords (laneState h j))).take P.n) ⦄ := by
  apply WP.spec_mono (compress_round_spec N iv pre h w counter (width ▸ shape) prefixOK)
  rintro ⟨words,out⟩ ⟨_,hash⟩ j A m hm bound ready
  let ws := stateWords (laneState h j)
  have size : ws.length = 8 := by simp [ws,stateWords,laneState]
  have block : recoveryBlock N w h counter j =
      padFrom 64 ({ A with word3 := (counter j).toNat }.compress ++ (ser ws).take P.n) := by
    rw [← packed_template_block A m ws P.n _ hm size shape (by omega)]
    apply Leaf.block_congr
    intro k hk
    rw [width]
    apply Eq.trans (packed_congr (chainWords w j) (chainWords w j) (fun i => h.val[i]! j)
      (fun i => ws[i]!) P.n k (counter j) rfl (fun i hi => Leaf.lane_lookup h j i hi) shape)
    simpa using ready (fun i => ws[i]!) (counter j) k hk
  rw [hash,seed,block,F_eq]
  apply th256_one _ _ hpk (by omega)
  simp [ws,ser_length,size]

end slhdsa.X86.Wots

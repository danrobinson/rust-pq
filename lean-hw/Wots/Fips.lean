import Wots.Layout
import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open Spec.SHA256

def template (A : Spec.Adrs) (m : Spec.Bytes) :=
  padFrom 64 ({ A with word3 := 0 }.compress ++ m)

private theorem packet_eq (A : Spec.Adrs) (m : Spec.Bytes) (t : Nat) (ht : t < 16) (hm : m.length ≤ 32) :
    Chain.packet (A.compress.take 18) (BitVec.ofNat 32 t) m (padTail m.length) =
      padFrom 64 ({ A with word3 := t }.compress ++ m) := by
  rw [padFrom_blk _ _ (by omega),compress_word3 A t]
  simp only [Chain.packet,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : t < 2^32),List.append_assoc]

theorem packed_template_block (A : Spec.Adrs) (m : Spec.Bytes) (ws : List Word) (n k : Nat)
    (hm : m.length = n) (hws : ws.length = 8) (shape : n=16 ∨ n=24 ∨ n=32) (hk : k < 16) :
    Leaf.blockOf (packedWord (fun i => word (template A m) (4*i)) (fun i => ws[i]!) n (BitVec.ofNat 32 k)) =
      padFrom 64 ({ A with word3 := k }.compress ++ (ser ws).take n) := by
  let value := (ser ws).take n
  have hv : value.length = n := by simp [value,ser_length,hws]; omega
  have base : template A m = Chain.packet (A.compress.take 18) 0 m (padTail n) := by
    rw [← hm]; exact (packet_eq A m 0 (by decide) (by omega)).symm
  change _ = padFrom 64 ({ A with word3 := k }.compress ++ value)
  apply Eq.trans _ (Leaf.block_words_inverse _ (padFrom_blk_length _ _ (by omega)))
  apply Leaf.block_congr
  intro i _
  rw [base,packed_layout _ _ _ _ _ _ _ (by simp [adrs_compress_length]) hm hws shape (by omega)]
  change word (Chain.packet _ _ value (padTail n)) _ = _
  rw [← hv,packet_eq A value k hk (by omega)]

private theorem chainState_length (iv : List Word) (w : Nat → Word) (initial : List Word) (n t : Nat)
    (h : initial.length = 8) : (chainState iv w initial n t).length = 8 := by
  cases t with
  | zero => exact h
  | succ k => exact sha_compress_length ..

/-- The pure reference computed by the fifteen-step SIMD loop is FIPS 205
Algorithm 5 when initialized with the SHA-256 public-seed state. -/
theorem chain_fips (P : Spec.Params) [Fact (P.family = .sha2)] (pk : Spec.Bytes) (A : Spec.Adrs)
    (m : Spec.Bytes) (init : List Word) (t : Nat) (bound : t ≤ 15) (hpk : pk.length = P.n)
    (hm : m.length = P.n) (hi : init.length=8) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32) :
    (ser (chainState (seedState P.n pk) (fun i => word (template A m) (4*i)) init P.n t)).take P.n =
      Spec.chain P ((ser init).take P.n) 0 t pk A := by
  induction t with
  | zero => rfl
  | succ k ih =>
    let ws := chainState (seedState P.n pk) (fun i => word (template A m) (4*i)) init P.n k
    let value := (ser ws).take P.n
    have hws : ws.length = 8 := chainState_length _ _ _ _ _ hi
    have hv : value.length = P.n := by simp [value,ser_length,hws]; omega
    let msg := padFrom 64 ({ A with word3 := k }.compress ++ value)
    have correct := packed_template_block A m ws P.n k hm hws shape (by omega)
    change (ser (compress (seedState P.n pk) _)).take P.n = _
    rw [correct,chain_succ,F_eq,Nat.zero_add]
    change (ser (compress (seedState P.n pk) msg)).take P.n = _
    have prev : value = _ := ih (by omega)
    rw [← prev]
    exact th256_one P.n pk hpk (by omega) _ value (by omega)

private theorem state_congr (iv : List Word) (w w' : Nat → Word) (init : List Word) (n t : Nat)
    (shape : n=16 ∨ n=24 ∨ n=32) (same : ∀ k < 16, w k = w' k) :
    chainState iv w init n t = chainState iv w' init n t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [chainState,ih]
    congr 1
    apply Leaf.block_congr
    intro i hi
    exact packed_congr _ _ _ _ _ _ _ (same i hi) (fun _ _ => rfl) shape

/-- The actual endpoint loop realizes Algorithm 5 on sixteen independent addresses.
The entry conditions describe the prepared message templates, seed and cached prefix. -/
theorem endpoint_chain_fips (P : Spec.Params) [Fact (P.family = .sha2)] (N : Usize) (pk : Spec.Bytes)
    (iv pre initial : Hash) (base : Words) (A : Fin 16 → Spec.Adrs) (m : Fin 16 → Spec.Bytes)
    (width : N.val = P.n) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32) (hpk : pk.length = P.n)
    (hm : ∀ j, (m j).length = P.n) (seed : ∀ j, stateWords (laneState iv j) = seedState P.n pk)
    (messageOK : ∀ j k, k < 16 → base.val[k]! j = word (template (A j) (m j)) (4*k))
    (prefixOK : Trace pre (fun j => schedule (Leaf.blockOf (chainWords base j))) (laneState iv) 4) :
    WotsRust.sha256.x86.avx512.wots_endpoints_loop1_loop0 N ⟨0#i32,15#i32⟩ iv (fun _ => 0xffff) base initial pre ⦃ out =>
      ∀ j, (ser (stateWords (laneState out j))).take P.n =
        Spec.chain P ((ser (stateWords (laneState initial j))).take P.n) 0 15 pk (A j) ⦄ := by
  apply WP.spec_mono (chain_spec N iv pre initial base (width ▸ shape) prefixOK)
  intro out h j
  rw [h j,seed,width,state_congr _ (chainWords base j) (fun k => word (template (A j) (m j)) (4*k)) _ _ _ shape (messageOK j)]
  exact chain_fips P pk (A j) (m j) _ 15 (by decide) hpk (hm j) (by simp [stateWords,laneState]) shape
end slhdsa.X86.Wots

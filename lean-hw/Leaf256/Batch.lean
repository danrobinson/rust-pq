import Leaf256.Messages
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open Spec.SHA256
open LeafRust.sha256.x86.avx512

abbrev laneWords {n : Usize} (a : Array Reg n) (j : Fin 16) (k : Nat) := a.val[k]! j

def hashBatch {N : Usize} (base : Array Reg 16#usize) (state prefixPrf prefixF : Array Reg 8#usize)
    (idx half change : Reg) (dst : Slice (Array U8 N)) := do
  let (w,high) ← prfMessage base idx half
  let prf ← compress state prefixPrf w
  let w' ← leafMessage N w high half change prf
  let leaf ← compress state prefixF w'
  write_words leaf dst

def withType (f : Nat → Word) (change : Word) (k : Nat) := if k = 2 then f 2 ^^^ change else f k

def leafDigest (st : List Word) (base : Nat → Word) (idx change : Word) (n : Nat) :=
  let prf := Spec.SHA256.compress st (blockOf (prfWords base idx))
  Spec.SHA256.compress st (blockOf (leafWords base (fun k => prf[k]!) idx change n))

theorem lane_lookup (s : Array Reg 8#usize) (j : Fin 16) (k : Nat) (hk : k < 8) :
    laneWords s j k = (stateWords (laneState s j))[k]! := by
  interval_cases k <;> rfl

theorem block_congr (f g : Nat → Word) (h : ∀ k < 16, f k = g k) : blockOf f = blockOf g := by
  unfold blockOf
  congr 1
  funext j
  rw [h (j.val/4) (by omega)]

private theorem leaf_congr (b f g : Nat → Word) (idx change : Word) (n : Nat)
    (hn : n = 16 ∨ n = 24 ∨ n = 32) (h : ∀ k < 8, f k = g k) :
    blockOf (leafWords b f idx change n) = blockOf (leafWords b g idx change n) := by
  apply block_congr
  intro k hk
  unfold leafWords
  split_ifs <;> simp (disch := omega) only [h]

theorem digest_congr {base other : Nat → Word} (st : List Word) (idx change : Word) (n : Nat)
    (h : ∀ k < 16, base k = other k) : leafDigest st base idx change n = leafDigest st other idx change n := by
  have pre : blockOf (prfWords base idx) = blockOf (prfWords other idx) := by
    apply block_congr; intro k hk; simp (disch := omega) only [prfWords,h]
  unfold leafDigest
  rw [pre]
  apply congrArg (Spec.SHA256.compress st)
  apply block_congr
  intro k hk
  simp (disch := omega) only [leafWords,prfWords,h]

theorem hash_batch_spec {N : Usize} (base : Array Reg 16#usize) (s pp pf : Array Reg 8#usize)
    (idx change : Reg) (dst : Slice (Array U8 N))
    (hn : N.val = 16 ∨ N.val = 24 ∨ N.val = 32) (hl : dst.length ≤ 16)
    (hp : Trace pp (fun j => schedule (blockOf (laneWords base j))) (laneState s) 4)
    (hf : Trace pf (fun j => schedule (blockOf (withType (laneWords base j) (change j)))) (laneState s) 4) :
    hashBatch base s pp pf idx (fun _ => 0xffff) change dst ⦃ r =>
      r.length = dst.length ∧ ∀ j : Fin 16, j.val < dst.length → ∀ k, k < N.val →
      (r.val[j.val]!.val[k]!).bv =
        ((leafDigest (stateWords (laneState s j)) (laneWords base j) (idx j) (change j) N.val)[k/4]!).extractLsb'
          (8*(3-k%4)) 8 ⦄ := by
  unfold hashBatch
  step with prf_message_spec base idx as ⟨pair,hh,hw⟩
  obtain ⟨w,high⟩ := pair
  let B := fun j => blockOf (prfWords (laneWords base j) (idx j))
  have words (k) (hk : k < 16) (j) : laneWords w j k = word (B j) (4*k) := by
    rw [word_blockOf _ _ hk]; exact hw k hk j
  have prefixP : Trace pp (fun j => schedule (B j)) (laneState s) 4 := by
    apply transfer_prefix (by decide) _ hp
    intro j k hk
    simp (disch := omega) only [B,word_blockOf,prfWords,if_neg]
  step with compress_block_spec s pp w B prefixP words as ⟨prf,hprf⟩
  step with leaf_message_spec N w high change prf (laneWords base) idx hn hh hw as ⟨w',hw'⟩
  let F := fun j => blockOf (leafWords (laneWords base j) (laneWords prf j) (idx j) (change j) N.val)
  have prefixF : Trace pf (fun j => schedule (F j)) (laneState s) 4 := by
    apply transfer_prefix (by decide) _ hf
    intro j k hk
    simp (disch := omega) only [F,word_blockOf,leafWords,prfWords,withType,if_neg]
  step with compress_block_spec s pf w' F prefixF (fun k hk j => by
    rw [word_blockOf _ _ hk]; exact hw' k hk j) as ⟨d,hd⟩
  apply WP.spec_mono (Store.write_words_spec d dst hn hl)
  rintro r ⟨hlen,hr⟩
  refine ⟨hlen,fun j hj k hk => ?_⟩
  rw [hr j hj k hk]
  unfold Store.digestByte
  rw [show d.val[k/4]! j = _ from lane_lookup d j (k/4) (by omega),hd j]
  have get (t : Nat) (ht : t < 8) : laneWords prf j t = (Spec.SHA256.compress (stateWords (laneState s j)) (B j))[t]! := by
    rw [lane_lookup prf j t ht,hprf j]
  exact congrArg (fun msg => ((Spec.SHA256.compress (stateWords (laneState s j)) msg)[k/4]!).extractLsb'
    (8*(3-k%4)) 8) (leaf_congr _ _ _ _ _ _ hn get)

#print axioms hash_batch_spec
end slhdsa.X86.Leaf

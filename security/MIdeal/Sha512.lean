import MIdeal.MixedTables
import Ideal.Sha.Shape

namespace MIdeal.Sha512
open VCVio.Algorithms Ideal SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2

def len16 (n : ℕ) := Encoding.natToBytesBE (8*n) 16

@[simp] theorem len16_length (n : ℕ) : (len16 n).length = 16 := by simp [len16, Encoding.natToBytesBE]

def tailL (n : ℕ) : List UInt8 := 0x80 :: (List.replicate ((239 - n % 128) % 128) 0 ++ len16 n)
def padL (m : List UInt8) := m ++ tailL m.length

theorem tailL_length (n : ℕ) : (tailL n).length = 17 + (239 - n % 128) % 128 := by
  simp [tailL]; omega

theorem padL_length (m : List UInt8) : (padL m).length = 128*((m.length+16)/128+1) := by
  simp [padL, tailL_length]; omega

theorem pad_toList (m : ByteArray) : (pad512 m).data.toList = padL m.data.toList := by
  unfold pad512
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [Ideal.push_loop]
  have : (240-(m.size+1)%128)%128 = (239-m.size%128)%128 := by omega
  simp [padL, tailL, len16, this]

theorem strip_tail (l l' : List UInt8) (n n' : Nat) (h : l ++ tailL n = l' ++ tailL n') :
    l = l' := by
  unfold tailL at h
  rw [← List.cons_append, ← List.append_assoc, ← List.cons_append, ← List.append_assoc] at h
  have h1 := (List.append_inj' h (by simp)).1
  have h2 := congrArg List.reverse h1
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append] at h2
  have h3 := strip_zeros _ _ _ _ h2
  simpa using h3

theorem padL_injective : Function.Injective padL := fun _ _ h => strip_tail _ _ _ _ h

/-! ## Blocks -/

/-- Split a byte list into 128-byte blocks (a trailing partial block is dropped). -/
def blocksOf (l : List UInt8) : List Block512 :=
  (List.range (l.length / 128)).map fun k => Vector.ofFn fun j : Fin 128 => l.getD (k * 128 + j) 0

@[simp] theorem blocksOf_length (l : List UInt8) : (blocksOf l).length = l.length / 128 := by
  simp [blocksOf]

theorem blocksOf_cons (b : Block512) (l : List UInt8) : blocksOf (b.toList ++ l) = b :: blocksOf l := by
  unfold blocksOf
  rw [show (b.toList ++ l).length / 128 = l.length / 128 + 1 by simp, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  refine congrArg₂ List.cons ?_ (List.map_congr_left ?_)
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
    simp [hi]
  · intro k _
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Function.comp, Nat.succ_mul]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
      List.getD_eq_getElem?_getD]
    congr 2
    simp; omega

theorem blocksOf_flat (n : Nat) (l : List UInt8) (h : l.length = 128 * n) :
    (blocksOf l).flatMap Vector.toList = l := by
  induction n generalizing l with
  | zero =>
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; rfl
  | succ n ih =>
    let b : Block512 := ⟨(l.take 128).toArray, by simp; omega⟩
    have hl : l = b.toList ++ l.drop 128 := by simp [b]
    rw [hl, blocksOf_cons, List.flatMap_cons, ih _ (by simp; omega)]

theorem blocksOf_injective (l l' : List UInt8) (h : l.length % 128 = 0) (h' : l'.length % 128 = 0)
    (e : blocksOf l = blocksOf l') : l = l' := by
  rw [← blocksOf_flat (l.length / 128) l (by omega), ← blocksOf_flat (l'.length / 128) l' (by omega),
    e]

/-- The padded message, as a list of 128-byte blocks. -/
def padBlocks (msg : ByteArray) : List Block512 := blocksOf (padL msg.data.toList)

theorem padBlocks_length (msg : ByteArray) : (padBlocks msg).length = (msg.size + 16) / 128 + 1 := by
  simp [padBlocks, padL_length]

theorem padBlocks_injective : Function.Injective padBlocks := by
  intro a b h
  have h1 := blocksOf_injective _ _ (by rw [padL_length]; omega) (by rw [padL_length]; omega) h
  have h2 := padL_injective h1
  cases a; cases b
  simp at h2
  simp [h2]


def initial : Chain512 := ⟨iv512, rfl⟩

theorem chainAt512_toArray (s : Chain512) : chainAt512 s.toArray = s := by
  ext i hi
  simp [chainAt512, getElem!_pos, Vector.getElem_toArray, hi]

theorem fold_lift (g : CF Chain512 Block512) (p : ByteArray) (l : List ℕ) (s : Chain512) :
    l.foldl (fun st k => lift512 g st p (k*128)) s.toArray =
      (mdFold g s (l.map fun k => blockAt512 p (k*128))).toArray := by
  induction l generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons, List.map_cons, lift512, chainAt512_toArray]
    exact ih _

/-- SHA-512 uses the public compression table exactly once for each padded block. -/
theorem sha512_shape (g : CF Chain512 Block512) (msg : ByteArray) :
    sha512G (lift512 g) msg = stateBytes64 (mdFold g initial (padBlocks msg)).toArray := by
  unfold sha512G sha512FamilyG
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  rw [show iv512 = initial.toArray from rfl, fold_lift]
  rw [show ∀ st, (stateBytes64 st).extract 0 64 = stateBytes64 st by
    intro st; simpa using @ByteArray.extract_zero_size (stateBytes64 st)]
  apply congrArg (fun bs => stateBytes64 (mdFold g initial bs).toArray)
  unfold padBlocks blocksOf
  rw [← pad_toList, List.range_eq_range']
  simp only [blockAt512, ba_get]
  rw [show (pad512 msg).size = (pad512 msg).data.toList.length by rw [Array.length_toList]; rfl]
end MIdeal.Sha512

#print axioms MIdeal.Sha512.sha512_shape
#print axioms MIdeal.Sha512.padBlocks_injective

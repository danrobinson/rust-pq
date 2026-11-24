import MIdeal.MsgPrf512

namespace MIdeal.Sha512
open Ideal MLink SLHDSA SLHDSA.Concrete
variable (S : Sha2Set)

def seedBlock (pk : S.Node) : Block512 :=
  ⟨(key0L S pk).toArray, by
    simp [key0L]
    have : S.vp.params.n ≤ 128 := by cases S <;> decide
    omega⟩

theorem seedBlock_injective : Function.Injective (seedBlock S) := by
  intro x y h
  exact key0L_injective S (congrArg Vector.toList h)

def payload (xs : List S.Node) := xs.flatMap Vector.toList

theorem payload_length (xs : List S.Node) : (payload S xs).length = S.vp.params.n * xs.length := by
  induction xs with
  | nil => simp [payload]
  | cons x xs ih =>
    change (x.toList ++ payload S xs).length = _
    simp [ih, Nat.mul_add, Nat.add_comm]

theorem payload_injective : Function.Injective (payload S) := by
  have hn : 0 < S.vp.params.n := by cases S <;> decide
  intro xs
  induction xs with
  | nil =>
    intro ys h
    have e := congrArg List.length h
    rw [payload_length, payload_length] at e
    simpa [Nat.ne_of_gt hn] using e
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have e := congrArg List.length h
      simp [payload_length, Nat.ne_of_gt hn] at e
    | cons y ys =>
      obtain ⟨h₁,h₂⟩ := List.append_inj (show x.toList ++ payload S xs = y.toList ++ payload S ys from h) (by simp)
      rw [Vector.toList_inj.mp h₁, ih h₂]

theorem concat_payload (xs : List S.Node) : (concatBytes xs).data.toList = payload S xs := by
  unfold concatBytes
  suffices h : ∀ acc : ByteArray, (xs.foldl (fun out v => out ++ bytesToByteArray v) acc).data.toList =
      acc.data.toList ++ payload S xs by simpa using h ByteArray.empty
  induction xs with
  | nil => simp [payload]
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, ih]
    simp [payload, bytesToByteArray, Vector.toList]

/-- Blocks after the seed block for a SHA-512 tweakable hash invocation. -/
def thashBytes (a : Bytes 22) (xs : List S.Node) :=
  a.toList ++ payload S xs ++ tailL (150 + S.vp.params.n * xs.length)

def thashBlocks (a : Bytes 22) (xs : List S.Node) := blocksOf (thashBytes S a xs)

theorem thashBytes_length (a : Bytes 22) (xs : List S.Node) :
    (thashBytes S a xs).length = 128 * ((38 + S.vp.params.n * xs.length) / 128 + 1) := by
  simp only [thashBytes, List.length_append, Vector.length_toList, payload_length, tailL_length]
  omega

theorem thashBlocks_length (a : Bytes 22) (xs : List S.Node) :
    (thashBlocks S a xs).length = (38 + S.vp.params.n * xs.length) / 128 + 1 := by
  rw [thashBlocks, blocksOf_length, thashBytes_length]; omega

theorem thashBlocks_injective {a a' : Bytes 22} {xs ys : List S.Node}
    (h : thashBlocks S a xs = thashBlocks S a' ys) : a = a' ∧ xs = ys := by
  have e := blocksOf_injective _ _ (by rw [thashBytes_length]; omega) (by rw [thashBytes_length]; omega) h
  obtain ⟨ha,hx⟩ := List.append_inj (strip_tail _ _ _ _ e) (by simp)
  exact ⟨Vector.toList_inj.mp ha, payload_injective S hx⟩

/-- The first block after the public seed contains the full compressed address. -/
def readAddress (b : Block512) : Bytes 22 := Vector.ofFn fun i : Fin 22 => b[i.val]

theorem readAddress_first (a : Bytes 22) (xs : List S.Node) (b : Block512) (bs : List Block512)
    (h : thashBlocks S a xs = b :: bs) : readAddress b = a := by
  unfold thashBlocks blocksOf at h
  rw [thashBytes_length, Nat.mul_div_cancel_left _ (by decide : 0 < 128), List.range_succ_eq_map] at h
  simp only [List.map_cons] at h
  rw [← (List.cons.inj h).1]
  apply Vector.ext
  intro i hi
  simp only [readAddress, Vector.getElem_ofFn, thashBytes, List.append_assoc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  simp [hi]

theorem thash_wide (g : CompressionTables) (hw : S.vp.params.n ≠ 16) (pk : S.Node) (a : Bytes 22)
    (xs : List S.Node) (hm : xs.length ≠ 1) :
    (tablePrimitives g S.vp.params).Thash pk a xs =
      trunc S (mdFold g.2 (g.2 (initial, seedBlock S pk)) (thashBlocks S a xs)) := by
  have e : (sha2Prefix512Key pk a ++ concatBytes xs).data.toList =
      (seedBlock S pk).toList ++ (a.toList ++ payload S xs) := by
    simp only [sha2Prefix512Key, ByteArray.data_append, Array.toList_append, concat_payload]
    simp [seedBlock, key0L, bytesToByteArray, zeroByteArray, Vector.toList, List.append_assoc]
  have e₂ : padL ((seedBlock S pk).toList ++ (a.toList ++ payload S xs)) =
      (seedBlock S pk).toList ++ thashBytes S a xs := by
    simp [padL, thashBytes, List.append_assoc, payload_length]
    congr 1; omega
  change sha2ThashMixed (liftC g.1) (lift512 g.2) S.vp.params pk a xs = _
  simp only [sha2ThashMixed, ite_eq_right hm, ite_eq_right hw, sha512_shape, padBlocks, e, e₂,
    blocksOf_cons, mdFold, List.foldl_cons]
  exact prefix_eq S (serialize (mdFold g.2 (g.2 (initial, seedBlock S pk)) (thashBlocks S a xs)))
end MIdeal.Sha512

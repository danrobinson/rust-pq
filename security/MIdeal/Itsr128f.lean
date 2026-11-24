import MIdeal.Hmsg
import MIdeal.MsgPrf512
import Ideal.Games.Itsr

namespace MIdeal.Hmsg
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec VCVio.Algorithms.Sha2

/-- MGF1 keeps all of counter zero's digest and two bytes from counter one's digest. -/
def digest128f (s : St × St) : Bytes 34 :=
  Sha512.takeBytes 34 (by decide) (s.1 ++ s.2)

private theorem appendStates_bijective : Function.Bijective (fun s : St × St => s.1 ++ s.2) := by
  constructor
  · rintro ⟨a,b⟩ ⟨c,d⟩ h
    have e := congrArg Vector.toList h
    simp only [Vector.toList_append] at e
    obtain ⟨h₁,h₂⟩ := List.append_inj e (by simp)
    exact Prod.ext (Vector.toList_inj.mp h₁) (Vector.toList_inj.mp h₂)
  · intro s
    refine ⟨(Vector.ofFn (fun i : Fin 32 => s[i.val]), Vector.ofFn (fun i : Fin 32 => s[32+i.val])), ?_⟩
    apply Vector.ext
    intro i hi
    change ((Vector.ofFn (fun j : Fin 32 => s[j.val]) ++ Vector.ofFn (fun j : Fin 32 => s[32+j.val])) : Bytes 64)[i] = s[i]
    by_cases h : i < 32
    · rw [Vector.getElem_append_left h, Vector.getElem_ofFn]
    · rw [Vector.getElem_append_right hi (by omega), Vector.getElem_ofFn]
      simp only [show 32 + (i - 32) = i by omega]

theorem digest128f_uniform (P : Bytes 34 → Prop) :
    Pr{let u ← $ᵗ (St × St)}[P (digest128f u)] = Pr{let y ← $ᵗ (Bytes 34)}[P y] :=
  (SampleableType.prEvent_uniformSample_comp_of_bijective appendStates_bijective
    (fun s => P (Sha512.takeBytes 34 (by decide) s))).trans (Sha512.takeBytes_balanced 34 (by decide) P)

theorem digest128f_eq (a b : St) :
    byteArrayPrefixOrZero ((digestBytes a ++ digestBytes b).extract 0 34) 34 = digest128f (a,b) := by
  let v : Bytes 64 := a ++ b
  have app : digestBytes a ++ digestBytes b = bytesToByteArray v := by
    apply ByteArray.ext
    rw [ByteArray.data_append]
    rfl
  rw [app]
  have hraw : (((bytesToByteArray v).extract 0 34).extract 0 34).toList = v.toList.take 34 := by
    rw [ByteArray.toList_eq_toList_data, ByteArray.data_extract, Array.toList_extract,
      ByteArray.data_extract, Array.toList_extract]
    simp [bytesToByteArray, Vector.toList]
  have hl : (((bytesToByteArray v).extract 0 34).extract 0 34).toList.length = 34 := by
    rw [hraw]; simp
  simp only [byteArrayPrefixOrZero, byteArrayPrefixChecked, decodeExact, hl, dite_true]
  apply Vector.ext
  intro i hi
  simp [digest128f, Sha512.takeBytes, hraw, v]

theorem hmsg_128f_digest (g : CompressionTables) (r pk root : Bytes 16) (m : List Byte) :
    (tablePrimitives g Sha2Set.s128f.vp.params).Hmsg r pk root m =
      let s := mdFold g.1 IV128 (iblocksH r pk root m)
      let output := fun ctr => mdFold g.1 IV128 (counterBlocks r pk s ctr)
      digest128f (output 0, output 1) :=
  (hmsg_128f g r pk root m).trans (digest128f_eq _ _)

def counterPrefix (r pk : Bytes 16) (s : St) : Blk := (r ++ pk) ++ s

def counterFinal (ctr : UInt32) : Blk :=
  ⟨((u32be ctr).data.toList ++ tailL 68).toArray, by simp [u32be, tailL_length]⟩

theorem counterBlocks_pair (r pk : Bytes 16) (s : St) (ctr : UInt32) :
    counterBlocks r pk s ctr = [counterPrefix r pk s, counterFinal ctr] := by
  unfold counterBlocks padBlocks padL
  have shape : (bytesToByteArray r ++ bytesToByteArray pk ++ digestBytes s ++ u32be ctr).data.toList =
      (counterPrefix r pk s).toList ++ (u32be ctr).data.toList := by
    simp only [ByteArray.data_append, Array.toList_append, counterPrefix, Vector.toList_append]
    rfl
  rw [shape]
  have len : ((counterPrefix r pk s).toList ++ (u32be ctr).data.toList).length = 68 := by simp [u32be]
  rw [len, List.append_assoc, blocksOf_cons]
  apply congrArg (List.cons _)
  have raw : (counterFinal ctr).toList = (u32be ctr).data.toList ++ tailL 68 := by simp [counterFinal, Vector.toList]
  rw [← raw]
  rw [← List.append_nil (counterFinal ctr).toList, blocksOf_cons]
  rfl

theorem counterFinal_ne : counterFinal 0 ≠ counterFinal 1 := by decide +kernel

theorem counterPrefix_injective {r pk r' pk' : Bytes 16} {s s' : St}
    (h : counterPrefix r pk s = counterPrefix r' pk' s') : r = r' ∧ pk = pk' ∧ s = s' := by
  have e := congrArg Vector.toList h
  simp only [counterPrefix, Vector.toList_append] at e
  obtain ⟨h₁,h₂⟩ := List.append_inj e (by simp)
  obtain ⟨h₃,h₄⟩ := List.append_inj h₁ (by simp)
  exact ⟨Vector.toList_inj.mp h₃, Vector.toList_inj.mp h₄, Vector.toList_inj.mp h₂⟩

theorem hmsg_128f_cells (g : CompressionTables) (r pk root : Bytes 16) (m : List Byte) :
    (tablePrimitives g Sha2Set.s128f.vp.params).Hmsg r pk root m =
      let innerState := mdFold g.1 IV128 (iblocksH r pk root m)
      let common := g.1 (IV128, counterPrefix r pk innerState)
      digest128f (g.1 (common, counterFinal 0), g.1 (common, counterFinal 1)) := by
  rw [hmsg_128f_digest]
  simp only [counterBlocks_pair, mdFold, List.foldl_cons, List.foldl_nil]
  rfl

private theorem twoCells_uniform {D : Type} [Fintype D] [SampleableType (D → St)]
    (x y : D) (ne : x ≠ y) (P : Bytes 34 → Prop) :
    Pr{let g ← $ᵗ (D → St)}[P (digest128f (g x, g y))] = Pr{let z ← $ᵗ (Bytes 34)}[P z] := by
  classical
  let Rest := {z : D // z ≠ x ∧ z ≠ y}
  let split (g : D → St) : (St × St) × (Rest → St) := ((g x, g y), fun z => g z.val)
  have bij : Function.Bijective split := by
    constructor
    · intro f g eq
      obtain ⟨h₁,h₂⟩ := Prod.mk.inj eq
      obtain ⟨hx,hy⟩ := Prod.mk.inj h₁
      funext z
      by_cases h : z = x
      · simpa [h] using hx
      by_cases h' : z = y
      · simpa [h'] using hy
      exact congrFun h₂ (⟨z,h,h'⟩ : Rest)
    · rintro ⟨⟨a,b⟩,other⟩
      refine ⟨fun z => if h : z = x then a else if h' : z = y then b else other ⟨z,h,h'⟩, ?_⟩
      apply Prod.ext
      · simp [split, ne.symm]
      · funext z
        simp [split,z.property.1,z.property.2]
  exact (SampleableType.prEvent_uniformSample_comp_of_bijective bij (fun z => P (digest128f z.1))).trans
    ((SampleableType.prEvent_uniformSample_fst (fun z => P (digest128f z))).trans (digest128f_uniform P))

/-- A fresh compression table gives the exact uniform digest at every fixed common state. -/
theorem freshCounterDigest_uniform (c : St) (P : Bytes 34 → Prop) :
    Pr{let g ← $ᵗ (CF St Blk)}[P (digest128f (g (c, counterFinal 0), g (c, counterFinal 1)))] =
      Pr{let y ← $ᵗ (Bytes 34)}[P y] :=
  twoCells_uniform _ _ (fun h => counterFinal_ne (congrArg Prod.snd h)) P

namespace Fast128
open Ideal.Itsr

abbrev Input := Bytes 16 × Bytes 16 × Bytes 16 × List Byte

def innerBlocks (x : Input) := iblocksH x.1 x.2.1 x.2.2.1 x.2.2.2

def prefixCell (g : CF St Blk) (x : Input) : St × Blk :=
  (IV128, counterPrefix x.1 x.2.1 (mdFold g IV128 (innerBlocks x)))

def rowDigest (g : CF St Blk) (row : St) := digest128f (g (row, counterFinal 0), g (row, counterFinal 1))

def cells (g : CF St Blk) (x : Input) :=
  mdCells g IV128 (innerBlocks x) ++ [prefixCell g x, (g (prefixCell g x), counterFinal 0),
    (g (prefixCell g x), counterFinal 1)]

theorem row_injective (g : CF St Blk) (visited : List (St × Blk))
    (hinj : ∀ z ∈ visited, ∀ z' ∈ visited, g z = g z' → z = z')
    (hIV : ∀ z ∈ visited, g z ≠ IV128) (x y : Input)
    (hx : ∀ z ∈ cells g x, z ∈ visited) (hy : ∀ z ∈ cells g y, z ∈ visited)
    (h : g (prefixCell g x) = g (prefixCell g y)) : x = y := by
  have hp := congrArg Prod.snd (hinj _ (hx _ (by simp [cells])) _ (hy _ (by simp [cells])) h)
  have hs := (counterPrefix_injective hp).2.2
  have eqB := md_inj g IV128 visited hinj hIV _ _ (fun z hz => hx z (by simp [cells,hz]))
    (fun z hz => hy z (by simp [cells,hz])) hs
  obtain ⟨hr,hp,hk,hm⟩ := iblocksH_injective eqB
  exact Prod.ext hr (Prod.ext hp (Prod.ext hk hm))

/-- On a collision-free trace, a successful fresh candidate exhibits coverage among the
digests of the visited rows, including when a counter cell was first read by the adversary. -/
theorem win_row_coverage {Index : Type} (idx : Bytes 34 → List Index) (g : CF St Blk)
    (visited : List (St × Blk)) (rows : List St) (cand : Input) (targets : List Input)
    (hcells : ∀ x ∈ cand :: targets, ∀ z ∈ cells g x, z ∈ visited)
    (hrows : ∀ z ∈ visited, z.1 ∈ rows)
    (hinj : ∀ z ∈ visited, ∀ z' ∈ visited, g z = g z' → z = z')
    (hIV : ∀ z ∈ visited, g z ≠ IV128) (hfresh : cand ∉ targets)
    (hwin : ∀ i ∈ idx (rowDigest g (g (prefixCell g cand))),
      i ∈ targets.flatMap (fun x => idx (rowDigest g (g (prefixCell g x))))) :
    CovP idx (rows.map (rowDigest g)) := by
  have logged (x : Input) (hx : x ∈ cand :: targets) : g (prefixCell g x) ∈ rows :=
    hrows (_,counterFinal 0) (hcells x hx _ (by simp [cells]))
  obtain ⟨pre,post,eq⟩ := List.append_of_mem (logged cand (by simp))
  refine ⟨pre.map (rowDigest g), rowDigest g (g (prefixCell g cand)), post.map (rowDigest g),
    by rw [eq]; simp, fun i hi => ?_⟩
  obtain ⟨x,hx,hit⟩ := List.mem_flatMap.mp (hwin i hi)
  have ne : g (prefixCell g x) ≠ g (prefixCell g cand) := by
    intro h
    have ex := row_injective g visited hinj hIV x cand (hcells x (by simp [hx])) (hcells cand (by simp)) h
    exact hfresh (ex ▸ hx)
  have mem := logged x (by simp [hx])
  rw [eq] at mem
  refine ⟨_, ?_, hit⟩
  simpa [List.mem_append,List.mem_cons,ne] using
    (show rowDigest g (g (prefixCell g x)) ∈ (pre ++ post).map (rowDigest g) from
      List.mem_map_of_mem (by simpa [List.mem_append,List.mem_cons,ne] using mem))

open Ideal.HP Ideal.Prf AnswerTape
/-- A program can choose its compression queries adaptively. Its visited rows supply at
most as much coverage as the same number of independent 34-byte digests. -/
theorem adaptive_row_coverage {α Index : Type} (idx : Bytes 34 → List Index)
    (oa : OracleComp (unifSpec + mS St Blk) α) (Q : ℕ)
    (hq : IsQueryBoundP oa (fun i => i.isRight = true) Q) :
    prT ($ᵗ (St → Blk → St) >>= fun g =>
      (simulateQ (stImpl (fun (t : (St × Blk) × Bool) => g t.1.1 t.1.2)
        (logU (fun t : (St × Blk) × Bool => t.1.1))) oa).run [] >>= fun z =>
      pure (covB idx (z.2.map (fun c => rowDigest (Function.uncurry g) c)))) ≤
      prT (tapeList (Bytes 34) Q >>= fun r => pure (covB idx r)) := by
  exact prT_tape_le (V := Blk → St) (spec := mS St Blk) (fun t => t.1.1) (fun g t => g t.1.1 t.1.2)
    (fun _ _ t h => congrFun h t.1.2) (fun row => digest128f (row (counterFinal 0),row (counterFinal 1)))
    (twoCells_uniform _ _ counterFinal_ne) _ (covB_mono idx) oa Q hq

end Fast128
end MIdeal.Hmsg

#print axioms MIdeal.Hmsg.digest128f_uniform
#print axioms MIdeal.Hmsg.hmsg_128f_digest

#print axioms MIdeal.Hmsg.hmsg_128f_cells

#print axioms MIdeal.Hmsg.freshCounterDigest_uniform

#print axioms MIdeal.Hmsg.Fast128.win_row_coverage

#print axioms MIdeal.Hmsg.Fast128.adaptive_row_coverage

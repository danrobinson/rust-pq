import Ideal.Sha.Shape

/-!
# Shape of `H_msg` at SLH-DSA-SHA2-128s

`H_msg(R, pk, root, M) = MGF1-SHA-256(R ‖ pk ‖ SHA-256(R ‖ pk ‖ root ‖ M), 30)`; since `30 ≤ 32`
MGF1 is one SHA-256 call.  For every table `g : CF St Blk` (`hmsg_shape`):

`(primsG (liftC g)).Hmsg R pk root M
   = dig30 (mdFold g IV128 (oblocksH R pk (mdFold g IV128 (iblocksH R pk root M))))`

where `iblocksH R pk root M` are the padded blocks of `R ‖ pk ‖ root ‖ M`, `oblocksH R pk s` the two
padded blocks of `R ‖ pk ‖ s ‖ 0^4` (68 bytes) and `dig30` the first 30 bytes of the state.
-/

namespace Ideal

open SLHDSA SLHDSA.Concrete VCVio.Algorithms.Sha2

/-- The inner hash input `R ‖ pk ‖ root ‖ M`. -/
def hInner (R pk root : Bytes 16) (M : List UInt8) : ByteArray :=
  bytesToByteArray R ++ bytesToByteArray pk ++ bytesToByteArray root ++ ByteArray.mk M.toArray

/-- The outer (MGF1, counter 0) hash input `R ‖ pk ‖ s ‖ 0^4`. -/
def hOuter (R pk : Bytes 16) (s : St) : ByteArray :=
  bytesToByteArray R ++ bytesToByteArray pk ++ digestBytes s ++ u32be 0

/-- The padded blocks of the inner hash input. -/
def iblocksH (R pk root : Bytes 16) (M : List UInt8) : List Blk := padBlocks (hInner R pk root M)

/-- The (two) padded blocks of the outer hash input. -/
def oblocksH (R pk : Bytes 16) (s : St) : List Blk := padBlocks (hOuter R pk s)

/-- First 30 bytes of the chaining value (the `H_msg` digest). -/
def dig30 (s : St) : Bytes 30 := Vector.ofFn fun i : Fin 30 => s[i.val]

theorem hInner_toList (R pk root : Bytes 16) (M : List UInt8) :
    (hInner R pk root M).data.toList = R.toList ++ (pk.toList ++ (root.toList ++ M)) := by
  simp [hInner, bytesToByteArray, Vector.toList]

theorem hOuter_toList (R pk : Bytes 16) (s : St) :
    (hOuter R pk s).data.toList = R.toList ++ (pk.toList ++ (s.toList ++ [0, 0, 0, 0])) := by
  simp [hOuter, bytesToByteArray, Vector.toList, u32be]

theorem hInner_size (R pk root : Bytes 16) (M : List UInt8) :
    (hInner R pk root M).size = 48 + M.length := by
  rw [show (hInner R pk root M).size = (hInner R pk root M).data.toList.length by
    rw [Array.length_toList]; rfl, hInner_toList]
  simp; omega

theorem hOuter_size (R pk : Bytes 16) (s : St) : (hOuter R pk s).size = 68 := by
  rw [show (hOuter R pk s).size = (hOuter R pk s).data.toList.length by
    rw [Array.length_toList]; rfl, hOuter_toList]
  simp

/-- Number of inner blocks. -/
theorem iblocksH_length (R pk root : Bytes 16) (M : List UInt8) :
    (iblocksH R pk root M).length = (M.length + 56) / 64 + 1 := by
  rw [iblocksH, padBlocks_length, hInner_size]; omega

/-- The outer hash input has two blocks. -/
theorem oblocksH_length (R pk : Bytes 16) (s : St) : (oblocksH R pk s).length = 2 := by
  rw [oblocksH, padBlocks_length, hOuter_size]

/-- The inner blocks determine `(R, pk, root, M)`. -/
theorem iblocksH_injective {R pk root R' pk' root' : Bytes 16} {M M' : List UInt8}
    (h : iblocksH R pk root M = iblocksH R' pk' root' M') :
    R = R' ∧ pk = pk' ∧ root = root' ∧ M = M' := by
  have h1 := congrArg (fun b : ByteArray => b.data.toList) (padBlocks_injective h)
  simp only [hInner_toList] at h1
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  obtain ⟨h4, h5⟩ := List.append_inj h3 (by simp)
  obtain ⟨h6, h7⟩ := List.append_inj h5 (by simp)
  exact ⟨Vector.toList_inj.mp h2, Vector.toList_inj.mp h4, Vector.toList_inj.mp h6, h7⟩

/-- The outer blocks determine `(R, pk, s)`. -/
theorem oblocksH_injective {R pk R' pk' : Bytes 16} {s s' : St}
    (h : oblocksH R pk s = oblocksH R' pk' s') : R = R' ∧ pk = pk' ∧ s = s' := by
  have h1 := congrArg (fun b : ByteArray => b.data.toList) (padBlocks_injective h)
  simp only [hOuter_toList] at h1
  obtain ⟨h2, h3⟩ := List.append_inj h1 (by simp)
  obtain ⟨h4, h5⟩ := List.append_inj h3 (by simp)
  obtain ⟨h6, -⟩ := List.append_inj h5 (by simp)
  exact ⟨Vector.toList_inj.mp h2, Vector.toList_inj.mp h4, Vector.toList_inj.mp h6⟩

theorem prefix_dig30 (s : St) :
    byteArrayPrefixOrZero ((bytesToByteArray s).extract 0 30) 30 = dig30 s := by
  have hraw : (((bytesToByteArray s).extract 0 30).extract 0 30).toList = s.toList.take 30 := by
    rw [ByteArray.toList_eq_toList_data, ByteArray.data_extract, Array.toList_extract,
      ByteArray.data_extract, Array.toList_extract]
    simp [bytesToByteArray, Vector.toList]
  have hl : (((bytesToByteArray s).extract 0 30).extract 0 30).toList.length = 30 := by
    rw [hraw]; simp
  simp only [byteArrayPrefixOrZero, byteArrayPrefixChecked, decodeExact, hl, dite_true]
  apply Vector.ext
  intro i hi
  simp [dig30, hraw]

/-- One-block MGF1 over a table. -/
theorem mgf1G_30 (c : CompressFn) (seed : ByteArray) :
    mgf1G c seed 30 = (sha256G c (seed ++ u32be 0)).extract 0 30 := by
  unfold mgf1G
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp

/-- **Shape of `H_msg` at SLH-DSA-SHA2-128s over a table.** -/
theorem hmsg_shape (g : CF St Blk) (R pk root : Bytes 16) (M : List UInt8) :
    (primsG (liftC g)).Hmsg R pk root M =
      dig30 (mdFold g IV128 (oblocksH R pk (mdFold g IV128 (iblocksH R pk root M)))) := by
  show sha2HmsgG (liftC g) Link.vp.params R pk root M = _
  have h : sha2HmsgG (liftC g) Link.vp.params R pk root M =
      byteArrayPrefixOrZero (mgf1G (liftC g) (bytesToByteArray R ++ bytesToByteArray pk ++
        sha256G (liftC g) (hInner R pk root M)) 30) 30 := rfl
  rw [h, mgf1G_30, sha256G_shape, sha256G_shape, prefix_dig30]
  rfl

/-! ## `dig30` of a uniform chaining value is uniform -/

/-- Last 2 bytes of the chaining value. -/
def lo2 (s : St) : Bytes 2 := Vector.ofFn fun i : Fin 2 => s[i.val + 30]

theorem split30_bijective : Function.Bijective fun s : St => (dig30 s, lo2 s) := by
  constructor
  · intro s t h
    simp only [Prod.mk.injEq] at h
    apply Vector.ext
    intro i hi
    by_cases h30 : i < 30
    · have := congrArg (fun v : Bytes 30 => v[i]) h.1
      simpa [dig30] using this
    · have := congrArg (fun v : Bytes 2 => v[i - 30]'(by omega)) h.2
      simp only [lo2, Vector.getElem_ofFn] at this
      simpa [show i - 30 + 30 = i by omega] using this
  · rintro ⟨a, b⟩
    refine ⟨Vector.ofFn fun i : Fin 32 => if h : i.val < 30 then a[i.val] else b[i.val - 30], ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · apply Vector.ext; intro i hi; simp [dig30]
    · apply Vector.ext; intro i hi; simp [lo2]

open OracleComp in
/-- Events of `dig30` of a uniform chaining value are events of a uniform 30-byte string. -/
theorem prEvent_dig30 (p : Bytes 30 → Prop) :
    Pr{let u ← $ᵗ St}[p (dig30 u)] = Pr{let y ← $ᵗ (Bytes 30)}[p y] :=
  (SampleableType.prEvent_uniformSample_comp_of_bijective split30_bijective (fun z => p z.1)).trans
    (SampleableType.prEvent_uniformSample_fst p)

open OracleComp in
/-- `dig30 <$> $ᵗ St` is uniform on `Bytes 30`. -/
theorem dig30_uniform :
    (dig30 <$> ($ᵗ St : ProbComp St)) =ᵈ ($ᵗ (Bytes 30) : ProbComp (Bytes 30)) := by
  apply OracleComp.evalDistEq_of_forall_prEvent_eq_output
  intro y
  rw [prEvent_map]
  exact prEvent_dig30 (· = y)

end Ideal

#print axioms Ideal.hmsg_shape
#print axioms Ideal.iblocksH_injective
#print axioms Ideal.oblocksH_injective
#print axioms Ideal.oblocksH_length
#print axioms Ideal.iblocksH_length
#print axioms Ideal.dig30_uniform

import Metal.Command
import Metal.Pipeline
import Metal.SignatureLayout

/-! Values of an observed command execution are stable after their unique writer.
A kernel's local refinement may rely on its inputs, but only on the resources its
source-derived binding trace actually reads. A strict producer epoch makes these
local obligations compositional, including concurrent producers in one epoch. -/

namespace MetalCommandValues
open MetalCommand MetalSignatureLayout

/-- A checked row-major dispatch can be evaluated at its symbolic coordinates.
The two component projections used by the source replay follow directly; an
arbitrary number of outer dimensions is handled by repeated application. -/
theorem decode (outer digit stride : Nat) (within : digit < stride) :
    (outer * stride + digit) / stride = outer ∧
    (outer * stride + digit) % stride = digit := by
  have pos : 0 < stride := by omega
  rw [Nat.mul_comm outer stride, Nat.mul_add_div pos, Nat.div_eq_of_lt within,
    Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt within]
  exact ⟨rfl,rfl⟩

theorem active (outer digit stride count : Nat) (row : outer < count) (col : digit < stride) :
    outer * stride + digit < count * stride := by
  have bound := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt row)
  rw [Nat.succ_mul] at bound
  omega

theorem rebase (row inner width stride word : Nat) :
    ((row * width + inner) * stride + word) - row * (width * stride) =
      inner * stride + word := by
  rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.add_sub_cancel_left]

def owner (g : Geometry) : Node g → Region
  | .inl _ => .randomizer
  | .inr (.inl (_, .inr (.inr _))) => .forsHigh
  | .inr (.inl _) => .forsLow
  | .inr (.inr (_, .inl _)) => .wots
  | .inr (.inr (_, .inr _)) => .xmssAuth

/-- A property of final values for one execution and request, indexed by
region. The host initializer is a producer with no dependencies. -/
def Local (trace : List Access) (correct : Region → Prop) : Prop :=
  ∀ a ∈ trace, (∀ r ∈ a.reads, correct r) → ∀ r ∈ a.writes, correct r

theorem writes_correct {trace : List Access} (safeTrace : safe trace = true)
    {correct : Region → Prop} (localRule : Local trace correct)
    {a : Access} (ha : a ∈ trace) {r : Region} (hr : r ∈ a.writes) : correct r := by
  suffices ∀ n, ∀ b ∈ trace, b.epoch = n → ∀ s ∈ b.writes, correct s from
    this a.epoch a ha rfl r hr
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro b hb eq
    apply localRule b hb
    intro s hs
    obtain ⟨writer, hw, earlier, hs'⟩ := produced safeTrace hb hs
    exact ih writer.epoch (eq ▸ earlier) writer hw rfl s hs'

/-- Which signature bytes a value contract has to supply. Separate scratch
regions can have independent invariants (e.g. a vector of subtree roots). -/
def correct (g : Geometry) (count : Nat) (out expected : Spec.Bytes) (scratch : Region → Prop)
    (r : Region) : Prop :=
  scratch r ∧ ∀ b : Byte g count, owner g b.2.1 = r →
      out[address g b]? = expected[address g b]?

/-- Every region of a GPU result has exactly one earlier producer, given the
actual final CPU read record. The empty high pass has no inhabitant. -/
def signatureReads (split : Bool) : List Region :=
  [.randomizer, .forsLow, .xmssAuth, .wots] ++ (if split then [.forsHigh] else [])

theorem published {trace : List Access} (safeTrace : safe trace = true)
    (g : Geometry) (split : Bool) (noHigh : split = false → g.s2 = 0)
    (reader : Access) (hr : reader ∈ trace) (reads : reader.reads = signatureReads split)
    {count : Nat} (b : Byte g count) : ∃ a ∈ trace, owner g b.2.1 ∈ a.writes := by
  have hb : owner g b.2.1 ∈ reader.reads := by
    rw [reads]
    rcases b with ⟨_, field, _⟩
    rcases field with x | ⟨tree,secret | (lo | hi)⟩ | ⟨layer,chain | auth⟩ <;>
      cases split <;> simp_all [owner, signatureReads]
    exact Fin.elim0 (noHigh ▸ hi)
  obtain ⟨a, ha, _, hw⟩ := produced safeTrace hr hb
  exact ⟨a,ha,hw⟩

/-- Internal signing result of a completed source-derived command trace, for an
arbitrary message, secret key and randomizer. The producer contracts for the
observed shader execution and host inputs are explicit hypotheses. -/
theorem sign_internal {trace : List Access} (safeTrace : safe trace = true)
    (p : Spec.Params) (hv : p.Valid) (mode : MetalPipeline.XmssMode)
    (g : Geometry) (geometry : signatureBytes g = p.sigBytes)
    (msg sk addrnd out : Spec.Bytes) (allocated : out.length = p.sigBytes)
    (scratch : Region → Prop)
    (published : ∀ b : Byte g 1, ∃ a ∈ trace, owner g b.2.1 ∈ a.writes)
    (localRule : Local trace (correct g 1 out (MetalPipeline.metalSignInternal mode p msg sk addrnd) scratch)) :
    out = Spec.slhSignInternal p msg sk addrnd := by
  have model := MetalPipeline.metal_sign_internal_eq_fips mode p hv msg sk addrnd
  rw [model] at localRule
  apply List.ext_getElem
  · rw [allocated, Spec.slhSignInternal_length p hv]
  · intro pos hout href
    obtain ⟨b, hb, _⟩ := cover g (count := 1) (pos := pos) (by simpa [geometry, allocated] using hout)
    obtain ⟨a, ha, hw⟩ := published b
    have eq := (writes_correct safeTrace localRule ha hw).2 b rfl
    rw [hb, List.getElem?_eq_getElem hout, List.getElem?_eq_getElem href] at eq
    exact Option.some.inj eq

/-- Every returned byte in a completed multi-signature buffer. Both batch
order and the last byte of the last signature are covered by the layout. -/
theorem batch_internal {trace : List Access} (safeTrace : safe trace = true)
    (p : Spec.Params) (hv : p.Valid) (mode : MetalPipeline.XmssMode)
    (g : Geometry) (geometry : signatureBytes g = p.sigBytes)
    (reqs : List MetalPipeline.BatchSignReq) (out : Spec.Bytes)
    (allocated : out.length = reqs.length * p.sigBytes) (scratch : Region → Prop)
    (published : ∀ b : Byte g reqs.length, ∃ a ∈ trace, owner g b.2.1 ∈ a.writes)
    (localRule : Local trace (correct g reqs.length out
      (MetalPipeline.metalBatchSignInternal mode p reqs).flatten scratch)) :
    out = reqs.flatMap (fun r => Spec.slhSignInternal p r.msg r.sk r.addrnd) := by
  rw [MetalPipeline.metal_batch_sign_internal_eq_fips mode p hv, ← List.flatMap_def] at localRule
  have len : ∀ rs : List MetalPipeline.BatchSignReq,
      (rs.flatMap (fun r => Spec.slhSignInternal p r.msg r.sk r.addrnd)).length =
        rs.length * p.sigBytes := by
    intro rs
    induction rs with
    | nil => simp
    | cons r rs ih =>
      simp [ih, Spec.slhSignInternal_length p hv, Nat.succ_mul, Nat.add_comm]
  apply List.ext_getElem (allocated.trans (len reqs).symm)
  intro pos hout href
  obtain ⟨b, hb, _⟩ := cover g (count := reqs.length) (pos := pos)
    (by simpa [geometry, allocated] using hout)
  obtain ⟨a, ha, hw⟩ := published b
  have eq := (writes_correct safeTrace localRule ha hw).2 b rfl
  rw [hb, List.getElem?_eq_getElem hout, List.getElem?_eq_getElem href] at eq
  exact Option.some.inj eq

def resultSlices (count width : Nat) (out : Spec.Bytes) : List Spec.Bytes :=
  (List.range count).map (fun i => (out.drop (i * width)).take width)

theorem slices_flatten (xs : List Spec.Bytes) (w : Nat) (len : ∀ s ∈ xs, s.length = w) :
    resultSlices xs.length w xs.flatten = xs := by
  induction xs with
  | nil => simp [resultSlices]
  | cons x xs ih =>
    have hx := len x (by simp)
    have rest : ∀ s ∈ xs, s.length = w := fun s hs => len s (by simp [hs])
    have drop (i : Nat) : (x ++ xs.flatten).drop ((i+1)*w) = xs.flatten.drop (i*w) := by
      rw [Nat.succ_mul, Nat.add_comm, ← hx]
      exact List.drop_length_add_append _
    simp only [resultSlices, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.flatten_cons, List.map_map, Function.comp_def, Nat.zero_mul, List.drop_zero]
    rw [List.take_left' hx]
    congr 1
    simpa only [resultSlices, Nat.succ_eq_add_one, drop] using ih rest

def framed (rs : List MetalPipeline.BatchSignReq) :=
  rs.map fun r => {r with msg := Spec.withContext r.msg r.ctx}

/-- Public host operation, including Algorithm 22 context rejection and the
post-completion flat-buffer slice loop of sign_internal_batch_family. -/
def publicResult (p : Spec.Params) (rs : List MetalPipeline.BatchSignReq) (out : Spec.Bytes) :=
  if rs.any (fun r => decide (r.ctx.length > 255)) then none
  else some (resultSlices rs.length p.sigBytes out)

theorem public_empty (p : Spec.Params) (out : Spec.Bytes) :
    publicResult p [] out = some [] := by rfl

theorem public_reject (p : Spec.Params) (rs : List MetalPipeline.BatchSignReq)
    (out : Spec.Bytes) (bad : ∃ r ∈ rs, 255 < r.ctx.length) :
    publicResult p rs out = none := by
  have test : rs.any (fun r => decide (r.ctx.length > 255)) = true := by simpa using bad
  simp [publicResult, test]

theorem public_batch {trace : List Access} (safeTrace : safe trace = true)
    (p : Spec.Params) (hv : p.Valid) (mode : MetalPipeline.XmssMode)
    (g : Geometry) (geometry : signatureBytes g = p.sigBytes)
    (rs : List MetalPipeline.BatchSignReq) (out : Spec.Bytes) (scratch : Region → Prop)
    (accepted : rs.any (fun r => decide (r.ctx.length > 255)) = false →
      out.length = rs.length * p.sigBytes ∧
      (∀ b : Byte g (framed rs).length, ∃ a ∈ trace, owner g b.2.1 ∈ a.writes) ∧
      Local trace (correct g (framed rs).length out
        (MetalPipeline.metalBatchSignInternal mode p (framed rs)).flatten scratch)) :
    publicResult p rs out = rs.mapM (fun r => Spec.slhSign p r.msg r.ctx r.sk r.addrnd) := by
  rw [← MetalPipeline.metal_batch_sign_eq_fips mode p hv]
  unfold publicResult MetalPipeline.metalBatchSign
  split <;> rename_i guard
  · rfl
  · simp only [Bool.not_eq_true] at guard
    obtain ⟨alloc, pub, rule⟩ := accepted guard
    have n : (framed rs).length = rs.length := by simp [framed]
    have outEq := batch_internal safeTrace p hv mode g geometry (framed rs) out
      (n ▸ alloc) scratch pub rule
    rw [outEq]
    change some _ = some (MetalPipeline.metalBatchSignInternal mode p (framed rs))
    rw [MetalPipeline.metal_batch_sign_internal_eq_fips mode p hv]
    congr 1
    let signatures := (framed rs).map (fun r => Spec.slhSignInternal p r.msg r.sk r.addrnd)
    have ns : signatures.length = rs.length := by simp [signatures,n]
    have lengths : ∀ s ∈ signatures, s.length = p.sigBytes := by
      simp only [signatures,List.mem_map]
      rintro _ ⟨r,_,rfl⟩
      exact Spec.slhSignInternal_length p hv _ _ _
    exact ns ▸ slices_flatten signatures p.sigBytes lengths

/-- GPU pool allocations may have spare capacity. The Rust slice loop never
reads those trailing bytes, including when reusing a larger previous batch. -/
theorem slices_prefix (count width : Nat) (pool : Spec.Bytes) :
    resultSlices count width (pool.take (count * width)) = resultSlices count width pool := by
  unfold resultSlices
  apply List.map_congr_left
  intro i hi
  have inRange := List.mem_range.mp hi
  have bound := Nat.mul_le_mul_right width (Nat.succ_le_of_lt inRange)
  rw [Nat.succ_mul] at bound
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

theorem public_pooled_batch {trace : List Access} (safeTrace : safe trace = true)
    (p : Spec.Params) (hv : p.Valid) (mode : MetalPipeline.XmssMode)
    (g : Geometry) (geometry : signatureBytes g = p.sigBytes)
    (rs : List MetalPipeline.BatchSignReq) (pool : Spec.Bytes) (scratch : Region → Prop)
    (accepted : rs.any (fun r => decide (r.ctx.length > 255)) = false →
      rs.length * p.sigBytes ≤ pool.length ∧
      (∀ b : Byte g (framed rs).length, ∃ a ∈ trace, owner g b.2.1 ∈ a.writes) ∧
      Local trace (correct g (framed rs).length (pool.take (rs.length*p.sigBytes))
        (MetalPipeline.metalBatchSignInternal mode p (framed rs)).flatten scratch)) :
    publicResult p rs pool = rs.mapM (fun r => Spec.slhSign p r.msg r.ctx r.sk r.addrnd) := by
  have h := public_batch safeTrace p hv mode g geometry rs (pool.take (rs.length*p.sigBytes)) scratch
    (fun guard => ⟨by simp [List.length_take, Nat.min_eq_left (accepted guard).1],
                   (accepted guard).2⟩)
  simpa only [publicResult,slices_prefix] using h

end MetalCommandValues

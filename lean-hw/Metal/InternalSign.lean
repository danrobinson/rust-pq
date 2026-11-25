import Metal.Completion

namespace MetalInternalSign
open Spec MetalPipeline MetalCommandValues MetalCommand MetalSignatureLayout

/-- The internal public API accepts message bytes directly and always returns
a vector on success. Its slice loop is shared with the framed API. -/
def returned (p : Params) (rs : List BatchSignReq) (pool : Bytes) :=
  resultSlices rs.length p.sigBytes pool

theorem pooled {trace : List Access} (safeTrace : safe trace = true)
    (p : Params) (hv : p.Valid) (mode : XmssMode)
    (g : Geometry) (geometry : signatureBytes g = p.sigBytes)
    (rs : List BatchSignReq) (pool : Bytes) (scratch : Region → Prop)
    (accepted : True → rs.length*p.sigBytes ≤ pool.length ∧
      (∀ b : MetalSignatureLayout.Byte g rs.length, ∃ a ∈ trace, owner g b.2.1 ∈ a.writes) ∧
      Local trace (correct g rs.length (pool.take (rs.length*p.sigBytes)) (metalBatchSignInternal mode p rs).flatten scratch)) :
    returned p rs pool = rs.map (fun r => slhSignInternal p r.msg r.sk r.addrnd) := by
  obtain ⟨alloc,pub,rule⟩ := accepted trivial
  let sigs := rs.map fun r => slhSignInternal p r.msg r.sk r.addrnd
  have buffer := batch_internal safeTrace p hv mode g geometry rs (pool.take (rs.length*p.sigBytes))
    (by simp [List.length_take,Nat.min_eq_left alloc]) scratch pub rule
  have full : pool.take (rs.length*p.sigBytes) = sigs.flatten := by simpa [sigs,List.flatMap_def] using buffer
  unfold returned
  rw [← slices_prefix _ _ pool,full]
  have len : sigs.length=rs.length := by simp [sigs]
  rw [← len]
  apply slices_flatten
  intro s hs
  rcases List.mem_map.mp hs with ⟨r,_,rfl⟩
  exact slhSignInternal_length p hv _ _ _

def api (p : Params) (rs : List BatchSignReq) (exit : MetalCompletion.Exit) (pool : Unit → Bytes) :
    Except MetalCompletion.Error (List Bytes) :=
  if rs.isEmpty then .ok [] else MetalCompletion.afterWait exit (fun _ => returned p rs (pool ()))

theorem success (p : Params) (rs : List BatchSignReq) (exit : MetalCompletion.Exit) (pool : Unit → Bytes)
    (out : List Bytes) (ok : api p rs exit pool = .ok out) : out = returned p rs (pool ()) := by
  cases rs with
  | nil => simpa [api,returned,resultSlices,eq_comm] using ok
  | cons r rs =>
    simp only [api,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte] at ok
    exact ((MetalCompletion.wait_success _ _ _).mp ok).2

end MetalInternalSign

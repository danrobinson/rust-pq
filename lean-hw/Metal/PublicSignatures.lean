import Metal.InternalSign

namespace MetalPublicSignatures
open Spec MetalPipeline MetalCompletion

abbrev Raw := List BatchSignReq → Except Error (List Bytes)
abbrev Outer := List BatchSignReq → Except Error (Option (List Bytes))
def RawSpec (p : Params) (raw : Raw) :=
  ∀ rs out, raw rs = .ok out → out = rs.map (fun r => slhSignInternal p r.msg r.sk r.addrnd)
def OuterSpec (p : Params) (outer : Outer) :=
  ∀ rs out, outer rs = .ok out → out = rs.mapM (fun r => slhSign p r.msg r.ctx r.sk r.addrnd)

def rawSingle (raw : Raw) (msg sk rnd : Bytes) :=
  (raw [⟨msg,[],sk,rnd⟩]).map List.getLast!

theorem raw_single (p : Params) (raw : Raw) (sound : RawSpec p raw)
    (msg sk rnd out : Bytes) (returned : rawSingle raw msg sk rnd = .ok out) :
    out=slhSignInternal p msg sk rnd := by
  cases run : raw [⟨msg,[],sk,rnd⟩] with
  | error error => simp [rawSingle,run,Except.map] at returned
  | ok xs =>
    have values := sound _ _ run
    simpa [rawSingle,run,values,Except.map,eq_comm] using returned

def single (raw : Raw) (msg ctx sk rnd : Bytes) : Except Error (Option Bytes) :=
  if ctx.length>255 then .ok none else (rawSingle raw (withContext msg ctx) sk rnd).map some

theorem single_sign (p : Params) (raw : Raw) (sound : RawSpec p raw)
    (msg ctx sk rnd : Bytes) (out : Option Bytes) (returned : single raw msg ctx sk rnd = .ok out) :
    out=slhSign p msg ctx sk rnd := by
  by_cases bad : ctx.length>255
  · simpa [single,slhSign,bad,eq_comm] using returned
  cases run : rawSingle raw (withContext msg ctx) sk rnd with
  | error error => simp [single,bad,run,Except.map] at returned
  | ok sig =>
    have sigEq := raw_single p raw sound _ _ _ _ run
    simpa [single,slhSign,bad,run,sigEq,Except.map,eq_comm] using returned

def sameKey (outer : Outer) (ctx sk : Bytes) (items : List (Bytes × Bytes)) : Except Error (Option (List Bytes)) :=
  if ctx.length>255 then .ok none else outer (items.map fun (m,rnd) => ⟨m,ctx,sk,rnd⟩)

theorem same_key (p : Params) (outer : Outer) (sound : OuterSpec p outer)
    (ctx sk : Bytes) (items : List (Bytes × Bytes)) (out : Option (List Bytes))
    (returned : sameKey outer ctx sk items = .ok out) :
    out = (if ctx.length>255 then none else items.mapM (fun (m,rnd) => slhSign p m ctx sk rnd)) := by
  by_cases bad : ctx.length>255
  · simpa [sameKey,bad,eq_comm] using returned
  simp only [sameKey,bad,↓reduceIte] at returned ⊢
  simpa [List.mapM_map,Function.comp_def] using sound _ _ returned

/-- Single raw and hedged signing, deterministic signing with PK.seed, and
the common-context batch APIs. Paired items are the checked equal-length zip. -/
structure Correct (p : Params) (raw : Raw) (outer : Outer) : Prop where
  internal : ∀ m sk rnd out, rawSingle raw m sk rnd=.ok out → out=slhSignInternal p m sk rnd
  hedged : ∀ m ctx sk rnd out, single raw m ctx sk rnd=.ok out → out=slhSign p m ctx sk rnd
  deterministic : ∀ m ctx sk out, single raw m ctx sk (block p sk 2)=.ok out → out=slhSign p m ctx sk (block p sk 2)
  hedgedBatch : ∀ ctx sk items out, sameKey outer ctx sk items=.ok out →
    out=(if ctx.length>255 then none else items.mapM fun (m,rnd) => slhSign p m ctx sk rnd)
  deterministicBatch : ∀ ctx sk (msgs : List Bytes) out, sameKey outer ctx sk (msgs.map fun m => (m,block p sk 2))=.ok out →
    out=(if ctx.length>255 then none else msgs.mapM fun m => slhSign p m ctx sk (block p sk 2))

theorem wrappers (p : Params) (raw : Raw) (outer : Outer) (r : RawSpec p raw) (o : OuterSpec p outer) :
    Correct p raw outer := by
  refine ⟨raw_single p raw r, single_sign p raw r, fun m ctx sk => single_sign p raw r m ctx sk _,
    same_key p outer o,?_⟩
  intro ctx sk msgs out ok
  simpa [List.mapM_map,Function.comp_def] using same_key p outer o ctx sk _ out ok

end MetalPublicSignatures

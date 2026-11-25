import Metal.KeygenDispatch

namespace MetalCompletion
open Spec MetalPipeline MetalCommandValues

/-- The source check binds setup/begin errors and the post-wait status test.
The actual status delivered by the driver is an input to this model. -/
inductive Error | setup | missingCommand | device
  deriving DecidableEq
inductive Exit | setupFailure | missingCommand | submitted (completed : Bool)
  deriving DecidableEq

def bridgeCode (completed : Bool) : Int := if completed then 0 else -1

def afterWait {α : Type} (exit : Exit) (read : Unit → α) : Except Error α :=
  match exit with
  | .setupFailure => .error .setup
  | .missingCommand => .error .missingCommand
  | .submitted status => if bridgeCode status = 0 then .ok (read ()) else .error .device

theorem wait_success {α : Type} (exit : Exit) (read : Unit → α) (out : α) :
    afterWait exit read = .ok out ↔ exit = .submitted true ∧ out = read () := by
  cases exit with
  | submitted status => cases status <;> simp [afterWait,bridgeCode,eq_comm]
  | _ => simp [afterWait]

/-- Objective-C command creation checks the context, command buffer and
encoder. Retaining a nil wrapper also yields a null handle to Rust. -/
def observedExit (resources context command encoder wrapper completed : Bool) : Exit :=
  if resources && context && command && encoder && wrapper then .submitted completed else .setupFailure

theorem observed_success {α : Type} (resources context command encoder wrapper completed : Bool)
    (read : Unit → α) (out : α) :
    afterWait (observedExit resources context command encoder wrapper completed) read = .ok out ↔
      resources=true ∧ context=true ∧ command=true ∧ encoder=true ∧ wrapper=true ∧ completed=true ∧ out=read () := by
  rw [wait_success]
  unfold observedExit
  by_cases ready : (resources && context && command && encoder && wrapper)=true
  · simp only [ready,↓reduceIte,Exit.submitted.injEq]
    simp only [Bool.and_eq_true] at ready
    simp [ready.1.1.1.1,ready.1.1.1.2,ready.1.1.2,ready.1.2,ready.2]
  · simp only [ready,↓reduceIte,reduceCtorEq,false_and]
    simp only [Bool.and_eq_true] at ready
    tauto

/-- The named parameter sets pass geometry validation. The public wrapper
rejects oversized contexts before it enters the internal batch operation. -/
def sign (p : Params) (rs : List BatchSignReq) (exit : Exit) (pool : Unit → Bytes) : Except Error (Option (List Bytes)) :=
  if rs.any (fun r => decide (r.ctx.length>255)) then .ok none
  else if rs.isEmpty then .ok (some [])
  else afterWait exit (fun _ => some (resultSlices rs.length p.sigBytes (pool ())))

theorem sign_success (p : Params) (rs : List BatchSignReq) (exit : Exit) (pool : Unit → Bytes) (out : Option (List Bytes))
    (ok : sign p rs exit pool = .ok out) : out = publicResult p rs (pool ()) := by
  by_cases bad : rs.any (fun r => decide (r.ctx.length>255)) = true
  · simpa [sign,publicResult,bad,eq_comm] using ok
  cases rs with
  | nil => simpa [sign,publicResult,resultSlices,eq_comm] using ok
  | cons r rs =>
    simp only [sign,bad,Bool.false_eq_true,↓reduceIte,List.isEmpty_cons] at ok
    simpa [publicResult,bad] using ((wait_success _ _ _).mp ok).2

def keygen (batch : MetalKeygenDispatch.Batch) (exit : Exit) (read : Unit → List (Bytes × Bytes)) :
    Except Error (List (Bytes × Bytes)) :=
  if batch.isEmpty then .ok [] else afterWait exit read

theorem keygen_success (batch : MetalKeygenDispatch.Batch) (exit : Exit) (read : Unit → List (Bytes × Bytes))
    (empty : batch=[] → read ()=[]) (out : List (Bytes × Bytes)) (ok : keygen batch exit read = .ok out) :
    out=read () := by
  cases batch with
  | nil => simpa [keygen,empty rfl,eq_comm] using ok
  | cons s rs => exact ((wait_success _ _ _).mp ok).2

end MetalCompletion

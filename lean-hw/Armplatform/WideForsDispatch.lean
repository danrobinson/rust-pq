import Armplatform.WideForsSchedule
import Armplatform.ForsLoops

open Aeneas Aeneas.Std Result
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  PlatformProof.replay `WideForsFallback [
    (`slhdsa.fors.fors_pk_from_sig_loop2,`ArmForsReplay.slhdsa.fors.fors_pk_from_sig_loop2),
    (`slhdsa.fors_pk_from_sig_loop2_spec,`ArmForsReplay.slhdsa.fors_pk_from_sig_loop2_spec)]
    #[`slhdsa.fors_pk_from_sig_spec]

namespace slhdsa.WideFors
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def native {N : Usize} (paired multi : Bool) (p : params.Params) (sig md : Slice U8)
    (seed : hash.Seed N) (a : address.Adrs) : Result (Array U8 N) :=
  let P := paramsS p
  let out := evaluated P paired multi (bytes sig.val) (bytes md.val) (bytes seed.pk_seed.val) (adrsS a)
    (plan P paired multi)
  let data := out.map (fun b => (⟨b⟩ : U8))
  if h : data.length=N.val then ok (Array.from data h) else .fail .panic

theorem native_spec {N : Usize} (paired multi : Bool) (p : params.Params) (hp : PN p N)
    (sig md : Slice U8) (seed : hash.Seed N) (a : address.Adrs)
    (len : sig.length=p.k.val*(1+p.a.val)*N.val) :
    native paired multi p sig md seed a ⦃ r => bytes r.val =
      Spec.forsPkFromSig (paramsS p) (bytes sig.val) (bytes md.val) (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  unfold native
  have sl : (bytes sig.val).length=(paramsS p).k*(1+(paramsS p).a)*(paramsS p).n := by rw [hp.n]; simpa using len
  have pl : (bytes seed.pk_seed.val).length=(paramsS p).n := by rw [hp.n]; simp
  simp only [source_plan_fips (paramsS p) hp.valid paired multi _ _ _ sl pl]
  have outLen : (Spec.forsPkFromSig (paramsS p) (bytes sig.val) (bytes md.val) (bytes seed.pk_seed.val) (adrsS a)).length=N.val := by
    unfold Spec.forsPkFromSig
    rw [Spec.T_length _ hp.valid, hp.n]
  simp only [List.length_map,outLen, _root_.dite_true,step_simps,Array.from_val]
  simp [bytes]

noncomputable def dispatch {N : Usize} (available : Result Bool) (paired multi : Bool) (p : params.Params) (sig md : Slice U8)
    (seed : hash.Seed N) (a : address.Adrs) : Result (Array U8 N) := do
  let allowed ← match N.val with
    | 16 => ok true
    | 24 => ok true
    | 32 => ok true
    | _ => ok false
  if allowed then
    let yes ← available
    if yes then native paired multi p sig md seed a else
      WideForsFallback.slhdsa.fors.fors_pk_from_sig p sig md seed a
  else WideForsFallback.slhdsa.fors.fors_pk_from_sig p sig md seed a

theorem dispatch_fips {N : Usize} (available paired multi : Bool) (p : params.Params) (hp : PN p N)
    (sig md : Slice U8) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (len : sig.length=p.k.val*(1+p.a.val)*N.val) (mdlen : md.length=(p.k.val*p.a.val+7)/8) :
    dispatch (ok available) paired multi p sig md seed a ⦃ r => bytes r.val =
      Spec.forsPkFromSig (paramsS p) (bytes sig.val) (bytes md.val) (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  have portable := WideForsFallback.slhdsa.fors_pk_from_sig_spec p hp sig md seed hs a len mdlen
  have active := native_spec paired multi p hp sig md seed a len
  rcases hp.nok with w|w|w <;> cases available <;> simp only [dispatch,w,bind_ok,ite_true,Bool.false_eq_true,ite_false] <;> first | exact active | exact portable

end slhdsa.WideFors

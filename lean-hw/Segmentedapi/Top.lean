import Segmentedapi.Guard
import Segmentedapi.Randomizer
open Aeneas Aeneas.Std Result
namespace slhdsa.SegmentedApi

theorem sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (rnd : Array U8 N) (hsk : sk.length=4*N.val) (hm : Room m.length (msgSlack N.val+257)) :
    Program.slh.slh_sign p m ctx sk rnd ⦃ out => out.map (fun v => bytes v.val) =
      Spec.slhSign (paramsS p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes rnd.val) ⦄ := by
  rw [sign_eq_from_prf p hp m ctx sk rnd hm (fun key hc => randomizer_spec p hp key rnd ctx m hc hm)]
  exact slh_sign_spec p hp m ctx sk rnd hsk hm

#print axioms sign_spec
#print axioms verify_spec
end slhdsa.SegmentedApi

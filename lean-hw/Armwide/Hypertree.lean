import Armwide.HypertreeReplay
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Hypertree

theorem wots_pk_from_sig_spec [Public.Dispatcher.Cpu] [Keygen.Features] {N : Usize}
    (p : params.Params) (hp : PN p N) (sig : Slice U8) (m : Array U8 N) (seed : hash.Seed N)
    (hs : SeedOk seed) (a : address.Adrs) (fits : N.val*(2*N.val+3)≤sig.length) :
    Recovery.Dispatcher.wots.wots_pk_from_sig sig m seed a ⦃ r => slhdsa.bytes r.val =
      Spec.wotsPkFromSig (paramsS p) (slhdsa.bytes sig.val) (slhdsa.bytes m.val)
        (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) ⦄ := by
  rw [Recovery.Dispatcher.dispatch_eq_scalar p hp sig m seed hs a fits]
  exact slhdsa.wots_pk_from_sig_spec p hp sig m seed hs a fits

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM buildHypertree

#print axioms xmss_pk_from_sig_spec
#print axioms ht_sign_spec
#print axioms ht_verify_spec

end slhdsa.Armwide.Hypertree

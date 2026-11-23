import Shakebatch.AppleFors
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.Apple
noncomputable section

abbrev wots_pk_gen := @ShakeForestApple.slhdsa.ShakeBatch.shake.wots.wots_pk_gen Kadisp.machine ShakeForestApple.slhdsa.ShakeBatch.scalarStream available
abbrev wots_sign := @ShakeForestApple.slhdsa.ShakeBatch.shake.wots.wots_sign Kadisp.machine available
abbrev wots_pk_from_sig := @ShakeForestApple.slhdsa.ShakeBatch.shake.wots.wots_pk_from_sig Kadisp.machine ShakeForestApple.slhdsa.ShakeBatch.scalarStream available

theorem wots_pk_gen_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) :
    wots_pk_gen sk seed a ⦃ out => bytes out.val=Spec.wotsPkGen (Shake.params p)
      (bytes sk.val) (bytes seed.val) (adrsS a) ⦄ :=
  @ShakeForestApple.slhdsa.ShakeBatch.wots_pk_gen_spec Kadisp.machine
    ShakeForestApple.slhdsa.ShakeBatch.scalarStream ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp sk seed a true
    (available_for_fips _ p hp) (fun _ => Kadisp.permutation_correct) (by decide) (by decide)

theorem wots_sign_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk seed : Array U8 N) (a : address.Adrs) :
    wots_sign m sk seed a ⦃ out => bytes out.val=Spec.wotsSign (Shake.params p) (bytes m.val)
      (bytes sk.val) (bytes seed.val) (adrsS a) ∧ out.length=N.val*(2*N.val+3) ⦄ :=
  @ShakeForestApple.slhdsa.ShakeBatch.wots_sign_spec Kadisp.machine
    ShakeForestApple.slhdsa.ShakeBatch.scalarStream ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp m sk seed a true
    (available_for_fips _ p hp) (fun _ => Kadisp.permutation_correct) (by decide)

theorem wots_pk_from_sig_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (m seed : Array U8 N) (a : address.Adrs) (size : N.val*(2*N.val+3) ≤ sig.length) :
    wots_pk_from_sig sig m seed a ⦃ out => bytes out.val=Spec.wotsPkFromSig (Shake.params p)
      (bytes sig.val) (bytes m.val) (bytes seed.val) (adrsS a) ⦄ :=
  @ShakeForestApple.slhdsa.ShakeBatch.wots_pk_from_sig_spec Kadisp.machine
    ShakeForestApple.slhdsa.ShakeBatch.scalarStream ShakeForestApple.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp sig m seed a size true
    (available_for_fips _ p hp) (fun _ => Kadisp.permutation_correct) (by decide)

end
end slhdsa.ShakeBatch.Apple

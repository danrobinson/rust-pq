import Shakebatch.LinuxFors
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.Linux
noncomputable section

abbrev wots_pk_gen := @ShakeForestLinux.slhdsa.ShakeBatch.shake.wots.wots_pk_gen Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream available
abbrev wots_sign := @ShakeForestLinux.slhdsa.ShakeBatch.shake.wots.wots_sign Kldisp.machine available
abbrev wots_pk_from_sig := @ShakeForestLinux.slhdsa.ShakeBatch.shake.wots.wots_pk_from_sig Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream available

theorem wots_pk_gen_spec (one : Kldisp.RoundCorrect) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) :
    wots_pk_gen sk seed a ⦃ out => bytes out.val=Spec.wotsPkGen (Shake.params p)
      (bytes sk.val) (bytes seed.val) (adrsS a) ⦄ :=
  @ShakeForestLinux.slhdsa.ShakeBatch.wots_pk_gen_spec Kldisp.machine
    ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp sk seed a true
    (available_for_fips _ p hp) (fun _ => Kldisp.permutation_of_round one) (by decide) (by decide)

theorem wots_sign_spec (one : Kldisp.RoundCorrect) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk seed : Array U8 N) (a : address.Adrs) :
    wots_sign m sk seed a ⦃ out => bytes out.val=Spec.wotsSign (Shake.params p) (bytes m.val)
      (bytes sk.val) (bytes seed.val) (adrsS a) ∧ out.length=N.val*(2*N.val+3) ⦄ :=
  @ShakeForestLinux.slhdsa.ShakeBatch.wots_sign_spec Kldisp.machine
    ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp m sk seed a true
    (available_for_fips _ p hp) (fun _ => Kldisp.permutation_of_round one) (by decide)

theorem wots_pk_from_sig_spec (one : Kldisp.RoundCorrect) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (m seed : Array U8 N) (a : address.Adrs) (size : N.val*(2*N.val+3) ≤ sig.length) :
    wots_pk_from_sig sig m seed a ⦃ out => bytes out.val=Spec.wotsPkFromSig (Shake.params p)
      (bytes sig.val) (bytes m.val) (bytes seed.val) (adrsS a) ⦄ :=
  @ShakeForestLinux.slhdsa.ShakeBatch.wots_pk_from_sig_spec Kldisp.machine
    ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp sig m seed a size true
    (available_for_fips _ p hp) (fun _ => Kldisp.permutation_of_round one) (by decide)

end
end slhdsa.ShakeBatch.Linux

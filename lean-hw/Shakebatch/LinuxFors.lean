import Shakebatch.LinuxStream
import Shakebatch.Available
import Shakebatch.LinuxDispatch
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.Linux
noncomputable section

abbrev available := ShakeBatch.shake.batch.available KldispRust.shake256.parallel.available
abbrev sign := @ShakeForestLinux.slhdsa.ShakeBatch.shake.fors.fors_sign Kldisp.machine available
abbrev recover := @ShakeForestLinux.slhdsa.ShakeBatch.shake.fors.fors_pk_from_sig Kldisp.machine
  ShakeForestLinux.slhdsa.ShakeBatch.scalarStream available

theorem fors_sign_spec (one : Kldisp.RoundCorrect) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) (len : md.length=(p.k.val*p.a.val+7)/8) :
    sign p md sk seed a ⦃ out => bytes out.val=Spec.forsSign (Shake.params p) (bytes md.val)
      (bytes sk.val) (bytes seed.val) (adrsS a) ∧ out.length=p.k.val*(1+p.a.val)*N.val ⦄ :=
  @ShakeForestLinux.slhdsa.ShakeBatch.sign_dispatched Kldisp.machine
    ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp md sk seed a len true (available_for_fips _ p hp) (fun _ => Kldisp.permutation_of_round one) (by decide)

theorem fors_pk_from_sig_spec (one : Kldisp.RoundCorrect) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sig md : Slice U8)
    (seed : Array U8 N) (a : address.Adrs) (len : sig.length=p.k.val*(1+p.a.val)*N.val)
    (capacity : md.length=(p.k.val*p.a.val+7)/8) :
    recover p sig md seed a ⦃ out => bytes out.val=Spec.forsPkFromSig (Shake.params p)
      (bytes sig.val) (bytes md.val) (bytes seed.val) (adrsS a) ⦄ :=
  @ShakeForestLinux.slhdsa.ShakeBatch.recover_dispatched Kldisp.machine
    ShakeForestLinux.slhdsa.ShakeBatch.scalarStream ShakeForestLinux.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp sig md seed a len capacity true (available_for_fips _ p hp)
    (fun _ => Kldisp.permutation_of_round one) (by decide)

end
end slhdsa.ShakeBatch.Linux

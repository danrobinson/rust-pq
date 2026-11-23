import Shakebatch.X86Stream
import Shakebatch.X86Feature
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.X86
noncomputable section

abbrev sign := @ShakeForestX86.slhdsa.ShakeBatch.shake.fors.fors_sign Kxdispatch.machine available
abbrev recover := @ShakeForestX86.slhdsa.ShakeBatch.shake.fors.fors_pk_from_sig Kxdispatch.machine
  ShakeForestX86.slhdsa.ShakeBatch.scalarStream available

theorem fors_sign_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) (len : md.length=(p.k.val*p.a.val+7)/8) :
    sign p md sk seed a ⦃ out => bytes out.val=Spec.forsSign (Shake.params p) (bytes md.val)
      (bytes sk.val) (bytes seed.val) (adrsS a) ∧ out.length=p.k.val*(1+p.a.val)*N.val ⦄ :=
  @ShakeForestX86.slhdsa.ShakeBatch.sign_dispatched Kxdispatch.machine
    ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp md sk seed a len GatherRust.avx512Available (available_spec p hp) permutation (fun _ => by decide)

theorem fors_pk_from_sig_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sig md : Slice U8)
    (seed : Array U8 N) (a : address.Adrs) (len : sig.length=p.k.val*(1+p.a.val)*N.val)
    (capacity : md.length=(p.k.val*p.a.val+7)/8) :
    recover p sig md seed a ⦃ out => bytes out.val=Spec.forsPkFromSig (Shake.params p)
      (bytes sig.val) (bytes md.val) (bytes seed.val) (adrsS a) ⦄ :=
  @ShakeForestX86.slhdsa.ShakeBatch.recover_dispatched Kxdispatch.machine
    ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp sig md seed a len capacity GatherRust.avx512Available (available_spec p hp)
    permutation (fun _ => by decide)

end
end slhdsa.ShakeBatch.X86

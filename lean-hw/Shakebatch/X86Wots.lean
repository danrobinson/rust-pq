import Shakebatch.X86Fors
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch.X86
noncomputable section

abbrev wots_pk_gen := @ShakeForestX86.slhdsa.ShakeBatch.shake.wots.wots_pk_gen Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream available
abbrev wots_sign := @ShakeForestX86.slhdsa.ShakeBatch.shake.wots.wots_sign Kxdispatch.machine available
abbrev wots_pk_from_sig := @ShakeForestX86.slhdsa.ShakeBatch.shake.wots.wots_pk_from_sig Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream available

theorem wots_pk_gen_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) :
    wots_pk_gen sk seed a ⦃ out => bytes out.val=Spec.wotsPkGen (Shake.params p)
      (bytes sk.val) (bytes seed.val) (adrsS a) ⦄ :=
  @ShakeForestX86.slhdsa.ShakeBatch.wots_pk_gen_spec Kxdispatch.machine
    ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp sk seed a GatherRust.avx512Available
    (available_spec p hp) permutation (fun _ => by decide) (fun _ => by decide)

theorem wots_sign_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk seed : Array U8 N) (a : address.Adrs) :
    wots_sign m sk seed a ⦃ out => bytes out.val=Spec.wotsSign (Shake.params p) (bytes m.val)
      (bytes sk.val) (bytes seed.val) (adrsS a) ∧ out.length=N.val*(2*N.val+3) ⦄ :=
  @ShakeForestX86.slhdsa.ShakeBatch.wots_sign_spec Kxdispatch.machine
    ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp m sk seed a GatherRust.avx512Available
    (available_spec p hp) permutation (fun _ => by decide)

theorem wots_pk_from_sig_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (m seed : Array U8 N) (a : address.Adrs) (size : N.val*(2*N.val+3) ≤ sig.length) :
    wots_pk_from_sig sig m seed a ⦃ out => bytes out.val=Spec.wotsPkFromSig (Shake.params p)
      (bytes sig.val) (bytes m.val) (bytes seed.val) (adrsS a) ⦄ :=
  @ShakeForestX86.slhdsa.ShakeBatch.wots_pk_from_sig_spec Kxdispatch.machine
    ShakeForestX86.slhdsa.ShakeBatch.scalarStream ShakeForestX86.slhdsa.ShakeBatch.scalarStreamCorrect
    available N p hp sig m seed a size GatherRust.avx512Available
    (available_spec p hp) permutation (fun _ => by decide)

end
end slhdsa.ShakeBatch.X86

import Wotsapi.Funs
import Wotswide.Recovery
import Slhdsa.Proofs.Wots
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots.Api
open Wide
set_option maxRecDepth 8192

private theorem withDigits {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (m : Array U8 N) (s : WotsApiRust.hash.Seed N) (a : WotsApiRust.address.Adrs)
    (seedOK : SeedOk (coreSeed (WotsApiRust.wideSeed s))) (cpu : GatherRust.avx512Available=true)
    (room : N.val*(2*N.val+3) ≤ sig.length) (digits : alloc.vec.Vec U32)
    (matchesMsg : nats digits.val = Spec.wotsDigits (paramsS p) (bytes m.val))
    (count : digits.length = 2*N.val+3) (valid : ∀ d ∈ digits.val, d.val < 16) :
    WotsApiRust.wots.wide.recover s a sig (alloc.vec.Vec.deref digits) ⦃ r =>
      bytes r.val = Spec.wotsPkFromSig (paramsS p) (bytes sig.val) (bytes m.val) (bytes s.pk_seed.val)
        (adrsS (coreAddress (WotsApiRust.wideAddress a))) ⦄ := by
  have len : (alloc.vec.Vec.deref digits).length = 2*N.val+3 := by simpa [Slice.length,vec_deref_val,alloc.vec.Vec.length] using count
  unfold WotsApiRust.wots.wide.recover
  step with Wide.recover_fips (paramsS p) _ _ sig (alloc.vec.Vec.deref digits) hp.n.symm hp.nok seedOK cpu len
    (fun i hi => by have h := digit_le digits _ count valid i (len ▸ hi); omega)
    (by simpa only [len] using room) as ⟨out,eq⟩
  rw [eq,Spec.wotsPkFromSig,hp.len,len,← matchesMsg]
  apply congrArg (Spec.T (paramsS p) (bytes s.pk_seed.val) (Spec.wotsPkAdrs (adrsS (coreAddress (WotsApiRust.wideAddress a)))))
  apply List.flatMap_congr
  intro i hi
  have bound : i < digits.val.length := by have := List.mem_range.mp hi; change digits.val.length=_ at count; omega
  simp [chainAt,element,Spec.block,bytes,List.map_drop,List.map_take,nats_getElem! _ _ bound,vec_deref_val,w_eq,Nat.mul_comm]
  rw [show p.n.val = N.val from hp.n]
  rfl

theorem avx512_fips {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8)
    (m : Array U8 N) (s : WotsApiRust.hash.Seed N) (a : WotsApiRust.address.Adrs)
    (seedOK : SeedOk (coreSeed (WotsApiRust.wideSeed s))) (cpu : GatherRust.avx512Available=true)
    (room : N.val*(2*N.val+3) ≤ sig.length) :
    WotsApiRust.wots.wots_pk_from_sig sig m s a ⦃ r =>
      bytes r.val = Spec.wotsPkFromSig (paramsS p) (bytes sig.val) (bytes m.val) (bytes s.pk_seed.val)
        (adrsS (coreAddress (WotsApiRust.wideAddress a))) ⦄ := by
  unfold WotsApiRust.wots.wots_pk_from_sig
  have hn := hp.le32
  rw [show WotsApiRust.params.LEN2 = 3#usize by unfold WotsApiRust.params.LEN2; rfl]
  step as ⟨twice,ht⟩
  step as ⟨len,hl⟩
  rw [show WotsApiRust.wots.wots_digits (N := N) = wots.wots_digits by with_unfolding_all rfl]
  step with wots_digits_spec p hp m as ⟨digits,eq,count,valid⟩
  have proof := withDigits p hp sig m s a seedOK cpu room digits eq count valid
  rcases hp.nok with w|w|w <;> simpa only [w,bind_ok,WotsApiRust.sha256.x86.avx512_available,
    WotsX86Rust.sha256.x86.avx512_available,WotsX86Rust.sha256.x86.has_avx512.get,
    GatherRust.sha256.x86.avx512_available,cpu,ite_true] using proof

end slhdsa.X86.Wots.Api

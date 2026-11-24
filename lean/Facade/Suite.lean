import Slhdsa.Proofs.ShakeAdapter
import Slhdsa.Proofs.Sets
open Aeneas Aeneas.Std Result
namespace slhdsa.Suite

def view (family : Spec.HashFamily) (p : slhdsa.params.Params) : Spec.Params :=
  { paramsS p with family := family }

@[simp] theorem view_sha2 (p : slhdsa.params.Params) : view .sha2 p = paramsS p := rfl

theorem sigBytes_view (family : Spec.HashFamily) (p : slhdsa.params.Params) : (view family p).sigBytes = (paramsS p).sigBytes := rfl

theorem valid {p : slhdsa.params.Params} {N : Usize} (family : Spec.HashFamily) (hp : PN p N) :
    (view family p).Valid := by
  obtain ⟨h, _⟩ := hp
  rcases h with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m⟩
  exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m⟩

abbrev verify (family : Spec.HashFamily) :=
  match family with
  | .sha2 => api.verify
  | .shake => shake.api.verify

theorem api_verify_spec (family : Spec.HashFamily) {N : Usize} (p : params.Params) (hp : PN p N) (m sig ctx pk : Slice U8)
    (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    verify family N p m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (view family p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  cases family with
  | sha2 => exact slhdsa.api_verify_spec p hp m sig ctx pk hpk hm
  | shake => exact Shake.api_verify_spec p hp m sig ctx pk hpk hm

abbrev sign_into (family : Spec.HashFamily) :=
  match family with
  | .sha2 => adapter.sign_into
  | .shake => shake.adapter.sign_into

theorem adapter_sign_into_spec (family : Spec.HashFamily) {N : Usize} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (has : Bool) (addrnd : Slice U8) (sig : Slice U8)
    (hsk : sk.length = 4 * N.val) (hsig : sig.length = (paramsS p).sigBytes)
    (hr : has = true → addrnd.length = N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    sign_into family N p m ctx sk has addrnd sig ⦃ r =>
      (r.1 = true ↔ ctx.length ≤ 255) ∧
      (r.1 = true → Spec.slhSign (view family p) (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (randS (paramsS p) (bytes sk.val) has addrnd) = some (bytes r.2.val)) ∧
      (r.1 = false → r.2 = sig) ⦄ := by
  cases family with
  | sha2 => exact slhdsa.adapter_sign_into_spec p hp m ctx sk has addrnd sig hsk hsig hr hm
  | shake => exact Shake.adapter_sign_into_spec p hp m ctx sk has addrnd sig hsk hsig hr hm

abbrev keygen_seeds (family : Spec.HashFamily) :=
  match family with
  | .sha2 => adapter.keygen_seeds
  | .shake => shake.adapter.keygen_seeds

theorem adapter_keygen_seeds_spec (family : Spec.HashFamily) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk_seed sk_prf pk_seed sk pk : Slice U8)
    (h1 : sk_seed.length = N.val) (h2 : sk_prf.length = N.val) (h3 : pk_seed.length = N.val)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    keygen_seeds family N p sk_seed sk_prf pk_seed sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal (view family p) (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val) ⦄ := by
  cases family with
  | sha2 => exact slhdsa.adapter_keygen_seeds_spec p hp sk_seed sk_prf pk_seed sk pk h1 h2 h3 hsk hpk
  | shake => exact Shake.adapter_keygen_seeds_spec p hp sk_seed sk_prf pk_seed sk pk h1 h2 h3 hsk hpk

end slhdsa.Suite

namespace slhdsa.shake_128s
theorem shape : paramsS sets.shake_128s.params.PARAMS = Spec.sha2_128s := by
  rw [sets.shake_128s.params.PARAMS, ← sha2_128s.PARAMS_eq]; exact sha2_128s.hP
theorem hP : Suite.view .shake sets.shake_128s.params.PARAMS = Spec.shake_128s := by
  unfold Suite.view; rw [shape]; rfl
theorem pn : PN sets.shake_128s.params.PARAMS 16#usize := by
  rw [sets.shake_128s.params.PARAMS, ← sha2_128s.PARAMS_eq]; exact sha2_128s.pn
abbrev slack := @sha2_128s.slack
theorem block_shape : Spec.block Spec.shake_128s = Spec.block Spec.sha2_128s := rfl
end slhdsa.shake_128s

namespace slhdsa.shake_128f
theorem shape : paramsS sets.shake_128f.params.PARAMS = Spec.sha2_128f := by
  rw [sets.shake_128f.params.PARAMS, ← sha2_128f.PARAMS_eq]; exact sha2_128f.hP
theorem hP : Suite.view .shake sets.shake_128f.params.PARAMS = Spec.shake_128f := by
  unfold Suite.view; rw [shape]; rfl
theorem pn : PN sets.shake_128f.params.PARAMS 16#usize := by
  rw [sets.shake_128f.params.PARAMS, ← sha2_128f.PARAMS_eq]; exact sha2_128f.pn
abbrev slack := @sha2_128f.slack
theorem block_shape : Spec.block Spec.shake_128f = Spec.block Spec.sha2_128f := rfl
end slhdsa.shake_128f

namespace slhdsa.shake_192s
theorem shape : paramsS sets.shake_192s.params.PARAMS = Spec.sha2_192s := by
  rw [sets.shake_192s.params.PARAMS, ← sha2_192s.PARAMS_eq]; exact sha2_192s.hP
theorem hP : Suite.view .shake sets.shake_192s.params.PARAMS = Spec.shake_192s := by
  unfold Suite.view; rw [shape]; rfl
theorem pn : PN sets.shake_192s.params.PARAMS 24#usize := by
  rw [sets.shake_192s.params.PARAMS, ← sha2_192s.PARAMS_eq]; exact sha2_192s.pn
abbrev slack := @sha2_192s.slack
theorem block_shape : Spec.block Spec.shake_192s = Spec.block Spec.sha2_192s := rfl
end slhdsa.shake_192s

namespace slhdsa.shake_192f
theorem shape : paramsS sets.shake_192f.params.PARAMS = Spec.sha2_192f := by
  rw [sets.shake_192f.params.PARAMS, ← sha2_192f.PARAMS_eq]; exact sha2_192f.hP
theorem hP : Suite.view .shake sets.shake_192f.params.PARAMS = Spec.shake_192f := by
  unfold Suite.view; rw [shape]; rfl
theorem pn : PN sets.shake_192f.params.PARAMS 24#usize := by
  rw [sets.shake_192f.params.PARAMS, ← sha2_192f.PARAMS_eq]; exact sha2_192f.pn
abbrev slack := @sha2_192f.slack
theorem block_shape : Spec.block Spec.shake_192f = Spec.block Spec.sha2_192f := rfl
end slhdsa.shake_192f

namespace slhdsa.shake_256s
theorem shape : paramsS sets.shake_256s.params.PARAMS = Spec.sha2_256s := by
  rw [sets.shake_256s.params.PARAMS, ← sha2_256s.PARAMS_eq]; exact sha2_256s.hP
theorem hP : Suite.view .shake sets.shake_256s.params.PARAMS = Spec.shake_256s := by
  unfold Suite.view; rw [shape]; rfl
theorem pn : PN sets.shake_256s.params.PARAMS 32#usize := by
  rw [sets.shake_256s.params.PARAMS, ← sha2_256s.PARAMS_eq]; exact sha2_256s.pn
abbrev slack := @sha2_256s.slack
theorem block_shape : Spec.block Spec.shake_256s = Spec.block Spec.sha2_256s := rfl
end slhdsa.shake_256s

namespace slhdsa.shake_256f
theorem shape : paramsS sets.shake_256f.params.PARAMS = Spec.sha2_256f := by
  rw [sets.shake_256f.params.PARAMS, ← sha2_256f.PARAMS_eq]; exact sha2_256f.hP
theorem hP : Suite.view .shake sets.shake_256f.params.PARAMS = Spec.shake_256f := by
  unfold Suite.view; rw [shape]; rfl
theorem pn : PN sets.shake_256f.params.PARAMS 32#usize := by
  rw [sets.shake_256f.params.PARAMS, ← sha2_256f.PARAMS_eq]; exact sha2_256f.pn
abbrev slack := @sha2_256f.slack
theorem block_shape : Spec.block Spec.shake_256f = Spec.block Spec.sha2_256f := rfl
end slhdsa.shake_256f

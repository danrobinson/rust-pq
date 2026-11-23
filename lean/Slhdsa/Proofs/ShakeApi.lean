import Slhdsa.Proofs.ShakeSlh
open Aeneas Aeneas.Std Result

/-! The crate's interface, module `api`, for any valid parameter set. -/

namespace slhdsa.Shake

@[step]
theorem api_keygen_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (seeds sk pk : Slice U8)
    (hseeds : seeds.length = 3 * N.val) (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    shake.api.keygen N p seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) =
        Spec.slhKeygenInternal (params p) (Spec.block (paramsS p) (bytes seeds.val) 0)
          (Spec.block (paramsS p) (bytes seeds.val) 1) (Spec.block (paramsS p) (bytes seeds.val) 2) ∧
      r.1.length = 4 * N.val ∧ r.2.length = 2 * N.val ⦄ := by
  unfold shake.api.keygen
  let* ⟨ sk_seed, sk_seed_post ⟩ ← block_spec
  let* ⟨ sk_prf, sk_prf_post ⟩ ← block_spec
  let* ⟨ pk_seed, pk_seed_post ⟩ ← block_spec
  apply WP.spec_mono (slh_keygen_internal_spec p hp sk_seed sk_prf pk_seed sk pk hsk hpk)
  rintro r ⟨h1, h2, h3⟩
  refine ⟨?_, h2, h3⟩
  rw [h1, bytes_block_N p hp seeds sk_seed 0 sk_seed_post, bytes_block_N p hp seeds sk_prf 1 sk_prf_post,
    bytes_block_N p hp seeds pk_seed 2 pk_seed_post]

@[step]
theorem api_public_key_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk pk : Slice U8)
    (hsk : sk.length = 4 * N.val) (hpk : pk.length = 2 * N.val) :
    shake.api.public_key N sk pk ⦃ r => bytes r.val = Spec.skPk (paramsS p) (bytes sk.val) ∧
      r.length = 2 * N.val ⦄ := by
  have hN := hp.le32
  unfold shake.api.public_key
  step*
  all_goals try (rw [s_post1, i1_post, i_post]; scalar_tac)
  refine ⟨?_, by rw [r_post, s_post1, i1_post, i_post]; omega⟩
  rw [r_post, s_post]
  simp only [List.slice, Spec.skPk, hp.n, bytes_take, bytes_drop, i_post, i1_post]
  rw [List.take_of_length_le (by simp only [List.length_drop, bytes_length]; simp only [Slice.length] at hsk; omega)]

/-- `shake.api.sign` is the plain signer `slh_sign`. -/
@[step]
theorem api_sign_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (addrnd : Array U8 N) (hsk : sk.length = 4 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    shake.api.sign p m ctx sk addrnd ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign (params p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) ⦄ := by
  unfold shake.api.sign
  exact slh_sign_spec p hp m ctx sk addrnd hsk hm

@[step]
theorem api_sign_deterministic_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m ctx sk : Slice U8)
    (hsk : sk.length = 4 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    shake.api.sign_deterministic N p m ctx sk ⦃ r =>
      r.map (fun v => bytes v.val) =
        Spec.slhSign (params p) (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (Spec.block (paramsS p) (bytes sk.val) 2) ⦄ := by
  unfold shake.api.sign_deterministic
  let* ⟨ pk_seed, pk_seed_post ⟩ ← block_spec
  apply WP.spec_mono (slh_sign_spec p hp m ctx sk pk_seed hsk hm)
  intro r hr
  rw [hr, bytes_block_N p hp sk pk_seed 2 pk_seed_post]

@[step]
theorem api_verify_spec {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (m sig ctx pk : Slice U8)
    (hpk : pk.length = 2 * N.val) (hm : Room m.length (msgSlack N.val + 257)) :
    shake.api.verify N p m sig ctx pk ⦃ b =>
      b = Spec.slhVerify (params p) (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) ⦄ := by
  unfold shake.api.verify
  exact slh_verify_spec p hp m sig ctx pk hpk hm

end slhdsa.Shake

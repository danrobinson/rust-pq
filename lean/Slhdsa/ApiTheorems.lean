import Slhdsa.Theorems
import Slhdsa.Proofs.Api
import Spec.Correctness
open Aeneas Aeneas.Std Result

/-!
# Results about the checked signer and the crate's interface

The checked signer (`slh_sign_internal_checked`, `slh_sign_checked`, and
`api.sign_checked` / `api.sign_deterministic_checked` on top of them)
recomputes every value that a one-time key signs and releases a signature
only when the two computations agree. Proved here, for the Rust functions as
translated by Aeneas:

* (A) it never fails, and every signature it releases is the signature of
  FIPS 205 (the right-hand sides of `sign_internal_correct` and `sign_correct`);
* (B) every signature it releases verifies under the public key held in the
  private key, for every private key;
* (C) for a well-formed private key (`Spec.KeyOk`: the last block is the root
  that key generation derives from the first and third; in particular every
  key that key generation produced) it always releases a signature;
* (D) completeness: with a key from key generation, the signatures of the
  plain and the checked signers verify;
* (E) the rest of `api`: `keygen`, `public_key`, `verify`, and the plain
  `sign` and `sign_deterministic`.

`Spec.skPk sk` is `sk.drop 32`, the public key `PK.seed ‖ PK.root` held in a
private key. The hypotheses `Room` are those of `Theorems.lean`.
-/

namespace slhdsa

theorem ok_inj {α} {m : Result α} {r v : α} (h1 : m = ok r) (h2 : m = ok v) : r = v := by
  rw [h1] at h2; simpa using h2

theorem bytes_length16 (x : Array U8 16#usize) : (bytes x.val).length = Spec.n := by simp [Spec.n]

/-! ## (A) Exactness -/

/-- The checked signer returns, and what it returns is either nothing or the
signature of FIPS 205 Algorithm 19. -/
theorem sign_internal_checked_correct (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) :
    ∃ r, slh.slh_sign_internal_checked m sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        bytes sig.val = Spec.slhSignInternal (bytes m.val) (bytes sk.val) (bytes addrnd.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (slh_sign_internal_checked_spec m sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignInternalChecked_sound _ _ _ _ hr.symm).1

/-- The checked signer with a context string: nothing, or the signature of
FIPS 205 Algorithm 22. -/
theorem sign_checked_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, slh.slh_sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (slh_sign_checked_spec m ctx sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound _ _ _ _ _ hr.symm).1

theorem api_sign_checked_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, api.sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) :=
  sign_checked_correct m ctx sk addrnd hm

/-- The deterministic checked signer: nothing, or the signature of FIPS 205
Algorithm 22 with `PK.seed` as the randomness (the deterministic variant). -/
theorem api_sign_deterministic_checked_correct (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) :
    ∃ r, api.sign_deterministic_checked m ctx sk = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block (bytes sk.val) 2) =
          some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (api_sign_deterministic_checked_spec m ctx sk hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound _ _ _ _ _ hr.symm).1

/-! ## (B) Released signatures verify, for every private key -/

/-- At the level of the specification. -/
theorem spec_sign_internal_checked_verifies (msg sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignInternalChecked msg sk addrnd = some sig) :
    Spec.slhVerifyInternal msg sig (Spec.skPk sk) = true :=
  (Spec.slhSignInternalChecked_sound msg sk addrnd sig h).2

theorem spec_sign_checked_verifies (msg ctx sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignChecked msg ctx sk addrnd = some sig) :
    Spec.slhVerify msg sig ctx (Spec.skPk sk) = true :=
  (Spec.slhSignChecked_sound msg ctx sk addrnd sig h).2

theorem sign_internal_checked_verifies (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 152) (hpk : bytes pk.val = Spec.skPk (bytes sk.val))
    (h : slh.slh_sign_internal_checked m sk addrnd = ok (some sig)) :
    slh.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (slh_sign_internal_checked_spec m sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hpk,
    spec_sign_internal_checked_verifies _ _ _ _ hp.symm]

theorem sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 409) (hpk : bytes pk.val = Spec.skPk (bytes sk.val))
    (h : slh.slh_sign_checked m ctx sk addrnd = ok (some sig)) :
    slh.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (slh_sign_checked_spec m ctx sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_correct _ _ _ _ hm, vec_deref_val, hpk, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

theorem api_public_key_correct (sk : Array U8 64#usize) :
    ∃ pk, api.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk (bytes sk.val) :=
  spec_imp_exists (api_public_key_spec sk)

/-- A signature released by `api.sign_checked` verifies under
`api.public_key sk`, for every `sk`. -/
theorem api_sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 409)
    (h : api.sign_checked m ctx sk addrnd = ok (some sig)) (hpk : api.public_key sk = ok pk) :
    api.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  exact sign_checked_verifies m ctx sk addrnd pk sig hm h2 h

theorem api_sign_deterministic_checked_verifies (m ctx : Slice U8) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 409)
    (h : api.sign_deterministic_checked m ctx sk = ok (some sig)) (hpk : api.public_key sk = ok pk) :
    api.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (api_sign_deterministic_checked_spec m ctx sk hm)
  obtain rfl := ok_inj h hr
  rw [api.verify, verify_correct _ _ _ _ hm, vec_deref_val, h2, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

/-! ## (C) No false alarms for well-formed keys -/

/-- Keys from key generation are well formed, and the public key returned is
the one the private key holds. -/
theorem keygen_keyOk (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (h : slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk)) :
    Spec.KeyOk (bytes sk.val) ∧ bytes pk.val = Spec.skPk (bytes sk.val) := by
  obtain ⟨sk', pk', h', e⟩ := keygen_correct sk_seed sk_prf pk_seed
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk _ _ _ (bytes_length16 sk_seed) (bytes_length16 sk_prf) (bytes_length16 pk_seed)
  rw [← e] at this
  exact this

theorem sign_internal_checked_complete (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) (hk : Spec.KeyOk (bytes sk.val)) :
    ∃ sig, slh.slh_sign_internal_checked m sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (slh_sign_internal_checked_spec m sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignInternalChecked_complete (bytes m.val) (bytes sk.val) (bytes addrnd.val) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem sign_checked_complete (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk (bytes sk.val)) :
    ∃ sig, slh.slh_sign_checked m ctx sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (slh_sign_checked_spec m ctx sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (bytes addrnd.val) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem api_sign_checked_complete (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk (bytes sk.val)) :
    ∃ sig, api.sign_checked m ctx sk addrnd = ok (some sig) :=
  sign_checked_complete m ctx sk addrnd hm hc hk

theorem api_sign_deterministic_checked_complete (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk (bytes sk.val)) :
    ∃ sig, api.sign_deterministic_checked m ctx sk = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (api_sign_deterministic_checked_spec m ctx sk hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

/-! ## (E) The rest of `api` -/

/-- `api.keygen` writes the keys of FIPS 205 Algorithm 18 for the three
16-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of `seeds`. -/
theorem api_keygen_correct (seeds : Array U8 48#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize) :
    ∃ sk' pk', api.keygen seeds sk pk = ok (sk', pk') ∧
      (bytes sk'.val, bytes pk'.val) =
        Spec.slhKeygenInternal (Spec.block (bytes seeds.val) 0) (Spec.block (bytes seeds.val) 1)
          (Spec.block (bytes seeds.val) 2) := by
  obtain ⟨⟨sk', pk'⟩, h, hp⟩ := spec_imp_exists (api_keygen_spec seeds sk pk)
  exact ⟨sk', pk', h, hp⟩

theorem block48_length (seeds : Array U8 48#usize) (i : Nat) (hi : i < 3) :
    (Spec.block (bytes seeds.val) i).length = Spec.n := by
  simp [Spec.block, Spec.n]; omega

/-- Keys from `api.keygen` are well formed, and `api.public_key` of the
private key is the public key it wrote. -/
theorem api_keygen_keyOk (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
    (sk : Array U8 64#usize) (pk : Array U8 32#usize) (h : api.keygen seeds sk0 pk0 = ok (sk, pk)) :
    Spec.KeyOk (bytes sk.val) ∧ bytes pk.val = Spec.skPk (bytes sk.val) ∧ api.public_key sk = ok pk := by
  obtain ⟨sk', pk', h', e⟩ := api_keygen_correct seeds sk0 pk0
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk _ _ _ (block48_length seeds 0 (by omega)) (block48_length seeds 1 (by omega))
    (block48_length seeds 2 (by omega))
  rw [← e] at this
  refine ⟨this.1, this.2, ?_⟩
  obtain ⟨p, hp1, hp2⟩ := api_public_key_correct sk'
  rw [hp1]
  congr 1
  apply Std.Array.ext
  apply ht_bytes_injective
  rw [hp2]
  exact this.2.symm

/-- `api.verify` is FIPS 205 Algorithm 24 (the right-hand side of `verify_correct`). -/
theorem api_verify_correct (m sig ctx : Slice U8) (pk : Array U8 32#usize) (hm : Room m.length 409) :
    api.verify m sig ctx pk =
      ok (Spec.slhVerify (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) :=
  verify_correct m sig ctx pk hm

/-- `api.sign` is FIPS 205 Algorithm 22 (the right-hand side of `sign_correct`). -/
theorem api_sign_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, api.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  sign_correct m ctx sk addrnd hm

/-- `api.sign_deterministic` is FIPS 205 Algorithm 22, deterministic variant
(`PK.seed` as the randomness); it returns a signature whenever the context
string has at most 255 bytes. -/
theorem api_sign_deterministic_correct (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) :
    ∃ r, api.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block (bytes sk.val) 2) ∧
      (ctx.length ≤ 255 → r.isSome) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (api_sign_deterministic_spec m ctx sk hm)
  refine ⟨r, h, hr, fun hc => ?_⟩
  have : ¬ (bytes ctx.val).length > 255 := by simp; scalar_tac
  simp only [Spec.slhSign, this, ↓reduceIte] at hr
  cases r <;> simp_all

/-! ## (D) Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, slh.slh_sign_internal m sk addrnd = ok sig ∧ slh.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal _ _ _ hk]

theorem complete_internal_checked (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, slh.slh_sign_internal_checked m sk addrnd = ok (some sig) ∧
      slh.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_internal_checked_complete m sk addrnd hm hk
  exact ⟨sig, h, sign_internal_checked_verifies m sk addrnd pk sig hm hpk h⟩

theorem complete (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, slh.slh_sign m ctx sk addrnd = ok (some sig) ∧ slh.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

theorem complete_checked (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, slh.slh_sign_checked m ctx sk addrnd = ok (some sig) ∧
      slh.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, sign_checked_verifies m ctx sk addrnd pk sig hm hpk h⟩

/-- With keys from `api.keygen`, the plain hedged signer's signatures verify. -/
theorem api_complete_sign (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
    (sk : Array U8 64#usize) (pk : Array U8 32#usize) (hkg : api.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, api.sign m ctx sk addrnd = ok (some sig) ∧ api.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := api_sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `api.keygen`, the plain deterministic signer's signatures verify. -/
theorem api_complete_sign_deterministic (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : api.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, api.sign_deterministic m ctx sk = ok (some sig) ∧ api.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr, -⟩ := api_sign_deterministic_correct m ctx sk hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `api.keygen`, the checked hedged signer always returns a
signature, and it verifies. -/
theorem api_complete_sign_checked (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : api.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, api.sign_checked m ctx sk addrnd = ok (some sig) ∧ api.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, api_sign_checked_verifies m ctx sk addrnd pk sig hm h hpub⟩

/-- With keys from `api.keygen`, the checked deterministic signer always
returns a signature, and it verifies. -/
theorem api_complete_sign_deterministic_checked (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : api.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, api.sign_deterministic_checked m ctx sk = ok (some sig) ∧ api.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_deterministic_checked_complete m ctx sk hm hc hk
  exact ⟨sig, h, api_sign_deterministic_checked_verifies m ctx sk pk sig hm h hpub⟩

end slhdsa

#print axioms slhdsa.sign_internal_checked_correct
#print axioms slhdsa.sign_checked_correct
#print axioms slhdsa.api_sign_checked_correct
#print axioms slhdsa.api_sign_deterministic_checked_correct
#print axioms slhdsa.spec_sign_internal_checked_verifies
#print axioms slhdsa.spec_sign_checked_verifies
#print axioms slhdsa.sign_internal_checked_verifies
#print axioms slhdsa.sign_checked_verifies
#print axioms slhdsa.api_public_key_correct
#print axioms slhdsa.api_sign_checked_verifies
#print axioms slhdsa.api_sign_deterministic_checked_verifies
#print axioms slhdsa.keygen_keyOk
#print axioms slhdsa.sign_internal_checked_complete
#print axioms slhdsa.sign_checked_complete
#print axioms slhdsa.api_sign_checked_complete
#print axioms slhdsa.api_sign_deterministic_checked_complete
#print axioms slhdsa.api_keygen_correct
#print axioms slhdsa.api_keygen_keyOk
#print axioms slhdsa.api_verify_correct
#print axioms slhdsa.api_sign_correct
#print axioms slhdsa.api_sign_deterministic_correct
#print axioms slhdsa.complete_internal
#print axioms slhdsa.complete_internal_checked
#print axioms slhdsa.complete
#print axioms slhdsa.complete_checked
#print axioms slhdsa.api_complete_sign
#print axioms slhdsa.api_complete_sign_deterministic
#print axioms slhdsa.api_complete_sign_checked
#print axioms slhdsa.api_complete_sign_deterministic_checked

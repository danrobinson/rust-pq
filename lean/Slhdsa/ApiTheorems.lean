import Slhdsa.Theorems
import Spec.Correctness
open Aeneas Aeneas.Std Result

/-!
# Results about the checked signer and the crate's interface, per parameter set

For each of the six sets, the statements of the single-set tree's
`ApiTheorems.lean`, about the per-set functions of `sets.rs` (fixed-size key
types) and FIPS 205 at that set:

* (A) the checked signer never fails, and every signature it releases is the
  signature of FIPS 205 (the right-hand sides of `sign_internal_correct` and
  `sign_correct`);
* (B) every signature it releases verifies under the public key held in the
  private key, for every private key;
* (C) for a well-formed private key (`Spec.KeyOk`: the last block is the root
  that key generation derives from the first and third; in particular every
  key that key generation produced) it always releases a signature;
* (D) completeness: with a key from key generation, the signatures of the
  plain and the checked signers verify;
* (E) the rest of the interface: `keygen`, `public_key`, `verify`, and the
  plain `sign` and `sign_deterministic`.

`Spec.skPk p sk` is `sk.drop (2n)`, the public key `PK.seed ‖ PK.root` held in
a private key. The hypotheses `Room` are those of `Theorems.lean`. Generated
by a script from the single-set file (the same proofs, at each set).
-/

namespace slhdsa

theorem ok_inj {α} {m : Result α} {r v : α} (h1 : m = ok r) (h2 : m = ok v) : r = v := by
  rw [h1] at h2; simpa using h2

/-! ## SLH-DSA-SHA2-128s -/

namespace sha2_128s

theorem bytes_lengthN (x : Array U8 16#usize) : (bytes x.val).length = Spec.sha2_128s.n := by
  simp [Spec.sha2_128s]

theorem verify_eq (m sig ctx : Slice U8) (pk : Array U8 32#usize) :
    sets.sha2_128s.verify m sig ctx pk = sets.sha2_128s.slh_verify m sig ctx pk := by
  unfold sets.sha2_128s.verify sets.sha2_128s.slh_verify api.verify; rfl

theorem blockSeed_length (seeds : Array U8 48#usize) (i : Nat) (hi : i < 3) :
    (Spec.block Spec.sha2_128s (bytes seeds.val) i).length = Spec.sha2_128s.n := by
  simp [Spec.block, Spec.sha2_128s]; omega

/-! ## (A) Exactness -/

/-- The checked signer returns, and what it returns is either nothing or the
signature of FIPS 205 Algorithm 19. -/
theorem sign_internal_checked_correct (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) :
    ∃ r, sets.sha2_128s.slh_sign_internal_checked m sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        bytes sig.val = Spec.slhSignInternal Spec.sha2_128s (bytes m.val) (bytes sk.val) (bytes addrnd.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128s.slh_sign_internal_checked_spec m sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignInternalChecked_sound Spec.sha2_128s Spec.sha2_128s_valid _ _ _ _ hr.symm).1

/-- The checked signer with a context string: nothing, or the signature of
FIPS 205 Algorithm 22. -/
theorem sign_checked_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128s.slh_sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_128s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128s.slh_sign_checked_spec m ctx sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_128s Spec.sha2_128s_valid _ _ _ _ _ hr.symm).1

theorem api_sign_checked_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128s.sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_128s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) :=
  sign_checked_correct m ctx sk addrnd hm

/-- The deterministic checked signer: nothing, or the signature of FIPS 205
Algorithm 22 with `PK.seed` as the randomness (the deterministic variant). -/
theorem api_sign_deterministic_checked_correct (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128s.sign_deterministic_checked m ctx sk = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_128s (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_128s (bytes sk.val) 2) =
          some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128s.sign_deterministic_checked_spec m ctx sk hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_128s Spec.sha2_128s_valid _ _ _ _ _ hr.symm).1

/-! ## (B) Released signatures verify, for every private key -/

/-- At the level of the specification. -/
theorem spec_sign_internal_checked_verifies (msg sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignInternalChecked Spec.sha2_128s msg sk addrnd = some sig) :
    Spec.slhVerifyInternal Spec.sha2_128s msg sig (Spec.skPk Spec.sha2_128s sk) = true :=
  (Spec.slhSignInternalChecked_sound Spec.sha2_128s Spec.sha2_128s_valid msg sk addrnd sig h).2

theorem spec_sign_checked_verifies (msg ctx sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignChecked Spec.sha2_128s msg ctx sk addrnd = some sig) :
    Spec.slhVerify Spec.sha2_128s msg sig ctx (Spec.skPk Spec.sha2_128s sk) = true :=
  (Spec.slhSignChecked_sound Spec.sha2_128s Spec.sha2_128s_valid msg ctx sk addrnd sig h).2

theorem sign_internal_checked_verifies (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 152) (hpk : bytes pk.val = Spec.skPk Spec.sha2_128s (bytes sk.val))
    (h : sets.sha2_128s.slh_sign_internal_checked m sk addrnd = ok (some sig)) :
    sets.sha2_128s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_128s.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hpk,
    spec_sign_internal_checked_verifies _ _ _ _ hp.symm]

theorem sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 409) (hpk : bytes pk.val = Spec.skPk Spec.sha2_128s (bytes sk.val))
    (h : sets.sha2_128s.slh_sign_checked m ctx sk addrnd = ok (some sig)) :
    sets.sha2_128s.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_128s.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_correct _ _ _ _ hm, vec_deref_val, hpk, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

theorem api_public_key_correct (sk : Array U8 64#usize) :
    ∃ pk, sets.sha2_128s.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_128s (bytes sk.val) :=
  spec_imp_exists (sha2_128s.public_key_spec sk)

/-- A signature released by `sets.sha2_128s.sign_checked` verifies under
`sets.sha2_128s.public_key sk`, for every `sk`. -/
theorem api_sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 409)
    (h : sets.sha2_128s.sign_checked m ctx sk addrnd = ok (some sig)) (hpk : sets.sha2_128s.public_key sk = ok pk) :
    sets.sha2_128s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  exact sign_checked_verifies m ctx sk addrnd pk sig hm h2 h

theorem api_sign_deterministic_checked_verifies (m ctx : Slice U8) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 409)
    (h : sets.sha2_128s.sign_deterministic_checked m ctx sk = ok (some sig)) (hpk : sets.sha2_128s.public_key sk = ok pk) :
    sets.sha2_128s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_128s.sign_deterministic_checked_spec m ctx sk hm)
  obtain rfl := ok_inj h hr
  rw [verify_eq, verify_correct _ _ _ _ hm, vec_deref_val, h2, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

/-! ## (C) No false alarms for well-formed keys -/

/-- Keys from key generation are well formed, and the public key returned is
the one the private key holds. -/
theorem keygen_keyOk (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (h : sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_128s (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_128s (bytes sk.val) := by
  obtain ⟨sk', pk', h', e⟩ := keygen_correct sk_seed sk_prf pk_seed
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_128s Spec.sha2_128s_valid _ _ _ (bytes_lengthN sk_seed) (bytes_lengthN sk_prf) (bytes_lengthN pk_seed)
  rw [← e] at this
  exact this

theorem sign_internal_checked_complete (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) (hk : Spec.KeyOk Spec.sha2_128s (bytes sk.val)) :
    ∃ sig, sets.sha2_128s.slh_sign_internal_checked m sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128s.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignInternalChecked_complete Spec.sha2_128s Spec.sha2_128s_valid (bytes m.val) (bytes sk.val) (bytes addrnd.val) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem sign_checked_complete (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_128s (bytes sk.val)) :
    ∃ sig, sets.sha2_128s.slh_sign_checked m ctx sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128s.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_128s Spec.sha2_128s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (bytes addrnd.val) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem api_sign_checked_complete (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_128s (bytes sk.val)) :
    ∃ sig, sets.sha2_128s.sign_checked m ctx sk addrnd = ok (some sig) :=
  sign_checked_complete m ctx sk addrnd hm hc hk

theorem api_sign_deterministic_checked_complete (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_128s (bytes sk.val)) :
    ∃ sig, sets.sha2_128s.sign_deterministic_checked m ctx sk = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128s.sign_deterministic_checked_spec m ctx sk hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_128s Spec.sha2_128s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_128s (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

/-! ## (E) The rest of `api` -/

/-- `sets.sha2_128s.keygen` writes the keys of FIPS 205 Algorithm 18 for the three
16-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of `seeds`. -/
theorem api_keygen_correct (seeds : Array U8 48#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize) :
    ∃ sk' pk', sets.sha2_128s.keygen seeds sk pk = ok (sk', pk') ∧
      (bytes sk'.val, bytes pk'.val) =
        Spec.slhKeygenInternal Spec.sha2_128s (Spec.block Spec.sha2_128s (bytes seeds.val) 0) (Spec.block Spec.sha2_128s (bytes seeds.val) 1)
          (Spec.block Spec.sha2_128s (bytes seeds.val) 2) := by
  obtain ⟨⟨sk', pk'⟩, h, hp⟩ := spec_imp_exists (sha2_128s.keygen_spec seeds sk pk)
  exact ⟨sk', pk', h, hp⟩

/-- Keys from `sets.sha2_128s.keygen` are well formed, and `sets.sha2_128s.public_key` of the
private key is the public key it wrote. -/
theorem api_keygen_keyOk (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
    (sk : Array U8 64#usize) (pk : Array U8 32#usize) (h : sets.sha2_128s.keygen seeds sk0 pk0 = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_128s (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_128s (bytes sk.val) ∧ sets.sha2_128s.public_key sk = ok pk := by
  obtain ⟨sk', pk', h', e⟩ := api_keygen_correct seeds sk0 pk0
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_128s Spec.sha2_128s_valid _ _ _ (blockSeed_length seeds 0 (by omega)) (blockSeed_length seeds 1 (by omega))
    (blockSeed_length seeds 2 (by omega))
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
    sets.sha2_128s.verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_128s (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) :=
  verify_correct m sig ctx pk hm

/-- `api.sign` is FIPS 205 Algorithm 22 (the right-hand side of `sign_correct`). -/
theorem api_sign_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128s.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_128s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  sign_correct m ctx sk addrnd hm

/-- `api.sign_deterministic` is FIPS 205 Algorithm 22, deterministic variant
(`PK.seed` as the randomness); it returns a signature whenever the context
string has at most 255 bytes. -/
theorem api_sign_deterministic_correct (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128s.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_128s (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_128s (bytes sk.val) 2) ∧
      (ctx.length ≤ 255 → r.isSome) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128s.sign_deterministic_spec m ctx sk hm)
  refine ⟨r, h, hr, fun hc => ?_⟩
  have : ¬ (bytes ctx.val).length > 255 := by simp; scalar_tac
  simp only [Spec.slhSign, this, ↓reduceIte] at hr
  cases r <;> simp_all

/-! ## (D) Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, sets.sha2_128s.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_128s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_128s Spec.sha2_128s_valid _ _ _ hk]

theorem complete_internal_checked (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, sets.sha2_128s.slh_sign_internal_checked m sk addrnd = ok (some sig) ∧
      sets.sha2_128s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_internal_checked_complete m sk addrnd hm hk
  exact ⟨sig, h, sign_internal_checked_verifies m sk addrnd pk sig hm hpk h⟩

theorem complete (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128s.slh_sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_128s.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_128s Spec.sha2_128s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

theorem complete_checked (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128s.slh_sign_checked m ctx sk addrnd = ok (some sig) ∧
      sets.sha2_128s.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, sign_checked_verifies m ctx sk addrnd pk sig hm hpk h⟩

/-- With keys from `sets.sha2_128s.keygen`, the plain hedged signer's signatures verify. -/
theorem api_complete_sign (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
    (sk : Array U8 64#usize) (pk : Array U8 32#usize) (hkg : sets.sha2_128s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128s.sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_128s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := api_sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_128s Spec.sha2_128s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_128s.keygen`, the plain deterministic signer's signatures verify. -/
theorem api_complete_sign_deterministic (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : sets.sha2_128s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128s.sign_deterministic m ctx sk = ok (some sig) ∧ sets.sha2_128s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr, -⟩ := api_sign_deterministic_correct m ctx sk hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_128s Spec.sha2_128s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_128s (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_128s.keygen`, the checked hedged signer always returns a
signature, and it verifies. -/
theorem api_complete_sign_checked (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : sets.sha2_128s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128s.sign_checked m ctx sk addrnd = ok (some sig) ∧ sets.sha2_128s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, api_sign_checked_verifies m ctx sk addrnd pk sig hm h hpub⟩

/-- With keys from `sets.sha2_128s.keygen`, the checked deterministic signer always
returns a signature, and it verifies. -/
theorem api_complete_sign_deterministic_checked (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : sets.sha2_128s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128s.sign_deterministic_checked m ctx sk = ok (some sig) ∧ sets.sha2_128s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_deterministic_checked_complete m ctx sk hm hc hk
  exact ⟨sig, h, api_sign_deterministic_checked_verifies m ctx sk pk sig hm h hpub⟩


end sha2_128s

/-! ## SLH-DSA-SHA2-128f -/

namespace sha2_128f

theorem bytes_lengthN (x : Array U8 16#usize) : (bytes x.val).length = Spec.sha2_128f.n := by
  simp [Spec.sha2_128f]

theorem verify_eq (m sig ctx : Slice U8) (pk : Array U8 32#usize) :
    sets.sha2_128f.verify m sig ctx pk = sets.sha2_128f.slh_verify m sig ctx pk := by
  unfold sets.sha2_128f.verify sets.sha2_128f.slh_verify api.verify; rfl

theorem blockSeed_length (seeds : Array U8 48#usize) (i : Nat) (hi : i < 3) :
    (Spec.block Spec.sha2_128f (bytes seeds.val) i).length = Spec.sha2_128f.n := by
  simp [Spec.block, Spec.sha2_128f]; omega

/-! ## (A) Exactness -/

/-- The checked signer returns, and what it returns is either nothing or the
signature of FIPS 205 Algorithm 19. -/
theorem sign_internal_checked_correct (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) :
    ∃ r, sets.sha2_128f.slh_sign_internal_checked m sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        bytes sig.val = Spec.slhSignInternal Spec.sha2_128f (bytes m.val) (bytes sk.val) (bytes addrnd.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128f.slh_sign_internal_checked_spec m sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignInternalChecked_sound Spec.sha2_128f Spec.sha2_128f_valid _ _ _ _ hr.symm).1

/-- The checked signer with a context string: nothing, or the signature of
FIPS 205 Algorithm 22. -/
theorem sign_checked_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128f.slh_sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_128f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128f.slh_sign_checked_spec m ctx sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_128f Spec.sha2_128f_valid _ _ _ _ _ hr.symm).1

theorem api_sign_checked_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128f.sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_128f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) :=
  sign_checked_correct m ctx sk addrnd hm

/-- The deterministic checked signer: nothing, or the signature of FIPS 205
Algorithm 22 with `PK.seed` as the randomness (the deterministic variant). -/
theorem api_sign_deterministic_checked_correct (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128f.sign_deterministic_checked m ctx sk = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_128f (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_128f (bytes sk.val) 2) =
          some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128f.sign_deterministic_checked_spec m ctx sk hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_128f Spec.sha2_128f_valid _ _ _ _ _ hr.symm).1

/-! ## (B) Released signatures verify, for every private key -/

/-- At the level of the specification. -/
theorem spec_sign_internal_checked_verifies (msg sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignInternalChecked Spec.sha2_128f msg sk addrnd = some sig) :
    Spec.slhVerifyInternal Spec.sha2_128f msg sig (Spec.skPk Spec.sha2_128f sk) = true :=
  (Spec.slhSignInternalChecked_sound Spec.sha2_128f Spec.sha2_128f_valid msg sk addrnd sig h).2

theorem spec_sign_checked_verifies (msg ctx sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignChecked Spec.sha2_128f msg ctx sk addrnd = some sig) :
    Spec.slhVerify Spec.sha2_128f msg sig ctx (Spec.skPk Spec.sha2_128f sk) = true :=
  (Spec.slhSignChecked_sound Spec.sha2_128f Spec.sha2_128f_valid msg ctx sk addrnd sig h).2

theorem sign_internal_checked_verifies (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 152) (hpk : bytes pk.val = Spec.skPk Spec.sha2_128f (bytes sk.val))
    (h : sets.sha2_128f.slh_sign_internal_checked m sk addrnd = ok (some sig)) :
    sets.sha2_128f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_128f.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hpk,
    spec_sign_internal_checked_verifies _ _ _ _ hp.symm]

theorem sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 409) (hpk : bytes pk.val = Spec.skPk Spec.sha2_128f (bytes sk.val))
    (h : sets.sha2_128f.slh_sign_checked m ctx sk addrnd = ok (some sig)) :
    sets.sha2_128f.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_128f.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_correct _ _ _ _ hm, vec_deref_val, hpk, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

theorem api_public_key_correct (sk : Array U8 64#usize) :
    ∃ pk, sets.sha2_128f.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_128f (bytes sk.val) :=
  spec_imp_exists (sha2_128f.public_key_spec sk)

/-- A signature released by `sets.sha2_128f.sign_checked` verifies under
`sets.sha2_128f.public_key sk`, for every `sk`. -/
theorem api_sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 409)
    (h : sets.sha2_128f.sign_checked m ctx sk addrnd = ok (some sig)) (hpk : sets.sha2_128f.public_key sk = ok pk) :
    sets.sha2_128f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  exact sign_checked_verifies m ctx sk addrnd pk sig hm h2 h

theorem api_sign_deterministic_checked_verifies (m ctx : Slice U8) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 409)
    (h : sets.sha2_128f.sign_deterministic_checked m ctx sk = ok (some sig)) (hpk : sets.sha2_128f.public_key sk = ok pk) :
    sets.sha2_128f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_128f.sign_deterministic_checked_spec m ctx sk hm)
  obtain rfl := ok_inj h hr
  rw [verify_eq, verify_correct _ _ _ _ hm, vec_deref_val, h2, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

/-! ## (C) No false alarms for well-formed keys -/

/-- Keys from key generation are well formed, and the public key returned is
the one the private key holds. -/
theorem keygen_keyOk (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (h : sets.sha2_128f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_128f (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_128f (bytes sk.val) := by
  obtain ⟨sk', pk', h', e⟩ := keygen_correct sk_seed sk_prf pk_seed
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_128f Spec.sha2_128f_valid _ _ _ (bytes_lengthN sk_seed) (bytes_lengthN sk_prf) (bytes_lengthN pk_seed)
  rw [← e] at this
  exact this

theorem sign_internal_checked_complete (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 152) (hk : Spec.KeyOk Spec.sha2_128f (bytes sk.val)) :
    ∃ sig, sets.sha2_128f.slh_sign_internal_checked m sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128f.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignInternalChecked_complete Spec.sha2_128f Spec.sha2_128f_valid (bytes m.val) (bytes sk.val) (bytes addrnd.val) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem sign_checked_complete (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_128f (bytes sk.val)) :
    ∃ sig, sets.sha2_128f.slh_sign_checked m ctx sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128f.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_128f Spec.sha2_128f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (bytes addrnd.val) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem api_sign_checked_complete (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_128f (bytes sk.val)) :
    ∃ sig, sets.sha2_128f.sign_checked m ctx sk addrnd = ok (some sig) :=
  sign_checked_complete m ctx sk addrnd hm hc hk

theorem api_sign_deterministic_checked_complete (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_128f (bytes sk.val)) :
    ∃ sig, sets.sha2_128f.sign_deterministic_checked m ctx sk = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128f.sign_deterministic_checked_spec m ctx sk hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_128f Spec.sha2_128f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_128f (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

/-! ## (E) The rest of `api` -/

/-- `sets.sha2_128f.keygen` writes the keys of FIPS 205 Algorithm 18 for the three
16-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of `seeds`. -/
theorem api_keygen_correct (seeds : Array U8 48#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize) :
    ∃ sk' pk', sets.sha2_128f.keygen seeds sk pk = ok (sk', pk') ∧
      (bytes sk'.val, bytes pk'.val) =
        Spec.slhKeygenInternal Spec.sha2_128f (Spec.block Spec.sha2_128f (bytes seeds.val) 0) (Spec.block Spec.sha2_128f (bytes seeds.val) 1)
          (Spec.block Spec.sha2_128f (bytes seeds.val) 2) := by
  obtain ⟨⟨sk', pk'⟩, h, hp⟩ := spec_imp_exists (sha2_128f.keygen_spec seeds sk pk)
  exact ⟨sk', pk', h, hp⟩

/-- Keys from `sets.sha2_128f.keygen` are well formed, and `sets.sha2_128f.public_key` of the
private key is the public key it wrote. -/
theorem api_keygen_keyOk (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
    (sk : Array U8 64#usize) (pk : Array U8 32#usize) (h : sets.sha2_128f.keygen seeds sk0 pk0 = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_128f (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_128f (bytes sk.val) ∧ sets.sha2_128f.public_key sk = ok pk := by
  obtain ⟨sk', pk', h', e⟩ := api_keygen_correct seeds sk0 pk0
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_128f Spec.sha2_128f_valid _ _ _ (blockSeed_length seeds 0 (by omega)) (blockSeed_length seeds 1 (by omega))
    (blockSeed_length seeds 2 (by omega))
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
    sets.sha2_128f.verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_128f (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) :=
  verify_correct m sig ctx pk hm

/-- `api.sign` is FIPS 205 Algorithm 22 (the right-hand side of `sign_correct`). -/
theorem api_sign_correct (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128f.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_128f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  sign_correct m ctx sk addrnd hm

/-- `api.sign_deterministic` is FIPS 205 Algorithm 22, deterministic variant
(`PK.seed` as the randomness); it returns a signature whenever the context
string has at most 255 bytes. -/
theorem api_sign_deterministic_correct (m ctx : Slice U8) (sk : Array U8 64#usize)
    (hm : Room m.length 409) :
    ∃ r, sets.sha2_128f.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_128f (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_128f (bytes sk.val) 2) ∧
      (ctx.length ≤ 255 → r.isSome) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_128f.sign_deterministic_spec m ctx sk hm)
  refine ⟨r, h, hr, fun hc => ?_⟩
  have : ¬ (bytes ctx.val).length > 255 := by simp; scalar_tac
  simp only [Spec.slhSign, this, ↓reduceIte] at hr
  cases r <;> simp_all

/-! ## (D) Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, sets.sha2_128f.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_128f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_128f Spec.sha2_128f_valid _ _ _ hk]

theorem complete_internal_checked (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, sets.sha2_128f.slh_sign_internal_checked m sk addrnd = ok (some sig) ∧
      sets.sha2_128f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_internal_checked_complete m sk addrnd hm hk
  exact ⟨sig, h, sign_internal_checked_verifies m sk addrnd pk sig hm hpk h⟩

theorem complete (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128f.slh_sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_128f.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_128f Spec.sha2_128f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

theorem complete_checked (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128f.slh_sign_checked m ctx sk addrnd = ok (some sig) ∧
      sets.sha2_128f.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, sign_checked_verifies m ctx sk addrnd pk sig hm hpk h⟩

/-- With keys from `sets.sha2_128f.keygen`, the plain hedged signer's signatures verify. -/
theorem api_complete_sign (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
    (sk : Array U8 64#usize) (pk : Array U8 32#usize) (hkg : sets.sha2_128f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128f.sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_128f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := api_sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_128f Spec.sha2_128f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_128f.keygen`, the plain deterministic signer's signatures verify. -/
theorem api_complete_sign_deterministic (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : sets.sha2_128f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128f.sign_deterministic m ctx sk = ok (some sig) ∧ sets.sha2_128f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr, -⟩ := api_sign_deterministic_correct m ctx sk hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_128f Spec.sha2_128f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_128f (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_128f.keygen`, the checked hedged signer always returns a
signature, and it verifies. -/
theorem api_complete_sign_checked (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : sets.sha2_128f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128f.sign_checked m ctx sk addrnd = ok (some sig) ∧ sets.sha2_128f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, api_sign_checked_verifies m ctx sk addrnd pk sig hm h hpub⟩

/-- With keys from `sets.sha2_128f.keygen`, the checked deterministic signer always
returns a signature, and it verifies. -/
theorem api_complete_sign_deterministic_checked (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize)
    (pk0 : Array U8 32#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize)
    (hkg : sets.sha2_128f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 409) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_128f.sign_deterministic_checked m ctx sk = ok (some sig) ∧ sets.sha2_128f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_deterministic_checked_complete m ctx sk hm hc hk
  exact ⟨sig, h, api_sign_deterministic_checked_verifies m ctx sk pk sig hm h hpub⟩


end sha2_128f

/-! ## SLH-DSA-SHA2-192s -/

namespace sha2_192s

theorem bytes_lengthN (x : Array U8 24#usize) : (bytes x.val).length = Spec.sha2_192s.n := by
  simp [Spec.sha2_192s]

theorem verify_eq (m sig ctx : Slice U8) (pk : Array U8 48#usize) :
    sets.sha2_192s.verify m sig ctx pk = sets.sha2_192s.slh_verify m sig ctx pk := by
  unfold sets.sha2_192s.verify sets.sha2_192s.slh_verify api.verify; rfl

theorem blockSeed_length (seeds : Array U8 72#usize) (i : Nat) (hi : i < 3) :
    (Spec.block Spec.sha2_192s (bytes seeds.val) i).length = Spec.sha2_192s.n := by
  simp [Spec.block, Spec.sha2_192s]; omega

/-! ## (A) Exactness -/

/-- The checked signer returns, and what it returns is either nothing or the
signature of FIPS 205 Algorithm 19. -/
theorem sign_internal_checked_correct (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 304) :
    ∃ r, sets.sha2_192s.slh_sign_internal_checked m sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        bytes sig.val = Spec.slhSignInternal Spec.sha2_192s (bytes m.val) (bytes sk.val) (bytes addrnd.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192s.slh_sign_internal_checked_spec m sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignInternalChecked_sound Spec.sha2_192s Spec.sha2_192s_valid _ _ _ _ hr.symm).1

/-- The checked signer with a context string: nothing, or the signature of
FIPS 205 Algorithm 22. -/
theorem sign_checked_correct (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192s.slh_sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_192s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192s.slh_sign_checked_spec m ctx sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_192s Spec.sha2_192s_valid _ _ _ _ _ hr.symm).1

theorem api_sign_checked_correct (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192s.sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_192s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) :=
  sign_checked_correct m ctx sk addrnd hm

/-- The deterministic checked signer: nothing, or the signature of FIPS 205
Algorithm 22 with `PK.seed` as the randomness (the deterministic variant). -/
theorem api_sign_deterministic_checked_correct (m ctx : Slice U8) (sk : Array U8 96#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192s.sign_deterministic_checked m ctx sk = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_192s (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_192s (bytes sk.val) 2) =
          some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192s.sign_deterministic_checked_spec m ctx sk hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_192s Spec.sha2_192s_valid _ _ _ _ _ hr.symm).1

/-! ## (B) Released signatures verify, for every private key -/

/-- At the level of the specification. -/
theorem spec_sign_internal_checked_verifies (msg sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignInternalChecked Spec.sha2_192s msg sk addrnd = some sig) :
    Spec.slhVerifyInternal Spec.sha2_192s msg sig (Spec.skPk Spec.sha2_192s sk) = true :=
  (Spec.slhSignInternalChecked_sound Spec.sha2_192s Spec.sha2_192s_valid msg sk addrnd sig h).2

theorem spec_sign_checked_verifies (msg ctx sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignChecked Spec.sha2_192s msg ctx sk addrnd = some sig) :
    Spec.slhVerify Spec.sha2_192s msg sig ctx (Spec.skPk Spec.sha2_192s sk) = true :=
  (Spec.slhSignChecked_sound Spec.sha2_192s Spec.sha2_192s_valid msg ctx sk addrnd sig h).2

theorem sign_internal_checked_verifies (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (pk : Array U8 48#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 304) (hpk : bytes pk.val = Spec.skPk Spec.sha2_192s (bytes sk.val))
    (h : sets.sha2_192s.slh_sign_internal_checked m sk addrnd = ok (some sig)) :
    sets.sha2_192s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_192s.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hpk,
    spec_sign_internal_checked_verifies _ _ _ _ hp.symm]

theorem sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (pk : Array U8 48#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 561) (hpk : bytes pk.val = Spec.skPk Spec.sha2_192s (bytes sk.val))
    (h : sets.sha2_192s.slh_sign_checked m ctx sk addrnd = ok (some sig)) :
    sets.sha2_192s.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_192s.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_correct _ _ _ _ hm, vec_deref_val, hpk, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

theorem api_public_key_correct (sk : Array U8 96#usize) :
    ∃ pk, sets.sha2_192s.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_192s (bytes sk.val) :=
  spec_imp_exists (sha2_192s.public_key_spec sk)

/-- A signature released by `sets.sha2_192s.sign_checked` verifies under
`sets.sha2_192s.public_key sk`, for every `sk`. -/
theorem api_sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (pk : Array U8 48#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 561)
    (h : sets.sha2_192s.sign_checked m ctx sk addrnd = ok (some sig)) (hpk : sets.sha2_192s.public_key sk = ok pk) :
    sets.sha2_192s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  exact sign_checked_verifies m ctx sk addrnd pk sig hm h2 h

theorem api_sign_deterministic_checked_verifies (m ctx : Slice U8) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 561)
    (h : sets.sha2_192s.sign_deterministic_checked m ctx sk = ok (some sig)) (hpk : sets.sha2_192s.public_key sk = ok pk) :
    sets.sha2_192s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_192s.sign_deterministic_checked_spec m ctx sk hm)
  obtain rfl := ok_inj h hr
  rw [verify_eq, verify_correct _ _ _ _ hm, vec_deref_val, h2, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

/-! ## (C) No false alarms for well-formed keys -/

/-- Keys from key generation are well formed, and the public key returned is
the one the private key holds. -/
theorem keygen_keyOk (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (h : sets.sha2_192s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_192s (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_192s (bytes sk.val) := by
  obtain ⟨sk', pk', h', e⟩ := keygen_correct sk_seed sk_prf pk_seed
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_192s Spec.sha2_192s_valid _ _ _ (bytes_lengthN sk_seed) (bytes_lengthN sk_prf) (bytes_lengthN pk_seed)
  rw [← e] at this
  exact this

theorem sign_internal_checked_complete (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 304) (hk : Spec.KeyOk Spec.sha2_192s (bytes sk.val)) :
    ∃ sig, sets.sha2_192s.slh_sign_internal_checked m sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192s.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignInternalChecked_complete Spec.sha2_192s Spec.sha2_192s_valid (bytes m.val) (bytes sk.val) (bytes addrnd.val) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem sign_checked_complete (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_192s (bytes sk.val)) :
    ∃ sig, sets.sha2_192s.slh_sign_checked m ctx sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192s.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_192s Spec.sha2_192s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (bytes addrnd.val) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem api_sign_checked_complete (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_192s (bytes sk.val)) :
    ∃ sig, sets.sha2_192s.sign_checked m ctx sk addrnd = ok (some sig) :=
  sign_checked_complete m ctx sk addrnd hm hc hk

theorem api_sign_deterministic_checked_complete (m ctx : Slice U8) (sk : Array U8 96#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_192s (bytes sk.val)) :
    ∃ sig, sets.sha2_192s.sign_deterministic_checked m ctx sk = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192s.sign_deterministic_checked_spec m ctx sk hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_192s Spec.sha2_192s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_192s (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

/-! ## (E) The rest of `api` -/

/-- `sets.sha2_192s.keygen` writes the keys of FIPS 205 Algorithm 18 for the three
24-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of `seeds`. -/
theorem api_keygen_correct (seeds : Array U8 72#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize) :
    ∃ sk' pk', sets.sha2_192s.keygen seeds sk pk = ok (sk', pk') ∧
      (bytes sk'.val, bytes pk'.val) =
        Spec.slhKeygenInternal Spec.sha2_192s (Spec.block Spec.sha2_192s (bytes seeds.val) 0) (Spec.block Spec.sha2_192s (bytes seeds.val) 1)
          (Spec.block Spec.sha2_192s (bytes seeds.val) 2) := by
  obtain ⟨⟨sk', pk'⟩, h, hp⟩ := spec_imp_exists (sha2_192s.keygen_spec seeds sk pk)
  exact ⟨sk', pk', h, hp⟩

/-- Keys from `sets.sha2_192s.keygen` are well formed, and `sets.sha2_192s.public_key` of the
private key is the public key it wrote. -/
theorem api_keygen_keyOk (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize) (pk0 : Array U8 48#usize)
    (sk : Array U8 96#usize) (pk : Array U8 48#usize) (h : sets.sha2_192s.keygen seeds sk0 pk0 = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_192s (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_192s (bytes sk.val) ∧ sets.sha2_192s.public_key sk = ok pk := by
  obtain ⟨sk', pk', h', e⟩ := api_keygen_correct seeds sk0 pk0
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_192s Spec.sha2_192s_valid _ _ _ (blockSeed_length seeds 0 (by omega)) (blockSeed_length seeds 1 (by omega))
    (blockSeed_length seeds 2 (by omega))
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
theorem api_verify_correct (m sig ctx : Slice U8) (pk : Array U8 48#usize) (hm : Room m.length 561) :
    sets.sha2_192s.verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_192s (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) :=
  verify_correct m sig ctx pk hm

/-- `api.sign` is FIPS 205 Algorithm 22 (the right-hand side of `sign_correct`). -/
theorem api_sign_correct (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192s.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_192s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  sign_correct m ctx sk addrnd hm

/-- `api.sign_deterministic` is FIPS 205 Algorithm 22, deterministic variant
(`PK.seed` as the randomness); it returns a signature whenever the context
string has at most 255 bytes. -/
theorem api_sign_deterministic_correct (m ctx : Slice U8) (sk : Array U8 96#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192s.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_192s (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_192s (bytes sk.val) 2) ∧
      (ctx.length ≤ 255 → r.isSome) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192s.sign_deterministic_spec m ctx sk hm)
  refine ⟨r, h, hr, fun hc => ?_⟩
  have : ¬ (bytes ctx.val).length > 255 := by simp; scalar_tac
  simp only [Spec.slhSign, this, ↓reduceIte] at hr
  cases r <;> simp_all

/-! ## (D) Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_192s.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_192s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_192s Spec.sha2_192s_valid _ _ _ hk]

theorem complete_internal_checked (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_192s.slh_sign_internal_checked m sk addrnd = ok (some sig) ∧
      sets.sha2_192s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_internal_checked_complete m sk addrnd hm hk
  exact ⟨sig, h, sign_internal_checked_verifies m sk addrnd pk sig hm hpk h⟩

theorem complete (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192s.slh_sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_192s.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_192s Spec.sha2_192s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

theorem complete_checked (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192s.slh_sign_checked m ctx sk addrnd = ok (some sig) ∧
      sets.sha2_192s.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, sign_checked_verifies m ctx sk addrnd pk sig hm hpk h⟩

/-- With keys from `sets.sha2_192s.keygen`, the plain hedged signer's signatures verify. -/
theorem api_complete_sign (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize) (pk0 : Array U8 48#usize)
    (sk : Array U8 96#usize) (pk : Array U8 48#usize) (hkg : sets.sha2_192s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192s.sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_192s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := api_sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_192s Spec.sha2_192s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_192s.keygen`, the plain deterministic signer's signatures verify. -/
theorem api_complete_sign_deterministic (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize)
    (pk0 : Array U8 48#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize)
    (hkg : sets.sha2_192s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192s.sign_deterministic m ctx sk = ok (some sig) ∧ sets.sha2_192s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr, -⟩ := api_sign_deterministic_correct m ctx sk hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_192s Spec.sha2_192s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_192s (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_192s.keygen`, the checked hedged signer always returns a
signature, and it verifies. -/
theorem api_complete_sign_checked (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize)
    (pk0 : Array U8 48#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize)
    (hkg : sets.sha2_192s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192s.sign_checked m ctx sk addrnd = ok (some sig) ∧ sets.sha2_192s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, api_sign_checked_verifies m ctx sk addrnd pk sig hm h hpub⟩

/-- With keys from `sets.sha2_192s.keygen`, the checked deterministic signer always
returns a signature, and it verifies. -/
theorem api_complete_sign_deterministic_checked (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize)
    (pk0 : Array U8 48#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize)
    (hkg : sets.sha2_192s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192s.sign_deterministic_checked m ctx sk = ok (some sig) ∧ sets.sha2_192s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_deterministic_checked_complete m ctx sk hm hc hk
  exact ⟨sig, h, api_sign_deterministic_checked_verifies m ctx sk pk sig hm h hpub⟩


end sha2_192s

/-! ## SLH-DSA-SHA2-192f -/

namespace sha2_192f

theorem bytes_lengthN (x : Array U8 24#usize) : (bytes x.val).length = Spec.sha2_192f.n := by
  simp [Spec.sha2_192f]

theorem verify_eq (m sig ctx : Slice U8) (pk : Array U8 48#usize) :
    sets.sha2_192f.verify m sig ctx pk = sets.sha2_192f.slh_verify m sig ctx pk := by
  unfold sets.sha2_192f.verify sets.sha2_192f.slh_verify api.verify; rfl

theorem blockSeed_length (seeds : Array U8 72#usize) (i : Nat) (hi : i < 3) :
    (Spec.block Spec.sha2_192f (bytes seeds.val) i).length = Spec.sha2_192f.n := by
  simp [Spec.block, Spec.sha2_192f]; omega

/-! ## (A) Exactness -/

/-- The checked signer returns, and what it returns is either nothing or the
signature of FIPS 205 Algorithm 19. -/
theorem sign_internal_checked_correct (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 304) :
    ∃ r, sets.sha2_192f.slh_sign_internal_checked m sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        bytes sig.val = Spec.slhSignInternal Spec.sha2_192f (bytes m.val) (bytes sk.val) (bytes addrnd.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192f.slh_sign_internal_checked_spec m sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignInternalChecked_sound Spec.sha2_192f Spec.sha2_192f_valid _ _ _ _ hr.symm).1

/-- The checked signer with a context string: nothing, or the signature of
FIPS 205 Algorithm 22. -/
theorem sign_checked_correct (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192f.slh_sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_192f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192f.slh_sign_checked_spec m ctx sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_192f Spec.sha2_192f_valid _ _ _ _ _ hr.symm).1

theorem api_sign_checked_correct (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192f.sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_192f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) :=
  sign_checked_correct m ctx sk addrnd hm

/-- The deterministic checked signer: nothing, or the signature of FIPS 205
Algorithm 22 with `PK.seed` as the randomness (the deterministic variant). -/
theorem api_sign_deterministic_checked_correct (m ctx : Slice U8) (sk : Array U8 96#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192f.sign_deterministic_checked m ctx sk = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_192f (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_192f (bytes sk.val) 2) =
          some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192f.sign_deterministic_checked_spec m ctx sk hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_192f Spec.sha2_192f_valid _ _ _ _ _ hr.symm).1

/-! ## (B) Released signatures verify, for every private key -/

/-- At the level of the specification. -/
theorem spec_sign_internal_checked_verifies (msg sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignInternalChecked Spec.sha2_192f msg sk addrnd = some sig) :
    Spec.slhVerifyInternal Spec.sha2_192f msg sig (Spec.skPk Spec.sha2_192f sk) = true :=
  (Spec.slhSignInternalChecked_sound Spec.sha2_192f Spec.sha2_192f_valid msg sk addrnd sig h).2

theorem spec_sign_checked_verifies (msg ctx sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignChecked Spec.sha2_192f msg ctx sk addrnd = some sig) :
    Spec.slhVerify Spec.sha2_192f msg sig ctx (Spec.skPk Spec.sha2_192f sk) = true :=
  (Spec.slhSignChecked_sound Spec.sha2_192f Spec.sha2_192f_valid msg ctx sk addrnd sig h).2

theorem sign_internal_checked_verifies (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (pk : Array U8 48#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 304) (hpk : bytes pk.val = Spec.skPk Spec.sha2_192f (bytes sk.val))
    (h : sets.sha2_192f.slh_sign_internal_checked m sk addrnd = ok (some sig)) :
    sets.sha2_192f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_192f.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hpk,
    spec_sign_internal_checked_verifies _ _ _ _ hp.symm]

theorem sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (pk : Array U8 48#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 561) (hpk : bytes pk.val = Spec.skPk Spec.sha2_192f (bytes sk.val))
    (h : sets.sha2_192f.slh_sign_checked m ctx sk addrnd = ok (some sig)) :
    sets.sha2_192f.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_192f.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_correct _ _ _ _ hm, vec_deref_val, hpk, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

theorem api_public_key_correct (sk : Array U8 96#usize) :
    ∃ pk, sets.sha2_192f.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_192f (bytes sk.val) :=
  spec_imp_exists (sha2_192f.public_key_spec sk)

/-- A signature released by `sets.sha2_192f.sign_checked` verifies under
`sets.sha2_192f.public_key sk`, for every `sk`. -/
theorem api_sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (pk : Array U8 48#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 561)
    (h : sets.sha2_192f.sign_checked m ctx sk addrnd = ok (some sig)) (hpk : sets.sha2_192f.public_key sk = ok pk) :
    sets.sha2_192f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  exact sign_checked_verifies m ctx sk addrnd pk sig hm h2 h

theorem api_sign_deterministic_checked_verifies (m ctx : Slice U8) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 561)
    (h : sets.sha2_192f.sign_deterministic_checked m ctx sk = ok (some sig)) (hpk : sets.sha2_192f.public_key sk = ok pk) :
    sets.sha2_192f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_192f.sign_deterministic_checked_spec m ctx sk hm)
  obtain rfl := ok_inj h hr
  rw [verify_eq, verify_correct _ _ _ _ hm, vec_deref_val, h2, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

/-! ## (C) No false alarms for well-formed keys -/

/-- Keys from key generation are well formed, and the public key returned is
the one the private key holds. -/
theorem keygen_keyOk (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (h : sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_192f (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_192f (bytes sk.val) := by
  obtain ⟨sk', pk', h', e⟩ := keygen_correct sk_seed sk_prf pk_seed
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_192f Spec.sha2_192f_valid _ _ _ (bytes_lengthN sk_seed) (bytes_lengthN sk_prf) (bytes_lengthN pk_seed)
  rw [← e] at this
  exact this

theorem sign_internal_checked_complete (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 304) (hk : Spec.KeyOk Spec.sha2_192f (bytes sk.val)) :
    ∃ sig, sets.sha2_192f.slh_sign_internal_checked m sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192f.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignInternalChecked_complete Spec.sha2_192f Spec.sha2_192f_valid (bytes m.val) (bytes sk.val) (bytes addrnd.val) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem sign_checked_complete (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_192f (bytes sk.val)) :
    ∃ sig, sets.sha2_192f.slh_sign_checked m ctx sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192f.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_192f Spec.sha2_192f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (bytes addrnd.val) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem api_sign_checked_complete (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_192f (bytes sk.val)) :
    ∃ sig, sets.sha2_192f.sign_checked m ctx sk addrnd = ok (some sig) :=
  sign_checked_complete m ctx sk addrnd hm hc hk

theorem api_sign_deterministic_checked_complete (m ctx : Slice U8) (sk : Array U8 96#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_192f (bytes sk.val)) :
    ∃ sig, sets.sha2_192f.sign_deterministic_checked m ctx sk = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192f.sign_deterministic_checked_spec m ctx sk hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_192f Spec.sha2_192f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_192f (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

/-! ## (E) The rest of `api` -/

/-- `sets.sha2_192f.keygen` writes the keys of FIPS 205 Algorithm 18 for the three
24-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of `seeds`. -/
theorem api_keygen_correct (seeds : Array U8 72#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize) :
    ∃ sk' pk', sets.sha2_192f.keygen seeds sk pk = ok (sk', pk') ∧
      (bytes sk'.val, bytes pk'.val) =
        Spec.slhKeygenInternal Spec.sha2_192f (Spec.block Spec.sha2_192f (bytes seeds.val) 0) (Spec.block Spec.sha2_192f (bytes seeds.val) 1)
          (Spec.block Spec.sha2_192f (bytes seeds.val) 2) := by
  obtain ⟨⟨sk', pk'⟩, h, hp⟩ := spec_imp_exists (sha2_192f.keygen_spec seeds sk pk)
  exact ⟨sk', pk', h, hp⟩

/-- Keys from `sets.sha2_192f.keygen` are well formed, and `sets.sha2_192f.public_key` of the
private key is the public key it wrote. -/
theorem api_keygen_keyOk (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize) (pk0 : Array U8 48#usize)
    (sk : Array U8 96#usize) (pk : Array U8 48#usize) (h : sets.sha2_192f.keygen seeds sk0 pk0 = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_192f (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_192f (bytes sk.val) ∧ sets.sha2_192f.public_key sk = ok pk := by
  obtain ⟨sk', pk', h', e⟩ := api_keygen_correct seeds sk0 pk0
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_192f Spec.sha2_192f_valid _ _ _ (blockSeed_length seeds 0 (by omega)) (blockSeed_length seeds 1 (by omega))
    (blockSeed_length seeds 2 (by omega))
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
theorem api_verify_correct (m sig ctx : Slice U8) (pk : Array U8 48#usize) (hm : Room m.length 561) :
    sets.sha2_192f.verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_192f (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) :=
  verify_correct m sig ctx pk hm

/-- `api.sign` is FIPS 205 Algorithm 22 (the right-hand side of `sign_correct`). -/
theorem api_sign_correct (m ctx : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192f.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_192f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  sign_correct m ctx sk addrnd hm

/-- `api.sign_deterministic` is FIPS 205 Algorithm 22, deterministic variant
(`PK.seed` as the randomness); it returns a signature whenever the context
string has at most 255 bytes. -/
theorem api_sign_deterministic_correct (m ctx : Slice U8) (sk : Array U8 96#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_192f.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_192f (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_192f (bytes sk.val) 2) ∧
      (ctx.length ≤ 255 → r.isSome) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_192f.sign_deterministic_spec m ctx sk hm)
  refine ⟨r, h, hr, fun hc => ?_⟩
  have : ¬ (bytes ctx.val).length > 255 := by simp; scalar_tac
  simp only [Spec.slhSign, this, ↓reduceIte] at hr
  cases r <;> simp_all

/-! ## (D) Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_192f.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_192f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_192f Spec.sha2_192f_valid _ _ _ hk]

theorem complete_internal_checked (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_192f.slh_sign_internal_checked m sk addrnd = ok (some sig) ∧
      sets.sha2_192f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_internal_checked_complete m sk addrnd hm hk
  exact ⟨sig, h, sign_internal_checked_verifies m sk addrnd pk sig hm hpk h⟩

theorem complete (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192f.slh_sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_192f.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_192f Spec.sha2_192f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

theorem complete_checked (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192f.slh_sign_checked m ctx sk addrnd = ok (some sig) ∧
      sets.sha2_192f.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, sign_checked_verifies m ctx sk addrnd pk sig hm hpk h⟩

/-- With keys from `sets.sha2_192f.keygen`, the plain hedged signer's signatures verify. -/
theorem api_complete_sign (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize) (pk0 : Array U8 48#usize)
    (sk : Array U8 96#usize) (pk : Array U8 48#usize) (hkg : sets.sha2_192f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192f.sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_192f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := api_sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_192f Spec.sha2_192f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_192f.keygen`, the plain deterministic signer's signatures verify. -/
theorem api_complete_sign_deterministic (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize)
    (pk0 : Array U8 48#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize)
    (hkg : sets.sha2_192f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192f.sign_deterministic m ctx sk = ok (some sig) ∧ sets.sha2_192f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr, -⟩ := api_sign_deterministic_correct m ctx sk hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_192f Spec.sha2_192f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_192f (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_192f.keygen`, the checked hedged signer always returns a
signature, and it verifies. -/
theorem api_complete_sign_checked (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize)
    (pk0 : Array U8 48#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize)
    (hkg : sets.sha2_192f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192f.sign_checked m ctx sk addrnd = ok (some sig) ∧ sets.sha2_192f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, api_sign_checked_verifies m ctx sk addrnd pk sig hm h hpub⟩

/-- With keys from `sets.sha2_192f.keygen`, the checked deterministic signer always
returns a signature, and it verifies. -/
theorem api_complete_sign_deterministic_checked (seeds : Array U8 72#usize) (sk0 : Array U8 96#usize)
    (pk0 : Array U8 48#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize)
    (hkg : sets.sha2_192f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_192f.sign_deterministic_checked m ctx sk = ok (some sig) ∧ sets.sha2_192f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_deterministic_checked_complete m ctx sk hm hc hk
  exact ⟨sig, h, api_sign_deterministic_checked_verifies m ctx sk pk sig hm h hpub⟩


end sha2_192f

/-! ## SLH-DSA-SHA2-256s -/

namespace sha2_256s

theorem bytes_lengthN (x : Array U8 32#usize) : (bytes x.val).length = Spec.sha2_256s.n := by
  simp [Spec.sha2_256s]

theorem verify_eq (m sig ctx : Slice U8) (pk : Array U8 64#usize) :
    sets.sha2_256s.verify m sig ctx pk = sets.sha2_256s.slh_verify m sig ctx pk := by
  unfold sets.sha2_256s.verify sets.sha2_256s.slh_verify api.verify; rfl

theorem blockSeed_length (seeds : Array U8 96#usize) (i : Nat) (hi : i < 3) :
    (Spec.block Spec.sha2_256s (bytes seeds.val) i).length = Spec.sha2_256s.n := by
  simp [Spec.block, Spec.sha2_256s]; omega

/-! ## (A) Exactness -/

/-- The checked signer returns, and what it returns is either nothing or the
signature of FIPS 205 Algorithm 19. -/
theorem sign_internal_checked_correct (m : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 304) :
    ∃ r, sets.sha2_256s.slh_sign_internal_checked m sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        bytes sig.val = Spec.slhSignInternal Spec.sha2_256s (bytes m.val) (bytes sk.val) (bytes addrnd.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256s.slh_sign_internal_checked_spec m sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignInternalChecked_sound Spec.sha2_256s Spec.sha2_256s_valid _ _ _ _ hr.symm).1

/-- The checked signer with a context string: nothing, or the signature of
FIPS 205 Algorithm 22. -/
theorem sign_checked_correct (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256s.slh_sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_256s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256s.slh_sign_checked_spec m ctx sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_256s Spec.sha2_256s_valid _ _ _ _ _ hr.symm).1

theorem api_sign_checked_correct (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256s.sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_256s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) :=
  sign_checked_correct m ctx sk addrnd hm

/-- The deterministic checked signer: nothing, or the signature of FIPS 205
Algorithm 22 with `PK.seed` as the randomness (the deterministic variant). -/
theorem api_sign_deterministic_checked_correct (m ctx : Slice U8) (sk : Array U8 128#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256s.sign_deterministic_checked m ctx sk = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_256s (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_256s (bytes sk.val) 2) =
          some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256s.sign_deterministic_checked_spec m ctx sk hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_256s Spec.sha2_256s_valid _ _ _ _ _ hr.symm).1

/-! ## (B) Released signatures verify, for every private key -/

/-- At the level of the specification. -/
theorem spec_sign_internal_checked_verifies (msg sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignInternalChecked Spec.sha2_256s msg sk addrnd = some sig) :
    Spec.slhVerifyInternal Spec.sha2_256s msg sig (Spec.skPk Spec.sha2_256s sk) = true :=
  (Spec.slhSignInternalChecked_sound Spec.sha2_256s Spec.sha2_256s_valid msg sk addrnd sig h).2

theorem spec_sign_checked_verifies (msg ctx sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignChecked Spec.sha2_256s msg ctx sk addrnd = some sig) :
    Spec.slhVerify Spec.sha2_256s msg sig ctx (Spec.skPk Spec.sha2_256s sk) = true :=
  (Spec.slhSignChecked_sound Spec.sha2_256s Spec.sha2_256s_valid msg ctx sk addrnd sig h).2

theorem sign_internal_checked_verifies (m : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (pk : Array U8 64#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 304) (hpk : bytes pk.val = Spec.skPk Spec.sha2_256s (bytes sk.val))
    (h : sets.sha2_256s.slh_sign_internal_checked m sk addrnd = ok (some sig)) :
    sets.sha2_256s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_256s.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hpk,
    spec_sign_internal_checked_verifies _ _ _ _ hp.symm]

theorem sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (pk : Array U8 64#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 561) (hpk : bytes pk.val = Spec.skPk Spec.sha2_256s (bytes sk.val))
    (h : sets.sha2_256s.slh_sign_checked m ctx sk addrnd = ok (some sig)) :
    sets.sha2_256s.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_256s.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_correct _ _ _ _ hm, vec_deref_val, hpk, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

theorem api_public_key_correct (sk : Array U8 128#usize) :
    ∃ pk, sets.sha2_256s.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_256s (bytes sk.val) :=
  spec_imp_exists (sha2_256s.public_key_spec sk)

/-- A signature released by `sets.sha2_256s.sign_checked` verifies under
`sets.sha2_256s.public_key sk`, for every `sk`. -/
theorem api_sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (pk : Array U8 64#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 561)
    (h : sets.sha2_256s.sign_checked m ctx sk addrnd = ok (some sig)) (hpk : sets.sha2_256s.public_key sk = ok pk) :
    sets.sha2_256s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  exact sign_checked_verifies m ctx sk addrnd pk sig hm h2 h

theorem api_sign_deterministic_checked_verifies (m ctx : Slice U8) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 561)
    (h : sets.sha2_256s.sign_deterministic_checked m ctx sk = ok (some sig)) (hpk : sets.sha2_256s.public_key sk = ok pk) :
    sets.sha2_256s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_256s.sign_deterministic_checked_spec m ctx sk hm)
  obtain rfl := ok_inj h hr
  rw [verify_eq, verify_correct _ _ _ _ hm, vec_deref_val, h2, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

/-! ## (C) No false alarms for well-formed keys -/

/-- Keys from key generation are well formed, and the public key returned is
the one the private key holds. -/
theorem keygen_keyOk (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (h : sets.sha2_256s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_256s (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_256s (bytes sk.val) := by
  obtain ⟨sk', pk', h', e⟩ := keygen_correct sk_seed sk_prf pk_seed
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_256s Spec.sha2_256s_valid _ _ _ (bytes_lengthN sk_seed) (bytes_lengthN sk_prf) (bytes_lengthN pk_seed)
  rw [← e] at this
  exact this

theorem sign_internal_checked_complete (m : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 304) (hk : Spec.KeyOk Spec.sha2_256s (bytes sk.val)) :
    ∃ sig, sets.sha2_256s.slh_sign_internal_checked m sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256s.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignInternalChecked_complete Spec.sha2_256s Spec.sha2_256s_valid (bytes m.val) (bytes sk.val) (bytes addrnd.val) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem sign_checked_complete (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_256s (bytes sk.val)) :
    ∃ sig, sets.sha2_256s.slh_sign_checked m ctx sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256s.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_256s Spec.sha2_256s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (bytes addrnd.val) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem api_sign_checked_complete (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_256s (bytes sk.val)) :
    ∃ sig, sets.sha2_256s.sign_checked m ctx sk addrnd = ok (some sig) :=
  sign_checked_complete m ctx sk addrnd hm hc hk

theorem api_sign_deterministic_checked_complete (m ctx : Slice U8) (sk : Array U8 128#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_256s (bytes sk.val)) :
    ∃ sig, sets.sha2_256s.sign_deterministic_checked m ctx sk = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256s.sign_deterministic_checked_spec m ctx sk hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_256s Spec.sha2_256s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_256s (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

/-! ## (E) The rest of `api` -/

/-- `sets.sha2_256s.keygen` writes the keys of FIPS 205 Algorithm 18 for the three
32-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of `seeds`. -/
theorem api_keygen_correct (seeds : Array U8 96#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize) :
    ∃ sk' pk', sets.sha2_256s.keygen seeds sk pk = ok (sk', pk') ∧
      (bytes sk'.val, bytes pk'.val) =
        Spec.slhKeygenInternal Spec.sha2_256s (Spec.block Spec.sha2_256s (bytes seeds.val) 0) (Spec.block Spec.sha2_256s (bytes seeds.val) 1)
          (Spec.block Spec.sha2_256s (bytes seeds.val) 2) := by
  obtain ⟨⟨sk', pk'⟩, h, hp⟩ := spec_imp_exists (sha2_256s.keygen_spec seeds sk pk)
  exact ⟨sk', pk', h, hp⟩

/-- Keys from `sets.sha2_256s.keygen` are well formed, and `sets.sha2_256s.public_key` of the
private key is the public key it wrote. -/
theorem api_keygen_keyOk (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize) (pk0 : Array U8 64#usize)
    (sk : Array U8 128#usize) (pk : Array U8 64#usize) (h : sets.sha2_256s.keygen seeds sk0 pk0 = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_256s (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_256s (bytes sk.val) ∧ sets.sha2_256s.public_key sk = ok pk := by
  obtain ⟨sk', pk', h', e⟩ := api_keygen_correct seeds sk0 pk0
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_256s Spec.sha2_256s_valid _ _ _ (blockSeed_length seeds 0 (by omega)) (blockSeed_length seeds 1 (by omega))
    (blockSeed_length seeds 2 (by omega))
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
theorem api_verify_correct (m sig ctx : Slice U8) (pk : Array U8 64#usize) (hm : Room m.length 561) :
    sets.sha2_256s.verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_256s (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) :=
  verify_correct m sig ctx pk hm

/-- `api.sign` is FIPS 205 Algorithm 22 (the right-hand side of `sign_correct`). -/
theorem api_sign_correct (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256s.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_256s (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  sign_correct m ctx sk addrnd hm

/-- `api.sign_deterministic` is FIPS 205 Algorithm 22, deterministic variant
(`PK.seed` as the randomness); it returns a signature whenever the context
string has at most 255 bytes. -/
theorem api_sign_deterministic_correct (m ctx : Slice U8) (sk : Array U8 128#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256s.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_256s (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_256s (bytes sk.val) 2) ∧
      (ctx.length ≤ 255 → r.isSome) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256s.sign_deterministic_spec m ctx sk hm)
  refine ⟨r, h, hr, fun hc => ?_⟩
  have : ¬ (bytes ctx.val).length > 255 := by simp; scalar_tac
  simp only [Spec.slhSign, this, ↓reduceIte] at hr
  cases r <;> simp_all

/-! ## (D) Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_256s.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_256s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_256s Spec.sha2_256s_valid _ _ _ hk]

theorem complete_internal_checked (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_256s.slh_sign_internal_checked m sk addrnd = ok (some sig) ∧
      sets.sha2_256s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_internal_checked_complete m sk addrnd hm hk
  exact ⟨sig, h, sign_internal_checked_verifies m sk addrnd pk sig hm hpk h⟩

theorem complete (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256s.slh_sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_256s.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_256s Spec.sha2_256s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

theorem complete_checked (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256s.slh_sign_checked m ctx sk addrnd = ok (some sig) ∧
      sets.sha2_256s.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, sign_checked_verifies m ctx sk addrnd pk sig hm hpk h⟩

/-- With keys from `sets.sha2_256s.keygen`, the plain hedged signer's signatures verify. -/
theorem api_complete_sign (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize) (pk0 : Array U8 64#usize)
    (sk : Array U8 128#usize) (pk : Array U8 64#usize) (hkg : sets.sha2_256s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256s.sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_256s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := api_sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_256s Spec.sha2_256s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_256s.keygen`, the plain deterministic signer's signatures verify. -/
theorem api_complete_sign_deterministic (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize)
    (pk0 : Array U8 64#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize)
    (hkg : sets.sha2_256s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256s.sign_deterministic m ctx sk = ok (some sig) ∧ sets.sha2_256s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr, -⟩ := api_sign_deterministic_correct m ctx sk hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_256s Spec.sha2_256s_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_256s (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_256s.keygen`, the checked hedged signer always returns a
signature, and it verifies. -/
theorem api_complete_sign_checked (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize)
    (pk0 : Array U8 64#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize)
    (hkg : sets.sha2_256s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256s.sign_checked m ctx sk addrnd = ok (some sig) ∧ sets.sha2_256s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, api_sign_checked_verifies m ctx sk addrnd pk sig hm h hpub⟩

/-- With keys from `sets.sha2_256s.keygen`, the checked deterministic signer always
returns a signature, and it verifies. -/
theorem api_complete_sign_deterministic_checked (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize)
    (pk0 : Array U8 64#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize)
    (hkg : sets.sha2_256s.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256s.sign_deterministic_checked m ctx sk = ok (some sig) ∧ sets.sha2_256s.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_deterministic_checked_complete m ctx sk hm hc hk
  exact ⟨sig, h, api_sign_deterministic_checked_verifies m ctx sk pk sig hm h hpub⟩


end sha2_256s

/-! ## SLH-DSA-SHA2-256f -/

namespace sha2_256f

theorem bytes_lengthN (x : Array U8 32#usize) : (bytes x.val).length = Spec.sha2_256f.n := by
  simp [Spec.sha2_256f]

theorem verify_eq (m sig ctx : Slice U8) (pk : Array U8 64#usize) :
    sets.sha2_256f.verify m sig ctx pk = sets.sha2_256f.slh_verify m sig ctx pk := by
  unfold sets.sha2_256f.verify sets.sha2_256f.slh_verify api.verify; rfl

theorem blockSeed_length (seeds : Array U8 96#usize) (i : Nat) (hi : i < 3) :
    (Spec.block Spec.sha2_256f (bytes seeds.val) i).length = Spec.sha2_256f.n := by
  simp [Spec.block, Spec.sha2_256f]; omega

/-! ## (A) Exactness -/

/-- The checked signer returns, and what it returns is either nothing or the
signature of FIPS 205 Algorithm 19. -/
theorem sign_internal_checked_correct (m : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 304) :
    ∃ r, sets.sha2_256f.slh_sign_internal_checked m sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        bytes sig.val = Spec.slhSignInternal Spec.sha2_256f (bytes m.val) (bytes sk.val) (bytes addrnd.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256f.slh_sign_internal_checked_spec m sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignInternalChecked_sound Spec.sha2_256f Spec.sha2_256f_valid _ _ _ _ hr.symm).1

/-- The checked signer with a context string: nothing, or the signature of
FIPS 205 Algorithm 22. -/
theorem sign_checked_correct (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256f.slh_sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_256f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256f.slh_sign_checked_spec m ctx sk addrnd hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_256f Spec.sha2_256f_valid _ _ _ _ _ hr.symm).1

theorem api_sign_checked_correct (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256f.sign_checked m ctx sk addrnd = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_256f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) = some (bytes sig.val) :=
  sign_checked_correct m ctx sk addrnd hm

/-- The deterministic checked signer: nothing, or the signature of FIPS 205
Algorithm 22 with `PK.seed` as the randomness (the deterministic variant). -/
theorem api_sign_deterministic_checked_correct (m ctx : Slice U8) (sk : Array U8 128#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256f.sign_deterministic_checked m ctx sk = ok r ∧
      ∀ sig, r = some sig →
        Spec.slhSign Spec.sha2_256f (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_256f (bytes sk.val) 2) =
          some (bytes sig.val) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256f.sign_deterministic_checked_spec m ctx sk hm)
  refine ⟨r, h, fun sig hs => ?_⟩
  subst hs
  exact (Spec.slhSignChecked_sound Spec.sha2_256f Spec.sha2_256f_valid _ _ _ _ _ hr.symm).1

/-! ## (B) Released signatures verify, for every private key -/

/-- At the level of the specification. -/
theorem spec_sign_internal_checked_verifies (msg sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignInternalChecked Spec.sha2_256f msg sk addrnd = some sig) :
    Spec.slhVerifyInternal Spec.sha2_256f msg sig (Spec.skPk Spec.sha2_256f sk) = true :=
  (Spec.slhSignInternalChecked_sound Spec.sha2_256f Spec.sha2_256f_valid msg sk addrnd sig h).2

theorem spec_sign_checked_verifies (msg ctx sk addrnd sig : Spec.Bytes)
    (h : Spec.slhSignChecked Spec.sha2_256f msg ctx sk addrnd = some sig) :
    Spec.slhVerify Spec.sha2_256f msg sig ctx (Spec.skPk Spec.sha2_256f sk) = true :=
  (Spec.slhSignChecked_sound Spec.sha2_256f Spec.sha2_256f_valid msg ctx sk addrnd sig h).2

theorem sign_internal_checked_verifies (m : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (pk : Array U8 64#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 304) (hpk : bytes pk.val = Spec.skPk Spec.sha2_256f (bytes sk.val))
    (h : sets.sha2_256f.slh_sign_internal_checked m sk addrnd = ok (some sig)) :
    sets.sha2_256f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_256f.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hpk,
    spec_sign_internal_checked_verifies _ _ _ _ hp.symm]

theorem sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (pk : Array U8 64#usize) (sig : alloc.vec.Vec U8)
    (hm : Room m.length 561) (hpk : bytes pk.val = Spec.skPk Spec.sha2_256f (bytes sk.val))
    (h : sets.sha2_256f.slh_sign_checked m ctx sk addrnd = ok (some sig)) :
    sets.sha2_256f.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_256f.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain rfl := ok_inj h hr
  rw [verify_correct _ _ _ _ hm, vec_deref_val, hpk, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

theorem api_public_key_correct (sk : Array U8 128#usize) :
    ∃ pk, sets.sha2_256f.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_256f (bytes sk.val) :=
  spec_imp_exists (sha2_256f.public_key_spec sk)

/-- A signature released by `sets.sha2_256f.sign_checked` verifies under
`sets.sha2_256f.public_key sk`, for every `sk`. -/
theorem api_sign_checked_verifies (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (pk : Array U8 64#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 561)
    (h : sets.sha2_256f.sign_checked m ctx sk addrnd = ok (some sig)) (hpk : sets.sha2_256f.public_key sk = ok pk) :
    sets.sha2_256f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  exact sign_checked_verifies m ctx sk addrnd pk sig hm h2 h

theorem api_sign_deterministic_checked_verifies (m ctx : Slice U8) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (sig : alloc.vec.Vec U8) (hm : Room m.length 561)
    (h : sets.sha2_256f.sign_deterministic_checked m ctx sk = ok (some sig)) (hpk : sets.sha2_256f.public_key sk = ok pk) :
    sets.sha2_256f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨pk', h1, h2⟩ := api_public_key_correct sk
  obtain rfl := ok_inj hpk h1
  obtain ⟨r, hr, hp⟩ := spec_imp_exists (sha2_256f.sign_deterministic_checked_spec m ctx sk hm)
  obtain rfl := ok_inj h hr
  rw [verify_eq, verify_correct _ _ _ _ hm, vec_deref_val, h2, spec_sign_checked_verifies _ _ _ _ _ hp.symm]

/-! ## (C) No false alarms for well-formed keys -/

/-- Keys from key generation are well formed, and the public key returned is
the one the private key holds. -/
theorem keygen_keyOk (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (h : sets.sha2_256f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_256f (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_256f (bytes sk.val) := by
  obtain ⟨sk', pk', h', e⟩ := keygen_correct sk_seed sk_prf pk_seed
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_256f Spec.sha2_256f_valid _ _ _ (bytes_lengthN sk_seed) (bytes_lengthN sk_prf) (bytes_lengthN pk_seed)
  rw [← e] at this
  exact this

theorem sign_internal_checked_complete (m : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 304) (hk : Spec.KeyOk Spec.sha2_256f (bytes sk.val)) :
    ∃ sig, sets.sha2_256f.slh_sign_internal_checked m sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256f.slh_sign_internal_checked_spec m sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignInternalChecked_complete Spec.sha2_256f Spec.sha2_256f_valid (bytes m.val) (bytes sk.val) (bytes addrnd.val) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem sign_checked_complete (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_256f (bytes sk.val)) :
    ∃ sig, sets.sha2_256f.slh_sign_checked m ctx sk addrnd = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256f.slh_sign_checked_spec m ctx sk addrnd hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_256f Spec.sha2_256f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (bytes addrnd.val) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

theorem api_sign_checked_complete (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_256f (bytes sk.val)) :
    ∃ sig, sets.sha2_256f.sign_checked m ctx sk addrnd = ok (some sig) :=
  sign_checked_complete m ctx sk addrnd hm hc hk

theorem api_sign_deterministic_checked_complete (m ctx : Slice U8) (sk : Array U8 128#usize)
    (hm : Room m.length 561) (hc : ctx.length ≤ 255) (hk : Spec.KeyOk Spec.sha2_256f (bytes sk.val)) :
    ∃ sig, sets.sha2_256f.sign_deterministic_checked m ctx sk = ok (some sig) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256f.sign_deterministic_checked_spec m ctx sk hm)
  obtain ⟨s, hs⟩ := Spec.slhSignChecked_complete Spec.sha2_256f Spec.sha2_256f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_256f (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig => exact ⟨sig, h⟩

/-! ## (E) The rest of `api` -/

/-- `sets.sha2_256f.keygen` writes the keys of FIPS 205 Algorithm 18 for the three
32-byte blocks `SK.seed ‖ SK.prf ‖ PK.seed` of `seeds`. -/
theorem api_keygen_correct (seeds : Array U8 96#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize) :
    ∃ sk' pk', sets.sha2_256f.keygen seeds sk pk = ok (sk', pk') ∧
      (bytes sk'.val, bytes pk'.val) =
        Spec.slhKeygenInternal Spec.sha2_256f (Spec.block Spec.sha2_256f (bytes seeds.val) 0) (Spec.block Spec.sha2_256f (bytes seeds.val) 1)
          (Spec.block Spec.sha2_256f (bytes seeds.val) 2) := by
  obtain ⟨⟨sk', pk'⟩, h, hp⟩ := spec_imp_exists (sha2_256f.keygen_spec seeds sk pk)
  exact ⟨sk', pk', h, hp⟩

/-- Keys from `sets.sha2_256f.keygen` are well formed, and `sets.sha2_256f.public_key` of the
private key is the public key it wrote. -/
theorem api_keygen_keyOk (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize) (pk0 : Array U8 64#usize)
    (sk : Array U8 128#usize) (pk : Array U8 64#usize) (h : sets.sha2_256f.keygen seeds sk0 pk0 = ok (sk, pk)) :
    Spec.KeyOk Spec.sha2_256f (bytes sk.val) ∧ bytes pk.val = Spec.skPk Spec.sha2_256f (bytes sk.val) ∧ sets.sha2_256f.public_key sk = ok pk := by
  obtain ⟨sk', pk', h', e⟩ := api_keygen_correct seeds sk0 pk0
  obtain ⟨rfl, rfl⟩ : sk' = sk ∧ pk' = pk := by simpa using ok_inj h' h
  have := Spec.keygen_keyOk Spec.sha2_256f Spec.sha2_256f_valid _ _ _ (blockSeed_length seeds 0 (by omega)) (blockSeed_length seeds 1 (by omega))
    (blockSeed_length seeds 2 (by omega))
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
theorem api_verify_correct (m sig ctx : Slice U8) (pk : Array U8 64#usize) (hm : Room m.length 561) :
    sets.sha2_256f.verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_256f (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val)) :=
  verify_correct m sig ctx pk hm

/-- `api.sign` is FIPS 205 Algorithm 22 (the right-hand side of `sign_correct`). -/
theorem api_sign_correct (m ctx : Slice U8) (sk : Array U8 128#usize) (addrnd : Array U8 32#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256f.sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_256f (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val) :=
  sign_correct m ctx sk addrnd hm

/-- `api.sign_deterministic` is FIPS 205 Algorithm 22, deterministic variant
(`PK.seed` as the randomness); it returns a signature whenever the context
string has at most 255 bytes. -/
theorem api_sign_deterministic_correct (m ctx : Slice U8) (sk : Array U8 128#usize)
    (hm : Room m.length 561) :
    ∃ r, sets.sha2_256f.sign_deterministic m ctx sk = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_256f (bytes m.val) (bytes ctx.val) (bytes sk.val) (Spec.block Spec.sha2_256f (bytes sk.val) 2) ∧
      (ctx.length ≤ 255 → r.isSome) := by
  obtain ⟨r, h, hr⟩ := spec_imp_exists (sha2_256f.sign_deterministic_spec m ctx sk hm)
  refine ⟨r, h, hr, fun hc => ?_⟩
  have : ¬ (bytes ctx.val).length > 255 := by simp; scalar_tac
  simp only [Spec.slhSign, this, ↓reduceIte] at hr
  cases r <;> simp_all

/-! ## (D) Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_256f.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_256f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_256f Spec.sha2_256f_valid _ _ _ hk]

theorem complete_internal_checked (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_256f.slh_sign_internal_checked m sk addrnd = ok (some sig) ∧
      sets.sha2_256f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_internal_checked_complete m sk addrnd hm hk
  exact ⟨sig, h, sign_internal_checked_verifies m sk addrnd pk sig hm hpk h⟩

theorem complete (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256f.slh_sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_256f.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_256f Spec.sha2_256f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

theorem complete_checked (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256f.slh_sign_checked m ctx sk addrnd = ok (some sig) ∧
      sets.sha2_256f.slh_verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, sign_checked_verifies m ctx sk addrnd pk sig hm hpk h⟩

/-- With keys from `sets.sha2_256f.keygen`, the plain hedged signer's signatures verify. -/
theorem api_complete_sign (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize) (pk0 : Array U8 64#usize)
    (sk : Array U8 128#usize) (pk : Array U8 64#usize) (hkg : sets.sha2_256f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256f.sign m ctx sk addrnd = ok (some sig) ∧ sets.sha2_256f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr⟩ := api_sign_correct m ctx sk addrnd hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_256f Spec.sha2_256f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
    (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_256f.keygen`, the plain deterministic signer's signatures verify. -/
theorem api_complete_sign_deterministic (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize)
    (pk0 : Array U8 64#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize)
    (hkg : sets.sha2_256f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256f.sign_deterministic m ctx sk = ok (some sig) ∧ sets.sha2_256f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, hpk, -⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨r, h, hr, -⟩ := api_sign_deterministic_correct m ctx sk hm
  obtain ⟨s, hs, hv⟩ := Spec.slh_complete Spec.sha2_256f Spec.sha2_256f_valid (bytes m.val) (bytes ctx.val) (bytes sk.val)
    (Spec.block Spec.sha2_256f (bytes sk.val) 2) (by simpa using hc) hk
  rw [hs] at hr
  cases r with
  | none => simp at hr
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at hr
    refine ⟨sig, h, ?_⟩
    rw [api_verify_correct _ _ _ _ hm, vec_deref_val, hr, hpk, hv]

/-- With keys from `sets.sha2_256f.keygen`, the checked hedged signer always returns a
signature, and it verifies. -/
theorem api_complete_sign_checked (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize)
    (pk0 : Array U8 64#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize)
    (hkg : sets.sha2_256f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256f.sign_checked m ctx sk addrnd = ok (some sig) ∧ sets.sha2_256f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_checked_complete m ctx sk addrnd hm hc hk
  exact ⟨sig, h, api_sign_checked_verifies m ctx sk addrnd pk sig hm h hpub⟩

/-- With keys from `sets.sha2_256f.keygen`, the checked deterministic signer always
returns a signature, and it verifies. -/
theorem api_complete_sign_deterministic_checked (seeds : Array U8 96#usize) (sk0 : Array U8 128#usize)
    (pk0 : Array U8 64#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize)
    (hkg : sets.sha2_256f.keygen seeds sk0 pk0 = ok (sk, pk))
    (m ctx : Slice U8) (hm : Room m.length 561) (hc : ctx.length ≤ 255) :
    ∃ sig, sets.sha2_256f.sign_deterministic_checked m ctx sk = ok (some sig) ∧ sets.sha2_256f.verify m sig.deref ctx pk = ok true := by
  obtain ⟨hk, -, hpub⟩ := api_keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h⟩ := api_sign_deterministic_checked_complete m ctx sk hm hc hk
  exact ⟨sig, h, api_sign_deterministic_checked_verifies m ctx sk pk sig hm h hpub⟩


end sha2_256f

end slhdsa

#print axioms slhdsa.sha2_128s.sign_internal_checked_correct
#print axioms slhdsa.sha2_128s.sign_checked_correct
#print axioms slhdsa.sha2_128s.api_sign_checked_correct
#print axioms slhdsa.sha2_128s.api_sign_deterministic_checked_correct
#print axioms slhdsa.sha2_128s.spec_sign_internal_checked_verifies
#print axioms slhdsa.sha2_128s.spec_sign_checked_verifies
#print axioms slhdsa.sha2_128s.sign_internal_checked_verifies
#print axioms slhdsa.sha2_128s.sign_checked_verifies
#print axioms slhdsa.sha2_128s.api_public_key_correct
#print axioms slhdsa.sha2_128s.api_sign_checked_verifies
#print axioms slhdsa.sha2_128s.api_sign_deterministic_checked_verifies
#print axioms slhdsa.sha2_128s.keygen_keyOk
#print axioms slhdsa.sha2_128s.sign_internal_checked_complete
#print axioms slhdsa.sha2_128s.sign_checked_complete
#print axioms slhdsa.sha2_128s.api_sign_checked_complete
#print axioms slhdsa.sha2_128s.api_sign_deterministic_checked_complete
#print axioms slhdsa.sha2_128s.api_keygen_correct
#print axioms slhdsa.sha2_128s.api_keygen_keyOk
#print axioms slhdsa.sha2_128s.api_verify_correct
#print axioms slhdsa.sha2_128s.api_sign_correct
#print axioms slhdsa.sha2_128s.api_sign_deterministic_correct
#print axioms slhdsa.sha2_128s.complete_internal
#print axioms slhdsa.sha2_128s.complete_internal_checked
#print axioms slhdsa.sha2_128s.complete
#print axioms slhdsa.sha2_128s.complete_checked
#print axioms slhdsa.sha2_128s.api_complete_sign
#print axioms slhdsa.sha2_128s.api_complete_sign_deterministic
#print axioms slhdsa.sha2_128s.api_complete_sign_checked
#print axioms slhdsa.sha2_128s.api_complete_sign_deterministic_checked
#print axioms slhdsa.sha2_128f.sign_internal_checked_correct
#print axioms slhdsa.sha2_128f.sign_checked_correct
#print axioms slhdsa.sha2_128f.api_sign_checked_correct
#print axioms slhdsa.sha2_128f.api_sign_deterministic_checked_correct
#print axioms slhdsa.sha2_128f.spec_sign_internal_checked_verifies
#print axioms slhdsa.sha2_128f.spec_sign_checked_verifies
#print axioms slhdsa.sha2_128f.sign_internal_checked_verifies
#print axioms slhdsa.sha2_128f.sign_checked_verifies
#print axioms slhdsa.sha2_128f.api_public_key_correct
#print axioms slhdsa.sha2_128f.api_sign_checked_verifies
#print axioms slhdsa.sha2_128f.api_sign_deterministic_checked_verifies
#print axioms slhdsa.sha2_128f.keygen_keyOk
#print axioms slhdsa.sha2_128f.sign_internal_checked_complete
#print axioms slhdsa.sha2_128f.sign_checked_complete
#print axioms slhdsa.sha2_128f.api_sign_checked_complete
#print axioms slhdsa.sha2_128f.api_sign_deterministic_checked_complete
#print axioms slhdsa.sha2_128f.api_keygen_correct
#print axioms slhdsa.sha2_128f.api_keygen_keyOk
#print axioms slhdsa.sha2_128f.api_verify_correct
#print axioms slhdsa.sha2_128f.api_sign_correct
#print axioms slhdsa.sha2_128f.api_sign_deterministic_correct
#print axioms slhdsa.sha2_128f.complete_internal
#print axioms slhdsa.sha2_128f.complete_internal_checked
#print axioms slhdsa.sha2_128f.complete
#print axioms slhdsa.sha2_128f.complete_checked
#print axioms slhdsa.sha2_128f.api_complete_sign
#print axioms slhdsa.sha2_128f.api_complete_sign_deterministic
#print axioms slhdsa.sha2_128f.api_complete_sign_checked
#print axioms slhdsa.sha2_128f.api_complete_sign_deterministic_checked
#print axioms slhdsa.sha2_192s.sign_internal_checked_correct
#print axioms slhdsa.sha2_192s.sign_checked_correct
#print axioms slhdsa.sha2_192s.api_sign_checked_correct
#print axioms slhdsa.sha2_192s.api_sign_deterministic_checked_correct
#print axioms slhdsa.sha2_192s.spec_sign_internal_checked_verifies
#print axioms slhdsa.sha2_192s.spec_sign_checked_verifies
#print axioms slhdsa.sha2_192s.sign_internal_checked_verifies
#print axioms slhdsa.sha2_192s.sign_checked_verifies
#print axioms slhdsa.sha2_192s.api_public_key_correct
#print axioms slhdsa.sha2_192s.api_sign_checked_verifies
#print axioms slhdsa.sha2_192s.api_sign_deterministic_checked_verifies
#print axioms slhdsa.sha2_192s.keygen_keyOk
#print axioms slhdsa.sha2_192s.sign_internal_checked_complete
#print axioms slhdsa.sha2_192s.sign_checked_complete
#print axioms slhdsa.sha2_192s.api_sign_checked_complete
#print axioms slhdsa.sha2_192s.api_sign_deterministic_checked_complete
#print axioms slhdsa.sha2_192s.api_keygen_correct
#print axioms slhdsa.sha2_192s.api_keygen_keyOk
#print axioms slhdsa.sha2_192s.api_verify_correct
#print axioms slhdsa.sha2_192s.api_sign_correct
#print axioms slhdsa.sha2_192s.api_sign_deterministic_correct
#print axioms slhdsa.sha2_192s.complete_internal
#print axioms slhdsa.sha2_192s.complete_internal_checked
#print axioms slhdsa.sha2_192s.complete
#print axioms slhdsa.sha2_192s.complete_checked
#print axioms slhdsa.sha2_192s.api_complete_sign
#print axioms slhdsa.sha2_192s.api_complete_sign_deterministic
#print axioms slhdsa.sha2_192s.api_complete_sign_checked
#print axioms slhdsa.sha2_192s.api_complete_sign_deterministic_checked
#print axioms slhdsa.sha2_192f.sign_internal_checked_correct
#print axioms slhdsa.sha2_192f.sign_checked_correct
#print axioms slhdsa.sha2_192f.api_sign_checked_correct
#print axioms slhdsa.sha2_192f.api_sign_deterministic_checked_correct
#print axioms slhdsa.sha2_192f.spec_sign_internal_checked_verifies
#print axioms slhdsa.sha2_192f.spec_sign_checked_verifies
#print axioms slhdsa.sha2_192f.sign_internal_checked_verifies
#print axioms slhdsa.sha2_192f.sign_checked_verifies
#print axioms slhdsa.sha2_192f.api_public_key_correct
#print axioms slhdsa.sha2_192f.api_sign_checked_verifies
#print axioms slhdsa.sha2_192f.api_sign_deterministic_checked_verifies
#print axioms slhdsa.sha2_192f.keygen_keyOk
#print axioms slhdsa.sha2_192f.sign_internal_checked_complete
#print axioms slhdsa.sha2_192f.sign_checked_complete
#print axioms slhdsa.sha2_192f.api_sign_checked_complete
#print axioms slhdsa.sha2_192f.api_sign_deterministic_checked_complete
#print axioms slhdsa.sha2_192f.api_keygen_correct
#print axioms slhdsa.sha2_192f.api_keygen_keyOk
#print axioms slhdsa.sha2_192f.api_verify_correct
#print axioms slhdsa.sha2_192f.api_sign_correct
#print axioms slhdsa.sha2_192f.api_sign_deterministic_correct
#print axioms slhdsa.sha2_192f.complete_internal
#print axioms slhdsa.sha2_192f.complete_internal_checked
#print axioms slhdsa.sha2_192f.complete
#print axioms slhdsa.sha2_192f.complete_checked
#print axioms slhdsa.sha2_192f.api_complete_sign
#print axioms slhdsa.sha2_192f.api_complete_sign_deterministic
#print axioms slhdsa.sha2_192f.api_complete_sign_checked
#print axioms slhdsa.sha2_192f.api_complete_sign_deterministic_checked
#print axioms slhdsa.sha2_256s.sign_internal_checked_correct
#print axioms slhdsa.sha2_256s.sign_checked_correct
#print axioms slhdsa.sha2_256s.api_sign_checked_correct
#print axioms slhdsa.sha2_256s.api_sign_deterministic_checked_correct
#print axioms slhdsa.sha2_256s.spec_sign_internal_checked_verifies
#print axioms slhdsa.sha2_256s.spec_sign_checked_verifies
#print axioms slhdsa.sha2_256s.sign_internal_checked_verifies
#print axioms slhdsa.sha2_256s.sign_checked_verifies
#print axioms slhdsa.sha2_256s.api_public_key_correct
#print axioms slhdsa.sha2_256s.api_sign_checked_verifies
#print axioms slhdsa.sha2_256s.api_sign_deterministic_checked_verifies
#print axioms slhdsa.sha2_256s.keygen_keyOk
#print axioms slhdsa.sha2_256s.sign_internal_checked_complete
#print axioms slhdsa.sha2_256s.sign_checked_complete
#print axioms slhdsa.sha2_256s.api_sign_checked_complete
#print axioms slhdsa.sha2_256s.api_sign_deterministic_checked_complete
#print axioms slhdsa.sha2_256s.api_keygen_correct
#print axioms slhdsa.sha2_256s.api_keygen_keyOk
#print axioms slhdsa.sha2_256s.api_verify_correct
#print axioms slhdsa.sha2_256s.api_sign_correct
#print axioms slhdsa.sha2_256s.api_sign_deterministic_correct
#print axioms slhdsa.sha2_256s.complete_internal
#print axioms slhdsa.sha2_256s.complete_internal_checked
#print axioms slhdsa.sha2_256s.complete
#print axioms slhdsa.sha2_256s.complete_checked
#print axioms slhdsa.sha2_256s.api_complete_sign
#print axioms slhdsa.sha2_256s.api_complete_sign_deterministic
#print axioms slhdsa.sha2_256s.api_complete_sign_checked
#print axioms slhdsa.sha2_256s.api_complete_sign_deterministic_checked
#print axioms slhdsa.sha2_256f.sign_internal_checked_correct
#print axioms slhdsa.sha2_256f.sign_checked_correct
#print axioms slhdsa.sha2_256f.api_sign_checked_correct
#print axioms slhdsa.sha2_256f.api_sign_deterministic_checked_correct
#print axioms slhdsa.sha2_256f.spec_sign_internal_checked_verifies
#print axioms slhdsa.sha2_256f.spec_sign_checked_verifies
#print axioms slhdsa.sha2_256f.sign_internal_checked_verifies
#print axioms slhdsa.sha2_256f.sign_checked_verifies
#print axioms slhdsa.sha2_256f.api_public_key_correct
#print axioms slhdsa.sha2_256f.api_sign_checked_verifies
#print axioms slhdsa.sha2_256f.api_sign_deterministic_checked_verifies
#print axioms slhdsa.sha2_256f.keygen_keyOk
#print axioms slhdsa.sha2_256f.sign_internal_checked_complete
#print axioms slhdsa.sha2_256f.sign_checked_complete
#print axioms slhdsa.sha2_256f.api_sign_checked_complete
#print axioms slhdsa.sha2_256f.api_sign_deterministic_checked_complete
#print axioms slhdsa.sha2_256f.api_keygen_correct
#print axioms slhdsa.sha2_256f.api_keygen_keyOk
#print axioms slhdsa.sha2_256f.api_verify_correct
#print axioms slhdsa.sha2_256f.api_sign_correct
#print axioms slhdsa.sha2_256f.api_sign_deterministic_correct
#print axioms slhdsa.sha2_256f.complete_internal
#print axioms slhdsa.sha2_256f.complete_internal_checked
#print axioms slhdsa.sha2_256f.complete
#print axioms slhdsa.sha2_256f.complete_checked
#print axioms slhdsa.sha2_256f.api_complete_sign
#print axioms slhdsa.sha2_256f.api_complete_sign_deterministic
#print axioms slhdsa.sha2_256f.api_complete_sign_checked
#print axioms slhdsa.sha2_256f.api_complete_sign_deterministic_checked

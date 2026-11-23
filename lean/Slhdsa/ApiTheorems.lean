import Slhdsa.Theorems
import Spec.Correctness
open Aeneas Aeneas.Std Result

/-!
# Results about the crate's interface, per parameter set

For each of the six sets, about the per-set functions of `sets.rs` (fixed-size
key types) and FIPS 205 at that set:

* the interface: `keygen` (Algorithm 21 on its three blocks of random bytes;
  the key it writes is well formed, `Spec.KeyOk`: the last block is the root
  that key generation derives from the first and third), `public_key`,
  `verify`, `sign` and `sign_deterministic`;
* completeness: with a key from key generation, the signatures of the internal,
  the pure and the interface signers verify.

`Spec.skPk p sk` is `sk.drop (2n)`, the public key `PK.seed ‖ PK.root` held in
a private key. The hypotheses `Room` are those of `Theorems.lean`. Generated
by a script from the single-set tree's file (the same statements and proofs,
at each set).
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

/-! ## Keys and the interface -/

theorem api_public_key_correct (sk : Array U8 64#usize) :
    ∃ pk, sets.sha2_128s.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_128s (bytes sk.val) :=
  spec_imp_exists (sha2_128s.public_key_spec sk)

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

/-! ## Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, sets.sha2_128s.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_128s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_128s Spec.sha2_128s_valid _ _ _ hk]

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

/-! ## Keys and the interface -/

theorem api_public_key_correct (sk : Array U8 64#usize) :
    ∃ pk, sets.sha2_128f.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_128f (bytes sk.val) :=
  spec_imp_exists (sha2_128f.public_key_spec sk)

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

/-! ## Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 16#usize) (sk : Array U8 64#usize)
    (pk : Array U8 32#usize) (hkg : sets.sha2_128f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, sets.sha2_128f.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_128f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_128f Spec.sha2_128f_valid _ _ _ hk]

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

/-! ## Keys and the interface -/

theorem api_public_key_correct (sk : Array U8 96#usize) :
    ∃ pk, sets.sha2_192s.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_192s (bytes sk.val) :=
  spec_imp_exists (sha2_192s.public_key_spec sk)

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

/-! ## Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_192s.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_192s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_192s Spec.sha2_192s_valid _ _ _ hk]

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

/-! ## Keys and the interface -/

theorem api_public_key_correct (sk : Array U8 96#usize) :
    ∃ pk, sets.sha2_192f.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_192f (bytes sk.val) :=
  spec_imp_exists (sha2_192f.public_key_spec sk)

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

/-! ## Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 24#usize) (sk : Array U8 96#usize)
    (pk : Array U8 48#usize) (hkg : sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 24#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_192f.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_192f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_192f Spec.sha2_192f_valid _ _ _ hk]

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

/-! ## Keys and the interface -/

theorem api_public_key_correct (sk : Array U8 128#usize) :
    ∃ pk, sets.sha2_256s.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_256s (bytes sk.val) :=
  spec_imp_exists (sha2_256s.public_key_spec sk)

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

/-! ## Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_256s.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_256s.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_256s Spec.sha2_256s_valid _ _ _ hk]

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

/-! ## Keys and the interface -/

theorem api_public_key_correct (sk : Array U8 128#usize) :
    ∃ pk, sets.sha2_256f.public_key sk = ok pk ∧ bytes pk.val = Spec.skPk Spec.sha2_256f (bytes sk.val) :=
  spec_imp_exists (sha2_256f.public_key_spec sk)

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

/-! ## Completeness: signatures made with a generated key verify -/

theorem complete_internal (sk_seed sk_prf pk_seed : Array U8 32#usize) (sk : Array U8 128#usize)
    (pk : Array U8 64#usize) (hkg : sets.sha2_256f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk))
    (m : Slice U8) (addrnd : Array U8 32#usize) (hm : Room m.length 304) :
    ∃ sig, sets.sha2_256f.slh_sign_internal m sk addrnd = ok sig ∧ sets.sha2_256f.slh_verify_internal m sig.deref pk = ok true := by
  obtain ⟨hk, hpk⟩ := keygen_keyOk _ _ _ _ _ hkg
  obtain ⟨sig, h, hs⟩ := sign_internal_correct m sk addrnd hm
  refine ⟨sig, h, ?_⟩
  rw [verify_internal_correct _ _ _ hm, vec_deref_val, hs, hpk, Spec.slh_complete_internal Spec.sha2_256f Spec.sha2_256f_valid _ _ _ hk]

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


end sha2_256f

end slhdsa

#print axioms slhdsa.sha2_128s.api_public_key_correct
#print axioms slhdsa.sha2_128s.keygen_keyOk
#print axioms slhdsa.sha2_128s.api_keygen_correct
#print axioms slhdsa.sha2_128s.api_keygen_keyOk
#print axioms slhdsa.sha2_128s.api_verify_correct
#print axioms slhdsa.sha2_128s.api_sign_correct
#print axioms slhdsa.sha2_128s.api_sign_deterministic_correct
#print axioms slhdsa.sha2_128s.complete_internal
#print axioms slhdsa.sha2_128s.complete
#print axioms slhdsa.sha2_128s.api_complete_sign
#print axioms slhdsa.sha2_128s.api_complete_sign_deterministic
#print axioms slhdsa.sha2_128f.api_public_key_correct
#print axioms slhdsa.sha2_128f.keygen_keyOk
#print axioms slhdsa.sha2_128f.api_keygen_correct
#print axioms slhdsa.sha2_128f.api_keygen_keyOk
#print axioms slhdsa.sha2_128f.api_verify_correct
#print axioms slhdsa.sha2_128f.api_sign_correct
#print axioms slhdsa.sha2_128f.api_sign_deterministic_correct
#print axioms slhdsa.sha2_128f.complete_internal
#print axioms slhdsa.sha2_128f.complete
#print axioms slhdsa.sha2_128f.api_complete_sign
#print axioms slhdsa.sha2_128f.api_complete_sign_deterministic
#print axioms slhdsa.sha2_192s.api_public_key_correct
#print axioms slhdsa.sha2_192s.keygen_keyOk
#print axioms slhdsa.sha2_192s.api_keygen_correct
#print axioms slhdsa.sha2_192s.api_keygen_keyOk
#print axioms slhdsa.sha2_192s.api_verify_correct
#print axioms slhdsa.sha2_192s.api_sign_correct
#print axioms slhdsa.sha2_192s.api_sign_deterministic_correct
#print axioms slhdsa.sha2_192s.complete_internal
#print axioms slhdsa.sha2_192s.complete
#print axioms slhdsa.sha2_192s.api_complete_sign
#print axioms slhdsa.sha2_192s.api_complete_sign_deterministic
#print axioms slhdsa.sha2_192f.api_public_key_correct
#print axioms slhdsa.sha2_192f.keygen_keyOk
#print axioms slhdsa.sha2_192f.api_keygen_correct
#print axioms slhdsa.sha2_192f.api_keygen_keyOk
#print axioms slhdsa.sha2_192f.api_verify_correct
#print axioms slhdsa.sha2_192f.api_sign_correct
#print axioms slhdsa.sha2_192f.api_sign_deterministic_correct
#print axioms slhdsa.sha2_192f.complete_internal
#print axioms slhdsa.sha2_192f.complete
#print axioms slhdsa.sha2_192f.api_complete_sign
#print axioms slhdsa.sha2_192f.api_complete_sign_deterministic
#print axioms slhdsa.sha2_256s.api_public_key_correct
#print axioms slhdsa.sha2_256s.keygen_keyOk
#print axioms slhdsa.sha2_256s.api_keygen_correct
#print axioms slhdsa.sha2_256s.api_keygen_keyOk
#print axioms slhdsa.sha2_256s.api_verify_correct
#print axioms slhdsa.sha2_256s.api_sign_correct
#print axioms slhdsa.sha2_256s.api_sign_deterministic_correct
#print axioms slhdsa.sha2_256s.complete_internal
#print axioms slhdsa.sha2_256s.complete
#print axioms slhdsa.sha2_256s.api_complete_sign
#print axioms slhdsa.sha2_256s.api_complete_sign_deterministic
#print axioms slhdsa.sha2_256f.api_public_key_correct
#print axioms slhdsa.sha2_256f.keygen_keyOk
#print axioms slhdsa.sha2_256f.api_keygen_correct
#print axioms slhdsa.sha2_256f.api_keygen_keyOk
#print axioms slhdsa.sha2_256f.api_verify_correct
#print axioms slhdsa.sha2_256f.api_sign_correct
#print axioms slhdsa.sha2_256f.api_sign_deterministic_correct
#print axioms slhdsa.sha2_256f.complete_internal
#print axioms slhdsa.sha2_256f.complete
#print axioms slhdsa.sha2_256f.api_complete_sign
#print axioms slhdsa.sha2_256f.api_complete_sign_deterministic

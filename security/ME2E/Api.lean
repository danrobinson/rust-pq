import ME2E.Basic

/-!
# The interface module `api`, generic part (all six SHA-2 sets)

Set-independent lemmas used by the per-set files `ME2E/Api/Sha2_<set>.lean` (the counterparts of
the single-set `E2E/Api.lean`, git `26aa3d8`) and by the typed forms of the end-to-end statements:

* splitting a `3n`-byte seed string and a `4n`-byte private key into `n`-byte blocks
  (`block_seeds`, `block_sk_pkSeed`, `seeds_split`, `sk_split`; `Spec.block p` at any `p`);
* `optVec_eq`, `map_wire`: optional Rust signature vectors;
* `spec_slhSignChecked_eq`: on a well-formed key (`Spec.KeyOk p`) the checked Algorithm 22 *is*
  Algorithm 22, for every valid `p`; `slhSign_tooLong`;
* typed values: `secretKey S sk`, the `4n`-byte Rust private key read as VCVio's typed key, with
  `skBytes_secretKey`; `keygen_typed`, `signPure_typed`, `verifyPure_typed`: outputs equal to
  `Spec.slhKeygenInternal` / `slhSign` / `slhVerify` at `S.spec` are VCVio's `keygenInternal`,
  `External.signPureWithRandomizer`, `External.verifyPure` on the FIPS encodings
  (`MLink.keygen_eq`, `slhSign_eq`, `slhVerify_eq`).
-/

namespace ME2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security
open slhdsa (bytes Room)
open MLink (Sha2Set cv sp nd)

/-! ### Splitting the seed string and the private key into `n`-byte blocks -/

theorem bytes_append (a b : List U8) : bytes (a ++ b) = bytes a ++ bytes b := by
  simp [bytes]

theorem block_cons0 (p : Spec.Params) (x rest : Spec.Bytes) (hx : x.length = p.n) :
    Spec.block p (x ++ rest) 0 = x := by
  simp [Spec.block, List.take_left' hx]

theorem block_consS (p : Spec.Params) (x rest : Spec.Bytes) (hx : x.length = p.n) (i : Nat) :
    Spec.block p (x ++ rest) (i + 1) = Spec.block p rest i := by
  simp only [Spec.block, Nat.add_mul, Nat.one_mul, Nat.add_comm _ p.n, ← List.drop_drop,
    List.drop_left' hx]

theorem bytesN_length {N : Usize} (p : Spec.Params) (hN : N.val = p.n) (x : Array U8 N) :
    (bytes x.val).length = p.n := by
  rw [bytes_length, x.property, hN]

/-- The three `n`-byte blocks of a string `a ‖ b ‖ c`. -/
theorem block_seeds {N M : Usize} (p : Spec.Params) (hN : N.val = p.n) (seeds : Array U8 M)
    (a b c : Array U8 N) (h : seeds.val = a.val ++ b.val ++ c.val) :
    Spec.block p (bytes seeds.val) 0 = bytes a.val ∧ Spec.block p (bytes seeds.val) 1 = bytes b.val ∧
      Spec.block p (bytes seeds.val) 2 = bytes c.val := by
  have hc : Spec.block p (bytes c.val) 0 = bytes c.val := by
    simpa using block_cons0 p (bytes c.val) [] (bytesN_length p hN c)
  rw [h, List.append_assoc, bytes_append, bytes_append]
  refine ⟨block_cons0 _ _ _ (bytesN_length p hN a), ?_, ?_⟩
  · rw [block_consS _ _ _ (bytesN_length p hN a) 0, block_cons0 _ _ _ (bytesN_length p hN b)]
  · rw [block_consS _ _ _ (bytesN_length p hN a) 1, block_consS _ _ _ (bytesN_length p hN b) 0, hc]

/-- The `PK.seed` block (block 2) of a private key `a ‖ b ‖ c ‖ d` is `c`. -/
theorem block_sk_pkSeed {N M : Usize} (p : Spec.Params) (hN : N.val = p.n) (sk : Array U8 M)
    (a b c d : Array U8 N) (h : sk.val = a.val ++ b.val ++ c.val ++ d.val) :
    Spec.block p (bytes sk.val) 2 = bytes c.val := by
  rw [h, List.append_assoc, List.append_assoc, bytes_append, bytes_append, bytes_append,
    block_consS _ _ _ (bytesN_length p hN a) 1, block_consS _ _ _ (bytesN_length p hN b) 0,
    block_cons0 _ _ _ (bytesN_length p hN c)]

/-- Every `3n`-byte string is `SK.seed ‖ SK.prf ‖ PK.seed` for exactly one triple of `n`-byte
arrays. -/
theorem seeds_split {N M : Usize} (hM : M.val = 3 * N.val) (seeds : Array U8 M) :
    ∃! abc : Array U8 N × Array U8 N × Array U8 N,
      seeds.val = abc.1.val ++ abc.2.1.val ++ abc.2.2.val := by
  have hl : seeds.val.length = 3 * N.val := by rw [seeds.property, hM]
  refine ⟨(Aeneas.Std.Array.from (seeds.val.take N.val) (by simp only [List.length_take, hl]; omega),
    Aeneas.Std.Array.from ((seeds.val.drop N.val).take N.val)
      (by simp only [List.length_take, List.length_drop, hl]; omega),
    Aeneas.Std.Array.from ((seeds.val.drop N.val).drop N.val)
      (by simp only [List.length_drop, hl]; omega)), ?_, ?_⟩
  · simp only [Aeneas.Std.Array.from_val]
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  · rintro ⟨a, b, c⟩ h
    simp only at h
    have ha : a.val.length = N.val := a.property
    have hb : b.val.length = N.val := b.property
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> apply Aeneas.Std.Array.ext <;>
      simp only [Aeneas.Std.Array.from_val, h, List.append_assoc]
    · rw [List.take_left' ha]
    · rw [List.drop_left' ha, List.take_left' hb]
    · rw [List.drop_left' ha, List.drop_left' hb]

/-- Every `4n`-byte private key is `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` for exactly one
quadruple of `n`-byte arrays. -/
theorem sk_split {N M : Usize} (hM : M.val = 4 * N.val) (sk : Array U8 M) :
    ∃! abcd : Array U8 N × Array U8 N × Array U8 N × Array U8 N,
      sk.val = abcd.1.val ++ abcd.2.1.val ++ abcd.2.2.1.val ++ abcd.2.2.2.val := by
  have hl : sk.val.length = 4 * N.val := by rw [sk.property, hM]
  refine ⟨(Aeneas.Std.Array.from (sk.val.take N.val) (by simp only [List.length_take, hl]; omega),
    Aeneas.Std.Array.from ((sk.val.drop N.val).take N.val)
      (by simp only [List.length_take, List.length_drop, hl]; omega),
    Aeneas.Std.Array.from (((sk.val.drop N.val).drop N.val).take N.val)
      (by simp only [List.length_take, List.length_drop, hl]; omega),
    Aeneas.Std.Array.from (((sk.val.drop N.val).drop N.val).drop N.val)
      (by simp only [List.length_drop, hl]; omega)), ?_, ?_⟩
  · simp only [Aeneas.Std.Array.from_val]
    rw [List.append_assoc, List.append_assoc, List.take_append_drop, List.take_append_drop,
      List.take_append_drop]
  · rintro ⟨a, b, c, d⟩ h
    simp only at h
    have ha : a.val.length = N.val := a.property
    have hb : b.val.length = N.val := b.property
    have hc : c.val.length = N.val := c.property
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Aeneas.Std.Array.ext <;>
      simp only [Aeneas.Std.Array.from_val, h, List.append_assoc]
    · rw [List.take_left' ha]
    · rw [List.drop_left' ha, List.take_left' hb]
    · rw [List.drop_left' ha, List.drop_left' hb, List.take_left' hc]
    · rw [List.drop_left' ha, List.drop_left' hb, List.drop_left' hc]

/-! ### Signatures returned by the Rust signers -/

/-- Two optional Rust signature vectors with the same bytes are equal. -/
theorem optVec_eq {r r' : Option (alloc.vec.Vec U8)}
    (h : r.map (fun v => bytes v.val) = r'.map (fun v => bytes v.val)) : r = r' := by
  cases r <;> cases r' <;> simp at h ⊢
  exact alloc.vec.Vec.ext _ _ (slhdsa.ht_bytes_injective h)

theorem map_wire (r : Option (alloc.vec.Vec U8)) :
    r.map (fun v => wire v.val) = (r.map (fun v => bytes v.val)).map cv := by
  cases r <;> rfl

/-! ### The checked signer of the specification on well-formed keys -/

/-- For a valid parameter set and a well-formed key, the checked Algorithm 22 *is* Algorithm 22,
on every message, context and randomness. -/
theorem spec_slhSignChecked_eq (p : Spec.Params) (hv : p.Valid) (msg ctx sk addrnd : Spec.Bytes)
    (hk : Spec.KeyOk p sk) :
    Spec.slhSignChecked p msg ctx sk addrnd = Spec.slhSign p msg ctx sk addrnd := by
  by_cases hc : ctx.length ≤ 255
  · obtain ⟨sig, h⟩ := Spec.slhSignChecked_complete p hv msg ctx sk addrnd hc hk
    rw [h, (Spec.slhSignChecked_sound p hv _ _ _ _ _ h).1]
  · have hc' : ctx.length > 255 := by omega
    simp [Spec.slhSignChecked, Spec.slhSign, hc']

theorem slhSign_tooLong (p : Spec.Params) (msg : Spec.Bytes) (ctx : Slice U8) (sk addrnd : Spec.Bytes)
    (hc : 255 < ctx.length) : Spec.slhSign p msg (bytes ctx.val) sk addrnd = none := by
  have hc' : (bytes ctx.val).length > 255 := by rw [slhdsa.bytes_length]; exact hc
  unfold Spec.slhSign
  rw [ite_eq_left hc']

/-! ### Typed values -/

variable (S : Sha2Set)

/-- A `4n`-byte Rust private-key array read as VCVio's typed secret key
`SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` (FIPS 205 Figure 15) of the set `S`. -/
def secretKey {N : Usize} (sk : Array U8 N) : SecretKeyCore S.prims.core :=
  { skSeed := nodeOfBytes S.vp.params.n ((bytes sk.val).take S.vp.params.n)
    skPrf := nodeOfBytes S.vp.params.n (((bytes sk.val).drop S.vp.params.n).take S.vp.params.n)
    pkSeed := nodeOfBytes S.vp.params.n
      ((((bytes sk.val).drop S.vp.params.n).drop S.vp.params.n).take S.vp.params.n)
    pkRoot := nodeOfBytes S.vp.params.n
      ((((bytes sk.val).drop S.vp.params.n).drop S.vp.params.n).drop S.vp.params.n) }

/-- On a `4n`-byte array, `secretKey S sk` encodes back to exactly the bytes of `sk`. -/
theorem skBytes_secretKey {N : Usize} (hN : N.val = 4 * S.vp.params.n) (sk : Array U8 N) :
    MLink.skBytes S (secretKey S sk) = bytes sk.val := by
  have h : (bytes sk.val).length = 4 * S.vp.params.n := by rw [bytes_length, sk.property, hN]
  show nd (nodeOfBytes _ _) ++ nd (nodeOfBytes _ _) ++ nd (nodeOfBytes _ _) ++
    nd (nodeOfBytes _ _) = _
  rw [nd_nodeOfBytes _ _ (by simp only [List.length_take, h]; omega),
    nd_nodeOfBytes _ _ (by simp only [List.length_take, List.length_drop, h]; omega),
    nd_nodeOfBytes _ _ (by simp only [List.length_take, List.length_drop, h]; omega),
    nd_nodeOfBytes _ _ (by simp only [List.length_drop, h]; omega)]
  generalize bytes sk.val = l
  simp only [List.append_assoc, List.take_append_drop]

/-- **Key generation, typed**: a pair `(sk, pk)` that is `Spec.slhKeygenInternal S.spec` of three
`n`-byte seeds is the FIPS encoding of VCVio's `keygenInternal` at the seeds read as nodes. -/
theorem keygen_typed {N : Usize} (hN : N.val = S.vp.params.n)
    (sk_seed sk_prf pk_seed : Array U8 N) (sk pk : List U8)
    (h : (bytes sk, bytes pk) =
      Spec.slhKeygenInternal S.spec (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val)) :
    bytes sk = MLink.skBytes S (GeneralScheme.keygenInternal S.vp S.prims (node S sk_seed)
        (node S sk_prf) (node S pk_seed)).2 ∧
      bytes pk = MLink.pkBytes S (GeneralScheme.keygenInternal S.vp S.prims (node S sk_seed)
        (node S sk_prf) (node S pk_seed)).1 := by
  rw [← nd_node S sk_seed hN, ← nd_node S sk_prf hN, ← nd_node S pk_seed hN, MLink.keygen_eq] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- **Pure signing, typed**: an optional signature that is `Spec.slhSign S.spec` is the FIPS
encoding of VCVio's `External.signPureWithRandomizer` at `secretKey S sk` (`none` exactly for its
error value). -/
theorem signPure_typed {N N4 : Usize} (hN : N.val = S.vp.params.n) (hN4 : N4.val = 4 * S.vp.params.n)
    (m ctx : List U8) (sk : Array U8 N4) (addrnd : Array U8 N) (r : Option (List U8))
    (h : r.map bytes = Spec.slhSign S.spec (bytes m) (bytes ctx) (bytes sk.val) (bytes addrnd.val)) :
    r.map bytes =
      (External.signPureWithRandomizer S.vp S.prims (cv (bytes m)) (cv (bytes ctx))
        (secretKey S sk) (node S addrnd)).toOption.map (MLink.sigBytes S) := by
  rw [← skBytes_secretKey S hN4 sk, ← nd_node S addrnd hN, MLink.slhSign_eq] at h
  exact h

/-- **Pure verification, typed**: for a `2n`-byte public key, `Spec.slhVerify S.spec` is VCVio's
`External.verifyPure` on the values of VCVio's strict decoders; a signature that does not decode
is rejected. -/
theorem verifyPure_typed (m sig ctx pk : List U8) (hpk : pk.length = 2 * S.spec.n) :
    Spec.slhVerify S.spec (bytes m) (bytes sig) (bytes ctx) (bytes pk) =
      match MLink.decodeSig S (cv (bytes sig)), MLink.decodePk S (cv (bytes pk)) with
      | .ok s, .ok k => External.verifyPure S.vp S.prims (cv (bytes m)) s (cv (bytes ctx)) k
      | _, _ => false :=
  MLink.slhVerify_eq S _ _ _ _ (by simpa using hpk)

end ME2E

#print axioms ME2E.block_seeds
#print axioms ME2E.block_sk_pkSeed
#print axioms ME2E.seeds_split
#print axioms ME2E.sk_split
#print axioms ME2E.optVec_eq
#print axioms ME2E.map_wire
#print axioms ME2E.spec_slhSignChecked_eq
#print axioms ME2E.slhSign_tooLong
#print axioms ME2E.skBytes_secretKey
#print axioms ME2E.keygen_typed
#print axioms ME2E.signPure_typed
#print axioms ME2E.verifyPure_typed

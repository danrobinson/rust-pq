import Facade.EndToEnd

open Aeneas Aeneas.Std Result
open LinkedArm.Signer
namespace slhdsa.Suite
attribute [local irreducible] Spec.slhSign Spec.slhVerify Spec.slhKeygenInternal

/-- Run the public fixed-size APIs on actual array buffers, and read the
    serialized signature from the Vec passed back into verification. -/
def PublicSession {S K V N : Usize} (P : Spec.Params) (slack : Nat)
    (keygen : Array U8 S → Array U8 K → Array U8 V → Result (Array U8 K × Array U8 V))
    (sign : Slice U8 → Slice U8 → Array U8 K → Array U8 N → Result (Option (alloc.vec.Vec U8)))
    (det : Slice U8 → Slice U8 → Array U8 K → Result (Option (alloc.vec.Vec U8)))
    (check : Slice U8 → Slice U8 → Slice U8 → Array U8 V → Result Bool) : Prop :=
  ∀ seeds skBuf pkBuf m ctx random deterministic, Room m.length slack → ctx.length ≤ 255 →
    ∃ sk pk sig, keygen seeds skBuf pkBuf = ok (sk, pk) ∧
      (if deterministic then det m ctx sk else sign m ctx sk random) = ok (some sig) ∧
      check m sig.deref ctx pk = ok true ∧
      Session P (Spec.block P (bytes seeds.val) 0) (Spec.block P (bytes seeds.val) 1)
        (Spec.block P (bytes seeds.val) 2) (bytes m.val) (bytes ctx.val) (bytes random.val)
        deterministic (bytes sk.val) (bytes pk.val) (bytes sig.val) true

private def keygenImpl (family : Spec.HashFamily) :=
  match family with
  | .sha2 => api.keygen
  | .shake => shake.api.keygen

private theorem keygenImpl_spec (family : Spec.HashFamily) {N} (p : params.Params) (hp : PN p N)
    (seeds sk pk : Slice U8) (hseeds : seeds.length = 3*N.val)
    (hsk : sk.length = 4*N.val) (hpk : pk.length = 2*N.val) :
    keygenImpl family N p seeds sk pk ⦃ r =>
      (bytes r.1.val, bytes r.2.val) = Spec.slhKeygenInternal (view family p)
        (Spec.block (view family p) (bytes seeds.val) 0) (Spec.block (view family p) (bytes seeds.val) 1)
        (Spec.block (view family p) (bytes seeds.val) 2) ∧
      r.1.length = 4*N.val ∧ r.2.length = 2*N.val ⦄ := by
  cases family
  · exact api_keygen_spec p hp _ _ _ hseeds hsk hpk
  · exact Shake.api_keygen_spec p hp _ _ _ hseeds hsk hpk

private def fixedKeygen (family : Spec.HashFamily) (N : Usize) (p : params.Params)
    {S K V : Usize} (seeds : Array U8 S) (sk : Array U8 K) (pk : Array U8 V) :=
  Aeneas.Std.bind (keygenImpl family N p seeds.to_slice sk.to_slice pk.to_slice)
    (Aeneas.Std.uncurry fun a b => ok (Array.from_slice sk a, Array.from_slice pk b))

private def plainSign (family : Spec.HashFamily) :=
  match family with
  | .sha2 => @api.sign
  | .shake => @shake.api.sign

private def deterministicSign (family : Spec.HashFamily) :=
  match family with
  | .sha2 => api.sign_deterministic
  | .shake => shake.api.sign_deterministic

private theorem modeSpec (family : Spec.HashFamily) {N} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (random : Array U8 N) (deterministic : Bool)
    (hsk : sk.length = 4*N.val) (room : Room m.length (msgSlack N.val + 257)) :
    (if deterministic then deterministicSign family N p m ctx sk
     else @plainSign family N p m ctx sk random) ⦃ r =>
      r.map (fun v => bytes v.val) = Spec.slhSign (view family p) (bytes m.val) (bytes ctx.val)
        (bytes sk.val) (if deterministic then Spec.block (view family p) (bytes sk.val) 2
                        else bytes random.val) ⦄ := by
  cases family <;> cases deterministic
  · exact api_sign_spec p hp _ _ _ random hsk room
  · exact api_sign_deterministic_spec p hp _ _ _ hsk room
  · exact Shake.api_sign_spec p hp _ _ _ random hsk room
  · exact Shake.api_sign_deterministic_spec p hp _ _ _ hsk room

private theorem fixedSession (family : Spec.HashFamily) {N S K V : Usize} (p : params.Params)
    (hp : PN p N) (std : view family p ∈ parameterSets ∨ view family p ∈ sha2ParameterSets)
    (sizes : S.val = 3*N.val ∧ K.val = 4*N.val ∧ V.val = 2*N.val) :
    PublicSession (view family p) (msgSlack N.val + 257)
      (@fixedKeygen family N p S K V)
      (fun m ctx sk r => @plainSign family N p m ctx sk.to_slice r)
      (fun m ctx sk => deterministicSign family N p m ctx sk.to_slice)
      (fun m s ctx pk => verify family N p m s ctx pk.to_slice) := by
  intro seeds skBuf pkBuf m ctx random deterministic room valid
  let P := view family p
  let block := Spec.block P (bytes seeds.val)
  have hctx : (bytes ctx.val).length ≤ 255 := by simpa using valid
  obtain ⟨⟨s,k⟩, kg, keys, skLen, pkLen⟩ := spec_imp_exists
    (keygenImpl_spec family p hp seeds.to_slice skBuf.to_slice pkBuf.to_slice
      (by simpa using sizes.1) (by simpa using sizes.2.1) (by simpa using sizes.2.2))
  let sk := Array.from_slice skBuf s
  let pk := Array.from_slice pkBuf k
  have sbytes : sk.val = s.val := from_slice_eq _ _ (skLen.trans sizes.2.1.symm)
  have pbytes : pk.val = k.val := from_slice_eq _ _ (pkLen.trans sizes.2.2.symm)
  have key : (bytes sk.val,bytes pk.val) = Spec.slhKeygenInternal P (block 0) (block 1) (block 2) := by
    simpa only [sbytes,pbytes,Array.val_to_slice] using keys
  have hsk : sk.to_slice.length = 4*N.val := by simpa using sizes.2.1
  have hpk : pk.to_slice.length = 2*N.val := by simpa using sizes.2.2
  let rand := if deterministic then Spec.block P (bytes sk.val) 2 else bytes random.val
  obtain ⟨out, run, eq⟩ := spec_imp_exists
    (modeSpec family p hp m ctx sk.to_slice random deterministic hsk room)
  simp only [Array.val_to_slice] at eq
  change out.map (fun v => bytes v.val) =
    Spec.slhSign P (bytes m.val) (bytes ctx.val) (bytes sk.val) rand at eq
  have bn (i : Nat) (hi : i < 3) : (block i).length = P.n := by
    have hn : P.n = N.val := hp.n
    simp [block, Spec.block, hn, sizes.1]
    interval_cases i <;> omega
  have lens := And.intro (bn 0 (by decide)) (And.intro (bn 1 (by decide)) (bn 2 (by decide)))
  have okKey := Spec.keygen_keyOk P (Suite.valid family hp) _ _ _ lens.1 lens.2.1 lens.2.2
  rw [← key] at okKey
  obtain ⟨want, signRef, verifyRef⟩ := Spec.slh_complete P (Suite.valid family hp) (bytes m.val) (bytes ctx.val) (bytes sk.val) rand hctx okKey.1
  rw [signRef] at eq
  cases out with
  | none => simp at eq
  | some sig =>
    simp only [Option.map_some, Option.some.injEq] at eq
    obtain ⟨v, vr, verdict⟩ := spec_imp_exists (api_verify_spec family p hp m sig.deref ctx pk.to_slice hpk room)
    have accepted : Spec.slhVerify P (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val) = true := by
      have hpub : bytes pk.val = Spec.skPk P (bytes sk.val) := okKey.2
      rw [eq,hpub]; exact verifyRef
    have trueVerdict : v = true := (show v = Spec.slhVerify P _ _ _ _ from
      by simpa only [vec_deref_val,Array.val_to_slice] using verdict).trans accepted
    rw [trueVerdict] at vr
    refine ⟨sk,pk,sig,?_,run,vr,(session_iff std lens hctx).mpr ⟨key,?_,accepted.symm,rfl⟩⟩
    · simp only [fixedKeygen,kg,bind_ok]; rfl
    · rw [eq]; exact signRef.symm

/-- Unfold the four concrete exported wrappers and eliminate their infallible
    slice conversions. Each application checks the actual function definitions. -/
local macro "apply_public_entries " h:ident " [" kg:Lean.Parser.Tactic.simpLemma ", " sg:Lean.Parser.Tactic.simpLemma ", " detSign:Lean.Parser.Tactic.simpLemma ", " ver:Lean.Parser.Tactic.simpLemma "]" : tactic =>
  `(tactic| (
    intro seeds sk pk msg ctx random det room valid
    specialize $h seeds sk pk msg ctx random det room valid
    simpa only [$kg, $sg, $detSign, $ver, fixedKeygen, keygenImpl, plainSign,
      deterministicSign, verify, lift, Array.to_slice_mut, bind_ok, uncurry] using $h))

theorem sha2_128s_session : PublicSession Spec.sha2_128s 409
    sets.sha2_128s.keygen sets.sha2_128s.sign sets.sha2_128s.sign_deterministic sets.sha2_128s.verify := by
  have h := @fixedSession .sha2 16#usize 48#usize 64#usize 32#usize _ sha2_128s.pn
    (by right; rw [view_sha2, sha2_128s.hP]; decide) (by decide)
  rw [view_sha2, sha2_128s.hP, sha2_128s.slack] at h
  apply_public_entries h [sets.sha2_128s.keygen, sets.sha2_128s.sign,
    sets.sha2_128s.sign_deterministic, sets.sha2_128s.verify]

theorem sha2_128f_session : PublicSession Spec.sha2_128f 409
    sets.sha2_128f.keygen sets.sha2_128f.sign sets.sha2_128f.sign_deterministic sets.sha2_128f.verify := by
  have h := @fixedSession .sha2 16#usize 48#usize 64#usize 32#usize _ sha2_128f.pn
    (by right; rw [view_sha2, sha2_128f.hP]; decide) (by decide)
  rw [view_sha2, sha2_128f.hP, sha2_128f.slack] at h
  apply_public_entries h [sets.sha2_128f.keygen, sets.sha2_128f.sign,
    sets.sha2_128f.sign_deterministic, sets.sha2_128f.verify]

theorem sha2_192s_session : PublicSession Spec.sha2_192s 561
    sets.sha2_192s.keygen sets.sha2_192s.sign sets.sha2_192s.sign_deterministic sets.sha2_192s.verify := by
  have h := @fixedSession .sha2 24#usize 72#usize 96#usize 48#usize _ sha2_192s.pn
    (by right; rw [view_sha2, sha2_192s.hP]; decide) (by decide)
  rw [view_sha2, sha2_192s.hP, sha2_192s.slack] at h
  apply_public_entries h [sets.sha2_192s.keygen, sets.sha2_192s.sign,
    sets.sha2_192s.sign_deterministic, sets.sha2_192s.verify]

theorem sha2_192f_session : PublicSession Spec.sha2_192f 561
    sets.sha2_192f.keygen sets.sha2_192f.sign sets.sha2_192f.sign_deterministic sets.sha2_192f.verify := by
  have h := @fixedSession .sha2 24#usize 72#usize 96#usize 48#usize _ sha2_192f.pn
    (by right; rw [view_sha2, sha2_192f.hP]; decide) (by decide)
  rw [view_sha2, sha2_192f.hP, sha2_192f.slack] at h
  apply_public_entries h [sets.sha2_192f.keygen, sets.sha2_192f.sign,
    sets.sha2_192f.sign_deterministic, sets.sha2_192f.verify]

theorem sha2_256s_session : PublicSession Spec.sha2_256s 561
    sets.sha2_256s.keygen sets.sha2_256s.sign sets.sha2_256s.sign_deterministic sets.sha2_256s.verify := by
  have h := @fixedSession .sha2 32#usize 96#usize 128#usize 64#usize _ sha2_256s.pn
    (by right; rw [view_sha2, sha2_256s.hP]; decide) (by decide)
  rw [view_sha2, sha2_256s.hP, sha2_256s.slack] at h
  apply_public_entries h [sets.sha2_256s.keygen, sets.sha2_256s.sign,
    sets.sha2_256s.sign_deterministic, sets.sha2_256s.verify]

theorem sha2_256f_session : PublicSession Spec.sha2_256f 561
    sets.sha2_256f.keygen sets.sha2_256f.sign sets.sha2_256f.sign_deterministic sets.sha2_256f.verify := by
  have h := @fixedSession .sha2 32#usize 96#usize 128#usize 64#usize _ sha2_256f.pn
    (by right; rw [view_sha2, sha2_256f.hP]; decide) (by decide)
  rw [view_sha2, sha2_256f.hP, sha2_256f.slack] at h
  apply_public_entries h [sets.sha2_256f.keygen, sets.sha2_256f.sign,
    sets.sha2_256f.sign_deterministic, sets.sha2_256f.verify]

theorem shake_128s_session : PublicSession Spec.shake_128s 409
    sets.shake_128s.keygen sets.shake_128s.sign sets.shake_128s.sign_deterministic sets.shake_128s.verify := by
  have h := @fixedSession .shake 16#usize 48#usize 64#usize 32#usize _ shake_128s.pn
    (by left; rw [shake_128s.hP]; decide) (by decide)
  rw [shake_128s.hP, shake_128s.slack] at h
  apply_public_entries h [sets.shake_128s.keygen, sets.shake_128s.sign,
    sets.shake_128s.sign_deterministic, sets.shake_128s.verify]

theorem shake_128f_session : PublicSession Spec.shake_128f 409
    sets.shake_128f.keygen sets.shake_128f.sign sets.shake_128f.sign_deterministic sets.shake_128f.verify := by
  have h := @fixedSession .shake 16#usize 48#usize 64#usize 32#usize _ shake_128f.pn
    (by left; rw [shake_128f.hP]; decide) (by decide)
  rw [shake_128f.hP, shake_128f.slack] at h
  apply_public_entries h [sets.shake_128f.keygen, sets.shake_128f.sign,
    sets.shake_128f.sign_deterministic, sets.shake_128f.verify]

theorem shake_192s_session : PublicSession Spec.shake_192s 561
    sets.shake_192s.keygen sets.shake_192s.sign sets.shake_192s.sign_deterministic sets.shake_192s.verify := by
  have h := @fixedSession .shake 24#usize 72#usize 96#usize 48#usize _ shake_192s.pn
    (by left; rw [shake_192s.hP]; decide) (by decide)
  rw [shake_192s.hP, shake_192s.slack] at h
  apply_public_entries h [sets.shake_192s.keygen, sets.shake_192s.sign,
    sets.shake_192s.sign_deterministic, sets.shake_192s.verify]

theorem shake_192f_session : PublicSession Spec.shake_192f 561
    sets.shake_192f.keygen sets.shake_192f.sign sets.shake_192f.sign_deterministic sets.shake_192f.verify := by
  have h := @fixedSession .shake 24#usize 72#usize 96#usize 48#usize _ shake_192f.pn
    (by left; rw [shake_192f.hP]; decide) (by decide)
  rw [shake_192f.hP, shake_192f.slack] at h
  apply_public_entries h [sets.shake_192f.keygen, sets.shake_192f.sign,
    sets.shake_192f.sign_deterministic, sets.shake_192f.verify]

theorem shake_256s_session : PublicSession Spec.shake_256s 561
    sets.shake_256s.keygen sets.shake_256s.sign sets.shake_256s.sign_deterministic sets.shake_256s.verify := by
  have h := @fixedSession .shake 32#usize 96#usize 128#usize 64#usize _ shake_256s.pn
    (by left; rw [shake_256s.hP]; decide) (by decide)
  rw [shake_256s.hP, shake_256s.slack] at h
  apply_public_entries h [sets.shake_256s.keygen, sets.shake_256s.sign,
    sets.shake_256s.sign_deterministic, sets.shake_256s.verify]

theorem shake_256f_session : PublicSession Spec.shake_256f 561
    sets.shake_256f.keygen sets.shake_256f.sign sets.shake_256f.sign_deterministic sets.shake_256f.verify := by
  have h := @fixedSession .shake 32#usize 96#usize 128#usize 64#usize _ shake_256f.pn
    (by left; rw [shake_256f.hP]; decide) (by decide)
  rw [shake_256f.hP, shake_256f.slack] at h
  apply_public_entries h [sets.shake_256f.keygen, sets.shake_256f.sign,
    sets.shake_256f.sign_deterministic, sets.shake_256f.verify]

run_cmd
  for decl in [``sha2_128s_session, ``sha2_128f_session,
      ``sha2_192s_session, ``sha2_192f_session,
      ``sha2_256s_session, ``sha2_256f_session,
      ``shake_128s_session, ``shake_128f_session,
      ``shake_192s_session, ``shake_192f_session,
      ``shake_256s_session, ``shake_256f_session] do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} depends on unexpected axiom {ax}"

end slhdsa.Suite

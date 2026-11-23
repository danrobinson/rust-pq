import ME2E.Shake
import MReduction.Shake
import Slhdsa.Proofs.ShakeSlh

/-! The five extracted SHAKE operations implement the byte cores used by the security
games, uniformly over the six approved parameter rows. -/
namespace ShakeSecurity.Rust
open Aeneas Aeneas.Std Result MLink slhdsa
open Reduction ME2E

def rustParams : Sha2Set → slhdsa.params.Params
  | .s128s => sets.shake_128s.params.PARAMS
  | .s128f => sets.shake_128f.params.PARAMS
  | .s192s => sets.shake_192s.params.PARAMS
  | .s192f => sets.shake_192f.params.PARAMS
  | .s256s => sets.shake_256s.params.PARAMS
  | .s256f => sets.shake_256f.params.PARAMS

def width : Sha2Set → Usize
  | .s128s | .s128f => 16#usize
  | .s192s | .s192f => 24#usize
  | .s256s | .s256f => 32#usize

variable (S : Sha2Set)

theorem pn : PN (rustParams S) (width S) := by
  cases S
  · unfold rustParams width; rw [sets.shake_128s.params.PARAMS, ← sha2_128s.PARAMS_eq]; exact sha2_128s.pn
  · unfold rustParams width; rw [sets.shake_128f.params.PARAMS, ← sha2_128f.PARAMS_eq]; exact sha2_128f.pn
  · unfold rustParams width; rw [sets.shake_192s.params.PARAMS, ← sha2_192s.PARAMS_eq]; exact sha2_192s.pn
  · unfold rustParams width; rw [sets.shake_192f.params.PARAMS, ← sha2_192f.PARAMS_eq]; exact sha2_192f.pn
  · unfold rustParams width; rw [sets.shake_256s.params.PARAMS, ← sha2_256s.PARAMS_eq]; exact sha2_256s.pn
  · unfold rustParams width; rw [sets.shake_256f.params.PARAMS, ← sha2_256f.PARAMS_eq]; exact sha2_256f.pn

theorem shape : Shake.params (rustParams S) = ShakeSecurity.params S := by
  cases S
  · unfold rustParams Shake.params; rw [sets.shake_128s.params.PARAMS, ← sha2_128s.PARAMS_eq, sha2_128s.hP]; rfl
  · unfold rustParams Shake.params; rw [sets.shake_128f.params.PARAMS, ← sha2_128f.PARAMS_eq, sha2_128f.hP]; rfl
  · unfold rustParams Shake.params; rw [sets.shake_192s.params.PARAMS, ← sha2_192s.PARAMS_eq, sha2_192s.hP]; rfl
  · unfold rustParams Shake.params; rw [sets.shake_192f.params.PARAMS, ← sha2_192f.PARAMS_eq, sha2_192f.hP]; rfl
  · unfold rustParams Shake.params; rw [sets.shake_256s.params.PARAMS, ← sha2_256s.PARAMS_eq, sha2_256s.hP]; rfl
  · unfold rustParams Shake.params; rw [sets.shake_256f.params.PARAMS, ← sha2_256f.PARAMS_eq, sha2_256f.hP]; rfl

theorem width_eq : (width S).val = S.vp.params.n := by cases S <;> rfl

theorem n_eq : (width S).val = (ShakeSecurity.params S).n := by cases S <;> rfl

theorem keygen (skSeed skPrf pkSeed : Array U8 (width S)) (sk pk : Slice U8)
    (hs : sk.length = 4 * (width S).val) (hp : pk.length = 2 * (width S).val) :
    shake.slh.slh_keygen_internal (rustParams S) skSeed skPrf pkSeed sk pk ⦃ r =>
      (wire r.2.val, wire r.1.val) = byteKeygen S.vp (prims S) (wireCodec S.vp.params)
        (node S skSeed) (node S skPrf) (node S pkSeed) ⦄ := by
  apply WP.spec_mono (Shake.slh_keygen_internal_spec _ (pn S) skSeed skPrf pkSeed sk pk hs hp)
  rintro r ⟨h, _, _⟩
  exact ShakeLink.ME2E.keygen_transfer S (width_eq S) _ _ _ _ _ (by simpa only [shape] using h)

theorem signInternal (m sk : Slice U8) (rand : Array U8 (width S))
    (hs : sk.length = 4 * (width S).val) :
    shake.slh.slh_sign_internal (rustParams S) m sk rand ⦃ r =>
      wire r.val = byteSign S.vp (prims S) (wireCodec S.vp.params)
        (wire m.val) (wire sk.val) (node S rand) ⦄ := by
  apply WP.spec_mono (Shake.slh_sign_internal_all_lengths _ (pn S) m sk rand hs)
  rintro r ⟨h, _⟩
  exact ShakeLink.ME2E.sign_transfer S (width_eq S) _ _ _ rand
    (by simpa only [← n_eq] using hs) (by simpa only [shape] using h)

theorem verifyInternal (m sig pk : Slice U8) (hp : pk.length = 2 * (width S).val) :
    shake.slh.slh_verify_internal (width S) (rustParams S) m sig pk ⦃ b =>
      b = byteVerify S.vp (prims S) (wireCodec S.vp.params)
        (wire m.val) (wire sig.val) (wire pk.val) ⦄ := by
  apply WP.spec_mono (Shake.slh_verify_internal_all_lengths _ (pn S) m sig pk hp)
  intro b h
  rw [h, shape, ShakeLink.ME2E.verify_transfer S _ _ _ (by simpa only [← n_eq] using hp)]
  rfl

theorem signPure (m ctx sk : Slice U8) (rand : Array U8 (width S))
    (hs : sk.length = 4 * (width S).val) (hm : Room m.length (msgSlack (width S).val + 257)) :
    shake.slh.slh_sign (rustParams S) m ctx sk rand ⦃ r =>
      r.map (fun v => wire v.val) = byteSignPure S.vp (prims S) (wireCodec S.vp.params)
        (wire m.val) (wire ctx.val) (wire sk.val) (node S rand) ⦄ := by
  apply WP.spec_mono (Shake.slh_sign_spec _ (pn S) m ctx sk rand hs hm)
  intro r h
  simpa only [Option.map_map, Function.comp_def, ShakeLink.MReduction.codec] using
    ShakeLink.ME2E.signPure_transfer S (width_eq S) _ _ _ rand
      (by simpa only [← n_eq] using hs) (r.map (fun v => v.val))
      (by simpa only [Option.map_map, Function.comp_def, shape] using h)

theorem verifyPure (m sig ctx pk : Slice U8) (hp : pk.length = 2 * (width S).val)
    (hm : Room m.length (msgSlack (width S).val + 257)) :
    shake.slh.slh_verify (width S) (rustParams S) m sig ctx pk ⦃ b =>
      b = byteVerifyPure S.vp (prims S) (wireCodec S.vp.params)
        (wire m.val) (wire sig.val) (wire ctx.val) (wire pk.val) ⦄ := by
  apply WP.spec_mono (Shake.slh_verify_spec _ (pn S) m sig ctx pk hp hm)
  intro b h
  rw [h, shape, ShakeLink.ME2E.verifyPure_transfer S _ _ _ _ (by simpa only [← n_eq] using hp)]
  rfl

end ShakeSecurity.Rust

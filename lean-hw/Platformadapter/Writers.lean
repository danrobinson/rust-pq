import Platformadapter.ExportsProgram
import Facade.Keygen
open Aeneas Aeneas.Std Result
open slh_dsa
namespace slh_dsa.PlatformExports

/-- The caller-controlled document constructor observes the exact DER prefix
and key. It may return a value, fail or diverge. -/
private theorem callback {T F} (writeSecret : Bool) {K} (header : Std.Array U8 K)
    (len : Usize) (key : Slice U8) (room : len.val=K.val+key.length)
    (cb : core.ops.function.FnOnce F (Slice U8) T) (f : F) :
    (do
      let initial := Array.repeat len 0#u8
      let encoded ← _root_.slhdsa.encoding.der_encode header.to_slice key initial.to_slice
      let buf := initial.from_slice encoded
      let out ← cb.call_once f buf.to_slice
      if writeSecret then
        let _ ← Array.Insts.ZeroizeZeroize.zeroize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) buf
        ok out
      else ok out) =
    cb.call_once f (Slice.from (header.val++key.val) (by simp; change K.val+key.length≤Usize.max; rw [←room]; scalar_tac)) := by
  let initial := Array.repeat len 0#u8
  obtain ⟨s,eq,bytes⟩ := _root_.slhdsa.spec_imp_exists (_root_.slhdsa.enc_der_encode_spec header.to_slice key initial.to_slice
    (by simpa [Slice.length] using room))
  dsimp only
  dsimp only [initial] at eq
  rw [eq]
  simp only [bind_ok]
  have size : s.val.length=len.val := by rw [bytes]; simpa [Slice.length] using room.symm
  have buf : (initial.from_slice s).to_slice = Slice.from (header.val++key.val)
      (by simp; change K.val+key.length≤Usize.max; rw [←room]; scalar_tac) := by
    apply Slice.ext
    rw [Array.val_to_slice,Array.from_slice_val _ _ size,bytes,Array.val_to_slice]
    simp
  rw [buf]
  obtain ⟨_,wipe,_⟩ := _root_.slhdsa.spec_imp_exists (slh_dsa.wipe_bytes_spec ((Array.repeat len 0#u8).from_slice s))
  cases writeSecret <;> simp only [Bool.false_eq_true,ite_false,ite_true,wipe,bind_ok] <;> apply Std.bind_pure


/-- The public and secret document callbacks run on exactly the fixed prefix
and the supplied key bytes. This includes a failing document constructor. -/
def WritersCorrect {P Sk Vk Sig} (C : params.Core P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig))
    {HK HV} (secretHeader : Std.Array U8 HK) (publicHeader : Std.Array U8 HV)
    (privateLen publicLen : Usize) (hs : privateLen.val=HK.val+Sk.val) (hv : publicLen.val=HV.val+Vk.val) : Prop :=
  (∀ (T F : Type) (cb : core.ops.function.FnOnce F (Slice U8) T) (f : F) (key : Slice U8) (size : key.length=Sk.val),
    C.with_pkcs8 cb key f = cb.call_once f (Slice.from (secretHeader.val++key.val)
      (by simp; change HK.val+key.length≤Usize.max; rw [size,←hs]; scalar_tac))) ∧
  (∀ (T F : Type) (cb : core.ops.function.FnOnce F (Slice U8) T) (f : F) (key : Slice U8) (size : key.length=Vk.val),
    C.with_spki cb key f = cb.call_once f (Slice.from (publicHeader.val++key.val)
      (by simp; change HV.val+key.length≤Usize.max; rw [size,←hv]; scalar_tac)))

local macro "writer_proof" coreId:ident priv:term:max pub:term:max plen:term:max vlen:term:max : tactic => do
  let pk := Lean.mkIdent (coreId.getId ++ `with_pkcs8)
  let sp := Lean.mkIdent (coreId.getId ++ `with_spki)
  `(tactic| (
  constructor
  · intro T F cb f key size
    have h := callback true $priv $plen key (by simp [size]) cb f
    change $pk:ident cb key f = _
    unfold $pk:ident
    simp only [lift, bind_tc_eq, bind_ok, Array.to_slice_mut,uncurry]
    simpa only [ite_true] using h
  · intro T F cb f key size
    have h := callback false $pub $vlen key (by simp [size]) cb f
    simp only [Bool.false_eq_true,ite_false,Std.bind_pure] at h
    change $sp:ident cb key f = _
    unfold $sp:ident
    simpa only [lift, bind_tc_eq, bind_ok, Array.to_slice_mut,uncurry] using h))

local macro "set_writers " lemmaId:ident coreId:ident secret:ident publicHeader:ident plen:term:max vlen:term:max : command =>
  `(theorem $lemmaId : WritersCorrect $coreId $secret $publicHeader $plen $vlen (by decide) (by decide) := by
      writer_proof $coreId $secret $publicHeader $plen $vlen)

set_writers sha2_128s_writers params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
  _root_.slhdsa.sets.sha2_128s.PKCS8_PREFIX _root_.slhdsa.sets.sha2_128s.SPKI_PREFIX 84#usize 50#usize
set_writers sha2_128f_writers params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
  _root_.slhdsa.sets.sha2_128f.PKCS8_PREFIX _root_.slhdsa.sets.sha2_128f.SPKI_PREFIX 84#usize 50#usize
set_writers sha2_192s_writers params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
  _root_.slhdsa.sets.sha2_192s.PKCS8_PREFIX _root_.slhdsa.sets.sha2_192s.SPKI_PREFIX 116#usize 66#usize
set_writers sha2_192f_writers params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
  _root_.slhdsa.sets.sha2_192f.PKCS8_PREFIX _root_.slhdsa.sets.sha2_192f.SPKI_PREFIX 116#usize 66#usize
set_writers sha2_256s_writers params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
  _root_.slhdsa.sets.sha2_256s.PKCS8_PREFIX _root_.slhdsa.sets.sha2_256s.SPKI_PREFIX 150#usize 82#usize
set_writers sha2_256f_writers params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856
  _root_.slhdsa.sets.sha2_256f.PKCS8_PREFIX _root_.slhdsa.sets.sha2_256f.SPKI_PREFIX 150#usize 82#usize
set_writers shake_128s_writers params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
  _root_.slhdsa.sets.shake_128s.PKCS8_PREFIX _root_.slhdsa.sets.shake_128s.SPKI_PREFIX 84#usize 50#usize
set_writers shake_128f_writers params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
  _root_.slhdsa.sets.shake_128f.PKCS8_PREFIX _root_.slhdsa.sets.shake_128f.SPKI_PREFIX 84#usize 50#usize
set_writers shake_192s_writers params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
  _root_.slhdsa.sets.shake_192s.PKCS8_PREFIX _root_.slhdsa.sets.shake_192s.SPKI_PREFIX 116#usize 66#usize
set_writers shake_192f_writers params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
  _root_.slhdsa.sets.shake_192f.PKCS8_PREFIX _root_.slhdsa.sets.shake_192f.SPKI_PREFIX 116#usize 66#usize
set_writers shake_256s_writers params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
  _root_.slhdsa.sets.shake_256s.PKCS8_PREFIX _root_.slhdsa.sets.shake_256s.SPKI_PREFIX 150#usize 82#usize
set_writers shake_256f_writers params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856
  _root_.slhdsa.sets.shake_256f.PKCS8_PREFIX _root_.slhdsa.sets.shake_256f.SPKI_PREFIX 150#usize 82#usize

end slh_dsa.PlatformExports

import Ct.Encoding

/-! Leakage of key handling and DER codecs on the fixed-size SHAKE APIs. -/
open Aeneas Aeneas.Std Ct

namespace Ct.Shake.Encoding

def Unary {α β : Type} (f : α → Leak β) : Prop :=
  ∀ a b, Rel (f a) (f b) (fun _ _ => True)

def Binary {α β γ : Type} (f : α → β → Leak γ) : Prop :=
  ∀ a b c d, Rel (f a b) (f c d) (fun _ _ => True)

def OnLengths {α : Type} (f : Slice U8 → Leak α) : Prop :=
  ∀ a b, a.length = b.length → Rel (f a) (f b) (fun _ _ => True)

def Parse {α : Type} (prefixLen : Nat) (f : Slice U8 → Leak α) : Prop :=
  ∀ a b, a.length = b.length → a.val.take prefixLen = b.val.take prefixLen →
    Rel (f a) (f b) (fun _ _ => True)

def ParseInto {α β : Type} (prefixLen : Nat) (f : Slice U8 → α → Leak β) : Prop :=
  ∀ a b sk sk', a.length = b.length → a.val.take prefixLen = b.val.take prefixLen →
    Rel (f a sk) (f b sk') (fun _ _ => True)

macro "codec_traces" eq:ident pk8:ident spki:ident sk:ident pk:ident
    sig:ident getSk:ident getPk:ident : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _; unfold $eq:ident; ct_steps
  · intro _ _ _ _; unfold $pk8:ident; ct_steps
  · intro _ _; unfold $spki:ident; ct_steps
  · intro _ _ _; unfold $sk:ident; ct_steps
  · intro _ _ _; unfold $pk:ident; ct_steps
  · intro _ _ _; unfold $sig:ident; ct_steps
  · intro _ _ _ _ _ hp
    unfold $getSk:ident
    ct_steps
    all_goals first | ct_side | skip
    simp only [Leak.erase_pure, Result.ok.injEq] at *
    subst_vars
    intro j hj
    exact Ct.Encoding.getElem!_of_take_eq hp j (by simpa using hj)
  · intro _ _ _ hp
    unfold $getPk:ident
    ct_steps
    all_goals first | ct_side | skip
    simp only [Leak.erase_pure, Result.ok.injEq] at *
    subst_vars
    intro j hj
    exact Ct.Encoding.getElem!_of_take_eq hp j (by simpa using hj)))

open slhdsa_leak.sets.shake_128s in
theorem shake_128s_codecs : Binary secret_keys_equal ∧ Binary pkcs8_encode ∧ Unary spki_encode ∧
    OnLengths secret_key_from ∧ OnLengths public_key_from ∧ OnLengths signature_len_ok ∧
    ParseInto 20 pkcs8_decode ∧ Parse 18 spki_decode := by
  codec_traces secret_keys_equal pkcs8_encode spki_encode secret_key_from public_key_from
    signature_len_ok pkcs8_decode spki_decode

open slhdsa_leak.sets.shake_128f in
theorem shake_128f_codecs : Binary secret_keys_equal ∧ Binary pkcs8_encode ∧ Unary spki_encode ∧
    OnLengths secret_key_from ∧ OnLengths public_key_from ∧ OnLengths signature_len_ok ∧
    ParseInto 20 pkcs8_decode ∧ Parse 18 spki_decode := by
  codec_traces secret_keys_equal pkcs8_encode spki_encode secret_key_from public_key_from
    signature_len_ok pkcs8_decode spki_decode

open slhdsa_leak.sets.shake_192s in
theorem shake_192s_codecs : Binary secret_keys_equal ∧ Binary pkcs8_encode ∧ Unary spki_encode ∧
    OnLengths secret_key_from ∧ OnLengths public_key_from ∧ OnLengths signature_len_ok ∧
    ParseInto 20 pkcs8_decode ∧ Parse 18 spki_decode := by
  codec_traces secret_keys_equal pkcs8_encode spki_encode secret_key_from public_key_from
    signature_len_ok pkcs8_decode spki_decode

open slhdsa_leak.sets.shake_192f in
theorem shake_192f_codecs : Binary secret_keys_equal ∧ Binary pkcs8_encode ∧ Unary spki_encode ∧
    OnLengths secret_key_from ∧ OnLengths public_key_from ∧ OnLengths signature_len_ok ∧
    ParseInto 20 pkcs8_decode ∧ Parse 18 spki_decode := by
  codec_traces secret_keys_equal pkcs8_encode spki_encode secret_key_from public_key_from
    signature_len_ok pkcs8_decode spki_decode

open slhdsa_leak.sets.shake_256s in
theorem shake_256s_codecs : Binary secret_keys_equal ∧ Binary pkcs8_encode ∧ Unary spki_encode ∧
    OnLengths secret_key_from ∧ OnLengths public_key_from ∧ OnLengths signature_len_ok ∧
    ParseInto 22 pkcs8_decode ∧ Parse 18 spki_decode := by
  codec_traces secret_keys_equal pkcs8_encode spki_encode secret_key_from public_key_from
    signature_len_ok pkcs8_decode spki_decode

open slhdsa_leak.sets.shake_256f in
theorem shake_256f_codecs : Binary secret_keys_equal ∧ Binary pkcs8_encode ∧ Unary spki_encode ∧
    OnLengths secret_key_from ∧ OnLengths public_key_from ∧ OnLengths signature_len_ok ∧
    ParseInto 22 pkcs8_decode ∧ Parse 18 spki_decode := by
  codec_traces secret_keys_equal pkcs8_encode spki_encode secret_key_from public_key_from
    signature_len_ok pkcs8_decode spki_decode

end Ct.Shake.Encoding

#print axioms Ct.Shake.Encoding.shake_128s_codecs
#print axioms Ct.Shake.Encoding.shake_128f_codecs
#print axioms Ct.Shake.Encoding.shake_192s_codecs
#print axioms Ct.Shake.Encoding.shake_192f_codecs
#print axioms Ct.Shake.Encoding.shake_256s_codecs
#print axioms Ct.Shake.Encoding.shake_256f_codecs

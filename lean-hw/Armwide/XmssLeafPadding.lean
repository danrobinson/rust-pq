import Armwide.XmssLeaves
import Armwide.Encoders
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.XmssLeaves
open Keygen
set_option maxHeartbeats 700000

def checkedAdrs (a : slhdsa.address.Adrs) : ArmwideRust.address.Adrs :=
  ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

def prepared (n : Nat) {L : Usize} (a : Spec.Adrs) (key : Nat) (buf : Array U8 L) :=
  ∀ pl : Spec.Bytes, pl.length=payLen n →
  (slhdsa.bytes buf.val).setSlice! 22 pl = padded n (leafAddr a key) (filled n pl)

abbrev prepare {L : Usize} (buf : Array U8 L) (a : slhdsa.address.Adrs) (key : U32) (size block : Usize) :=
  ArmwideRust.xmss.arm.prepare_tlen buf (checkedAdrs a) key size block

theorem prepare_spec (n : Nat) (width : n=16 ∨ n=24 ∨ n=32) (L size block : Usize)
    (layout : L.val=total n) (amount : size.val=22+payLen n) (prefixLen : block.val=if n=16 then 64 else 128)
    (a : slhdsa.address.Adrs) (key : U32) :
    prepare (Array.repeat L 0#u8) a key size block ⦃ buf => prepared n (slhdsa.adrsS a) key.val buf ⦄ := by
  obtain ⟨buf,okbuf,_⟩ := spec_imp_exists (Armwide.prepare_tlen_spec (Array.repeat L 0#u8) (checkedAdrs a)
    key size block (by omega) (by rw [layout,amount]; rcases width with rfl|rfl|rfl <;> decide)
    (by rw [prefixLen,amount]; rcases width with rfl|rfl|rfl <;> decide))
  unfold prepare
  rw [okbuf]
  simp only [WP.spec_ok]
  intro pl len
  rw [padded_eq n width _ pl len]
  let pkAddr := ({(slhdsa.adrsS a).setTypeAndClear Spec.WOTS_PK with keypair:=key.val} : Spec.Adrs)
  change _ = if n=16 then padFrom 64 (pkAddr.compress ++ pl) else S512.padFrom 128 (pkAddr.compress ++ pl)
  by_cases small : n=16
  · subst n
    have hp : L=640#usize := by change L.val=640 at layout; scalar_tac
    have hs : size=582#usize := by change size.val=582 at amount; scalar_tac
    have hb : block=64#usize := by simp at prefixLen; scalar_tac
    subst L; subst size; subst block
    have h := Armwide.prepare_tlen_sha256_pad (checkedAdrs a) key (List.replicate 64 0#8) pl
      (by simp) len
    rw [okbuf] at h; simp only [WP.spec_ok] at h
    change _ = (Spec.SHA256.pad ((List.replicate 64 0#8) ++ pkAddr.compress ++ pl)).drop 64 at h
    rw [List.append_assoc,pad_append64 _ _ (by simp),List.drop_left' (by simp)] at h
    exact h
  · simp only [small,↓reduceIte]
    have hs : (L.val=1280 ∧ size.val=1246) ∨ (L.val=2304 ∧ size.val=2166) := by
      rw [layout,amount]; rcases width with h|rfl|rfl
      · contradiction
      · decide
      · decide
    have hb : block=128#usize := by simp [small] at prefixLen; scalar_tac
    subst block
    have h := Armwide.prepare_tlen_sha512_pad L size hs (checkedAdrs a) key (List.replicate 128 0#8) pl
      (by simp) (by rw [len,amount];omega)
    rw [okbuf] at h; simp only [WP.spec_ok] at h
    change _ = (Spec.SHA512.pad ((List.replicate 128 0#8) ++ pkAddr.compress ++ pl)).drop 128 at h
    rw [List.append_assoc,S512.pad_append128 _ _ (by simp),List.drop_left' (by simp)] at h
    exact h

end slhdsa.Armwide.XmssLeaves

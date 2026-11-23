import Keypadding.Funs
import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Keypadding

def addressOf (a : PadRust.address.Adrs) : address.Adrs :=
  ⟨a.layer, a.tree, a.typ, a.keypair, a.word2, a.word3⟩

def keyAddress (a : PadRust.address.Adrs) (k : U32) : address.Adrs :=
  { addressOf a with typ := 1#u32, keypair := k, word2 := 0#u32, word3 := 0#u32 }

private theorem address_eq (a : PadRust.address.Adrs) :
    PadRust.address.Adrs.compress a = address.Adrs.compress (addressOf a) := rfl

theorem prepare_message_spec {L : Usize} (m : Array U8 L) (a : PadRust.address.Adrs)
    (k : U32) (size block : Usize) (hs : 22 ≤ size.val) (hl : size.val + 3 ≤ L.val)
    (hb : (block.val + size.val) * 8 < 65536) :
    PadRust.xmss.wide.prepare_message m a k size block ⦃ r =>
      ∃ adrBytes : Array U8 22#usize, bytes adrBytes.val = (adrsS (keyAddress a k)).compress ∧
      r.val = (((m.val.setSlice! 0 adrBytes.val).set size.val 128#u8).setSlice! (L.val - 2)
        ((BitVec.ofNat 16 ((block.val + size.val) * 8)).toBEBytes.map UScalar.mk)) ⦄ := by
  unfold PadRust.xmss.wide.prepare_message
  simp only [PadRust.address.Adrs.with_type, PadRust.address.Adrs.with_keypair,
    PadRust.address.WOTS_PK, address_eq]
  step*
  refine ⟨a2, a2_post, ?_⟩
  rw [s3_post2, s5_post, s4_post, Array.val_to_slice, i_post, m2_post,
    Array.set_val_eq, s_post2, s2_post, s1_post, Array.val_to_slice]
  have hi3 : i3 = U16.ofNat ((block.val + size.val) * 8) (by scalar_tac) := by
    apply UScalar.eq_of_val_eq
    rw [i3_post, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change i2.val < 65536; omega)]
    simp [i2_post, i1_post]
  rw [a3_post, hi3]
  simp only [U16.bv, U16.ofNat_bv, UScalarTy.numBits]

/-- Inserting endpoint bytes into the prepared zeroed buffer gives the padding of
the full seeded SHA message for each WOTS parameter size. -/
theorem padded_endpoints {L : Usize} (a : PadRust.address.Adrs) (k : U32)
    (size block : Usize) (payload : List U8)
    (shape : (payload.length = 560 ∧ L.val = 640 ∧ block.val = 64) ∨
      (payload.length = 1224 ∧ L.val = 1280 ∧ block.val = 128) ∨
      (payload.length = 2144 ∧ L.val = 2304 ∧ block.val = 128))
    (sz : size.val = 22 + payload.length) :
    PadRust.xmss.wide.prepare_message (Array.repeat L 0#u8) a k size block ⦃ r =>
      let msg := (adrsS (keyAddress a k)).compress ++ bytes payload
      bytes (r.val.setSlice! 22 payload) =
        if block.val = 64 then padFrom 64 msg else S512.padFrom 128 msg ⦄ := by
  have bounds : 22 ≤ size.val ∧ size.val + 3 ≤ L.val ∧ (block.val + size.val)*8 < 65536 := by
    rcases shape with h | h | h <;> omega
  apply WP.spec_mono (prepare_message_spec _ _ _ _ _ bounds.1 bounds.2.1 bounds.2.2)
  intro r ⟨adrBytes, ha, hr⟩
  rw [hr, Array.repeat_val, setSlice_rep _ _ _ (by simp; omega)]
  have plen : adrBytes.val.length = 22 := by simp
  let z := L.val-size.val-3
  have split : L.val-22 = payload.length + (1+(z+2)) := by dsimp [z]; omega
  let footer := (BitVec.ofNat 16 ((block.val + size.val) * 8)).toBEBytes.map (UScalar.mk (ty := .U8))
  have zeros : List.replicate (L.val-22) 0#u8 = List.replicate payload.length 0#u8 ++
      0#u8 :: (List.replicate z 0#u8 ++ List.replicate 2 0#u8) := by
    rw [split, List.replicate_add, Nat.add_comm 1, List.replicate_succ, List.replicate_add]
  rw [plen, zeros, ← List.append_assoc, set_mid _ _ _ _ _ (by simp [plen, sz])]
  have hfooter (head : List U8) (hlen : head.length = L.val-2) :
      (head ++ List.replicate 2 0#u8).setSlice! (L.val-2) footer = head ++ footer := by
    simp [List.setSlice!, ← hlen, footer]
  have hh : (adrBytes.val ++ List.replicate payload.length 0#u8 ++
       128#u8 :: (List.replicate z 0#u8 ++ List.replicate 2 0#u8)) =
      (adrBytes.val ++ List.replicate payload.length 0#u8 ++ [128#u8] ++ List.replicate z 0#u8) ++
        List.replicate 2 0#u8 := by simp [List.append_assoc]
  rw [hh, hfooter _ (by simp [plen, z]; omega)]
  simp only [List.append_assoc]
  have ins (tail : List U8) : (adrBytes.val ++ (List.replicate payload.length 0#u8 ++ tail)).setSlice! 22 payload =
      adrBytes.val ++ payload ++ tail := by
    rw [← List.append_assoc]
    exact setSlice!_mid _ _ _ _ _ plen.symm (by simp)
  rw [ins]
  let msg := (adrsS (keyAddress a k)).compress ++ bytes payload
  have ml : msg.length = size.val := by simp [msg, sz, adrs_compress_length, bytes]
  change _ = if block.val = 64 then padFrom 64 msg else S512.padFrom 128 msg
  rw [bytes_append, bytes_append, ha]
  change msg ++ _ = _
  rcases shape with ⟨hp,hL,hb⟩ | ⟨hp,hL,hb⟩ | ⟨hp,hL,hb⟩ <;>
    simp only [hb, ↓reduceIte, padFrom, S512.padFrom, ml, sz, hp] <;>
    simp only [List.append_assoc] <;> congr 1 <;>
    simp only [bytes_append, bytes_replicate, bytes_cons, bytes_nil, footer, z, hL, hb, sz, hp] <;>
    decide +kernel

#print axioms prepare_message_spec
#print axioms padded_endpoints
end slhdsa.X86.Keypadding

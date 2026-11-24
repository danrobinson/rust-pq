import Prehash.Funs
import Slhdsa.Proofs.Hash

open Aeneas Aeneas.Std Result
namespace slhdsa.prehash

def digestSize : PreHash → Nat
  | .Sha256 | .Shake128 => 32
  | .Sha512 | .Shake256 => 64

def oidBytes (ph : PreHash) : List U8 :=
  [6#u8,9#u8,96#u8,134#u8,72#u8,1#u8,101#u8,3#u8,4#u8,2#u8,
    match ph with | .Sha256 => 1#u8 | .Sha512 => 3#u8 | .Shake128 => 11#u8 | .Shake256 => 12#u8]

@[step] theorem digest_size_spec (ph : PreHash) : ph.digest_len ⦃ n => n.val = digestSize ph ⦄ := by
  cases ph <;> simp [PreHash.digest_len, digestSize]

@[step] theorem oid_spec (ph : PreHash) : ph.oid_der ⦃ a => a.val = oidBytes ph ⦄ := by
  cases ph <;> simp [PreHash.oid_der, oidBytes, global_simps, Array.make_val]

private theorem writeTail (headBytes data : List U8) (space start : Nat)
    (fits : data.length ≤ space) (offset : start = headBytes.length) :
    (headBytes ++ List.replicate space 0#u8).setSlice! start data =
      (headBytes ++ data) ++ List.replicate (space - data.length) 0#u8 := by
  subst start
  simp [List.setSlice!, fits, List.append_assoc]

set_option maxRecDepth 4096 in
theorem framing (ctx digest : Slice U8) (ph : PreHash) :
    format_prehash_message ctx ph digest ⦃ out =>
      if ctx.length ≤ 255 ∧ digest.length = digestSize ph then
        ∃ buf n, out = some (buf,n) ∧
          buf.val.take n.val = [1#u8, UScalar.cast .U8 ctx.len] ++
            ctx.val ++ oidBytes ph ++ digest.val ∧
          n.val = 13 + ctx.length + digest.length
      else out = none ⦄ := by
  have bound : digestSize ph ≤ 64 := by cases ph <;> decide
  unfold format_prehash_message
  step* <;> simp_all only [bne_iff_ne, not_ne_iff, Slice.len_val, Array.length_to_slice] <;>
    first | scalar_tac | skip
  have hc : ctx.length ≤ 255 := by scalar_tac
  have hd : digest.length = digestSize ph := by scalar_tac
  rw [ite_eq_left ⟨hc,hd⟩]
  refine ⟨_,_,rfl,?_,by scalar_tac⟩
  rw [s8_post2, Array.val_to_slice, oid_post]
  have init : (((Array.repeat 332#usize 0#u8).set 0#usize 1#u8).set 1#usize
      (UScalar.cast .U8 ctx.len)).val =
      [1#u8, UScalar.cast .U8 ctx.len] ++ List.replicate 330 0#u8 := by rfl
  let tag := [1#u8, UScalar.cast .U8 ctx.len]
  have headLen : tag.length = 2 := rfl
  have ho : (oidBytes ph).length = 11 := rfl
  rw [init, writeTail tag ctx.val 330 2 (by change ctx.length ≤ 330; omega) rfl]
  rw [writeTail (tag ++ ctx.val) (oidBytes ph) _ (2 + ctx.length)
      (by change (oidBytes ph).length ≤ 330 - ctx.length; omega) (by simp [headLen, Slice.length])]
  rw [writeTail ((tag ++ ctx.val) ++ oidBytes ph) digest.val _ _
    (by change digest.length ≤ 330 - ctx.length - (oidBytes ph).length; omega)
    (by simp [headLen, Slice.length,ho,Nat.add_assoc])]
  rw [show total.val = (((tag ++ ctx.val) ++ oidBytes ph) ++ digest.val).length by
    simp only [List.length_append, headLen, ho]; change _ = 2 + ctx.length + 11 + digest.length; scalar_tac]
  rw [List.take_left]

end slhdsa.prehash

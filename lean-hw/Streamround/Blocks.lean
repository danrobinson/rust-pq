import Chainavx2.Chunks
import Slhdsa.Proofs.Sha256
import Slhdsa.Proofs.Sha512
open Aeneas Aeneas.Std Result
open ChainAvx2Rust (fullChunks remainder)
namespace slhdsa.X86.Stream

def blockBytes {n} (blocks : List (Array U8 n)) := blocks.flatMap (fun b => bytes b.val)

theorem split_message {n} (msg : Slice U8) :
    blockBytes (fullChunks n msg).val ++ bytes (remainder n msg).val = bytes msg.val := by
  have h := congrArg bytes (ChainAvx2Rust.chunk_parts msg n)
  simpa [bytes,blockBytes,List.map_flatMap] using h

theorem group_count {n} (msg : Slice U8) : (fullChunks n msg).length = msg.length/n.val := by
  simp [fullChunks,Slice.length]

theorem tail_size {n} (msg : Slice U8) : (remainder n msg).length = msg.length % n.val := by
  simp only [remainder,Slice.length,Slice.from_val,List.length_drop]
  have := Nat.mod_add_div msg.val.length n.val
  omega

def fold256 (st : List Spec.SHA256.Word) (bs : List (Array U8 64#usize)) :=
  bs.foldl (fun s b => Spec.SHA256.compress s (bytes b.val)) st

theorem fold256_append (st : List Spec.SHA256.Word) (pre : Nat) (bs : List (Array U8 64#usize)) (tail : Spec.Bytes) :
    slhdsa.hashFrom st (slhdsa.padFrom pre (blockBytes bs ++ tail)) =
      slhdsa.hashFrom (fold256 st bs) (slhdsa.padFrom (pre+bs.length*64) tail) := by
  induction bs generalizing st pre with
  | nil => simp [blockBytes,fold256]
  | cons b bs ih =>
    have size : (bytes b.val).length = 64 := by simp
    simp only [blockBytes,List.flatMap_cons,List.append_assoc,slhdsa.padFrom_append64 _ _ _ size,
      slhdsa.hashFrom_append64 _ _ _ size,List.length_cons,fold256,List.foldl_cons]
    exact (ih (Spec.SHA256.compress st (bytes b.val)) (pre+64)).trans (by congr 2 <;> omega)

theorem fold256_exact (st : List Spec.SHA256.Word) (bs : List (Array U8 64#usize)) :
    slhdsa.hashFrom st (blockBytes bs) = fold256 st bs := by
  induction bs generalizing st with
  | nil => simp [slhdsa.hashFrom,blockBytes,fold256]
  | cons b bs ih =>
    rw [show blockBytes (b::bs) = bytes b.val ++ blockBytes bs from rfl,slhdsa.hashFrom_append64 _ _ _ (by simp)]
    exact ih _

theorem stream256_padding (st : List Spec.SHA256.Word) (pre : Nat) (msg padding : Slice U8)
    (padded : bytes padding.val = slhdsa.padFrom (pre+(msg.length/64)*64) (bytes (remainder 64#usize msg).val)) :
    fold256 (fold256 st (fullChunks 64#usize msg).val) (fullChunks 64#usize padding).val =
      slhdsa.hashFrom st (slhdsa.padFrom pre (bytes msg.val)) := by
  have aligned := slhdsa.padFrom_length (pre+(msg.length/64)*64) (bytes (remainder 64#usize msg).val)
  rw [← padded] at aligned
  have endLen : (remainder 64#usize padding).length = 0 := by
    rw [tail_size]; simpa [Slice.length] using aligned
  have noTail : (remainder 64#usize padding).val = [] := List.length_eq_zero_iff.mp endLen
  have flat := split_message (n := 64#usize) padding
  rw [noTail] at flat
  rw [show bytes [] = [] from rfl,List.append_nil] at flat
  rw [← fold256_exact,flat,padded,← split_message (n := 64#usize) msg,fold256_append]
  rw [show (fullChunks 64#usize msg).val.length = msg.length/64 from group_count msg]

def fold512 (st : List Spec.SHA512.Word) (bs : List (Array U8 128#usize)) :=
  bs.foldl (fun s b => Spec.SHA512.compress s (bytes b.val)) st

theorem fold512_append (st : List Spec.SHA512.Word) (pre : Nat) (bs : List (Array U8 128#usize)) (tail : Spec.Bytes) :
    slhdsa.S512.hashFrom st (slhdsa.S512.padFrom pre (blockBytes bs ++ tail)) =
      slhdsa.S512.hashFrom (fold512 st bs) (slhdsa.S512.padFrom (pre+bs.length*128) tail) := by
  induction bs generalizing st pre with
  | nil => simp [blockBytes,fold512]
  | cons b bs ih =>
    have size : (bytes b.val).length = 128 := by simp
    simp only [blockBytes,List.flatMap_cons,List.append_assoc,slhdsa.S512.padFrom_append128 _ _ _ size,
      slhdsa.S512.hashFrom_append128 _ _ _ size,List.length_cons,fold512,List.foldl_cons]
    exact (ih (Spec.SHA512.compress st (bytes b.val)) (pre+128)).trans (by congr 2 <;> omega)

theorem fold512_exact (st : List Spec.SHA512.Word) (bs : List (Array U8 128#usize)) :
    slhdsa.S512.hashFrom st (blockBytes bs) = fold512 st bs := by
  induction bs generalizing st with
  | nil => simp [slhdsa.S512.hashFrom,blockBytes,fold512]
  | cons b bs ih =>
    rw [show blockBytes (b::bs) = bytes b.val ++ blockBytes bs from rfl,slhdsa.S512.hashFrom_append128 _ _ _ (by simp)]
    exact ih _

theorem stream512_padding (st : List Spec.SHA512.Word) (pre : Nat) (msg padding : Slice U8)
    (padded : bytes padding.val = slhdsa.S512.padFrom (pre+(msg.length/128)*128) (bytes (remainder 128#usize msg).val)) :
    fold512 (fold512 st (fullChunks 128#usize msg).val) (fullChunks 128#usize padding).val =
      slhdsa.S512.hashFrom st (slhdsa.S512.padFrom pre (bytes msg.val)) := by
  have aligned := slhdsa.S512.padFrom_length (pre+(msg.length/128)*128) (bytes (remainder 128#usize msg).val)
  rw [← padded] at aligned
  have endLen : (remainder 128#usize padding).length = 0 := by
    rw [tail_size]; simpa [Slice.length] using aligned
  have noTail : (remainder 128#usize padding).val = [] := List.length_eq_zero_iff.mp endLen
  have flat := split_message (n := 128#usize) padding
  rw [noTail] at flat
  rw [show bytes [] = [] from rfl,List.append_nil] at flat
  rw [← fold512_exact,flat,padded,← split_message (n := 128#usize) msg,fold512_append]
  rw [show (fullChunks 128#usize msg).val.length = msg.length/128 from group_count msg]
end slhdsa.X86.Stream

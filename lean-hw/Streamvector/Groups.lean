import Streamround.Blocks
open Aeneas Aeneas.Std Result
open ChainAvx2Rust (fullChunks remainder)
namespace slhdsa.X86.Stream

/-- Consecutive groups preserve the left-to-right order required for chaining
one message, even when each group's schedules are computed in parallel. -/
theorem fold_groups {α β : Type} {n : Usize} (step : β → α → β) (initial : β)
    (groups : List (Array α n)) :
    groups.foldl (fun s group => group.val.foldl step s) initial =
      (groups.flatMap (·.val)).foldl step initial := by
  induction groups generalizing initial with
  | nil => rfl
  | cons group groups ih => simp only [List.foldl_cons,List.flatMap_cons,List.foldl_append,ih]

theorem prefix_groups256 (st : List Spec.SHA256.Word) (b : Slice (Array U8 64#usize)) :
    fold256 ((fullChunks 16#usize b).val.foldl (fun s g => fold256 s g.val) st) (remainder 16#usize b).val =
      fold256 st b.val := by
  unfold fold256
  rw [fold_groups,← List.foldl_append,ChainAvx2Rust.chunk_parts]

theorem prefix_groups512 (st : List Spec.SHA512.Word) (b : Slice (Array U8 128#usize)) :
    fold512 ((fullChunks 8#usize b).val.foldl (fun s g => fold512 s g.val) st) (remainder 8#usize b).val =
      fold512 st b.val := by
  unfold fold512
  rw [fold_groups,← List.foldl_append,ChainAvx2Rust.chunk_parts]

end slhdsa.X86.Stream

import Streamscalar.Fips
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream

/-- Each row holds one precomputed round word for each message block in the group. -/
def ordered256 (table : Array (Array U32 16#usize) 64#usize)
    (blocks : Array (Array U8 64#usize) 16#usize) (count : Nat) :=
  ∀ i < count, ∀ lane < 16, table.val[i]!.val[lane]!.bv =
    Spec.SHA256.K[i]! + (Spec.SHA256.schedule (bytes blocks.val[lane]!.val))[i]!

theorem ordered_round256 (i lane : Nat) (st v : Array U32 8#usize)
    (table : Array (Array U32 16#usize) 64#usize) (blocks : Array (Array U8 64#usize) 16#usize)
    (roundIndex : i < 64) (laneIndex : lane < 16) (rows : ordered256 table blocks 64)
    (state : state256 v = rounds256 i (bytes blocks.val[lane]!.val) st) :
    StreamRoundRust.sha256.stream.round v table.val[i]!.val[lane]! ⦃ out =>
      state256 out = rounds256 (i+1) (bytes blocks.val[lane]!.val) st ⦄ := by
  apply WP.spec_mono (round256_spec v _ _ i (rows i roundIndex lane laneIndex))
  intro out computed
  simp only [computed,state,rounds256,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- Each row holds one precomputed round word for each message block in the group. -/
def ordered512 (table : Array (Array U64 8#usize) 80#usize)
    (blocks : Array (Array U8 128#usize) 8#usize) (count : Nat) :=
  ∀ i < count, ∀ lane < 8, table.val[i]!.val[lane]!.bv =
    Spec.SHA512.K[i]! + (Spec.SHA512.schedule (bytes blocks.val[lane]!.val))[i]!

theorem ordered_round512 (i lane : Nat) (st v : Array U64 8#usize)
    (table : Array (Array U64 8#usize) 80#usize) (blocks : Array (Array U8 128#usize) 8#usize)
    (roundIndex : i < 80) (laneIndex : lane < 8) (rows : ordered512 table blocks 80)
    (state : state512 v = rounds512 i (bytes blocks.val[lane]!.val) st) :
    StreamRoundRust.sha512.stream.round v table.val[i]!.val[lane]! ⦃ out =>
      state512 out = rounds512 (i+1) (bytes blocks.val[lane]!.val) st ⦄ := by
  apply WP.spec_mono (round512_spec v _ _ i (rows i roundIndex lane laneIndex))
  intro out computed
  simp only [computed,state,rounds512,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

end slhdsa.X86.Stream

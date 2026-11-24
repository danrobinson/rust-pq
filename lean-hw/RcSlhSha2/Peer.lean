import RcSlhSha2.Full

namespace slhdsa.RcSlhSha2
open Aeneas Aeneas.Std Result Spec

/-- The provider accepts any batching of the complete blocks. Each individual
call receives a representable Rust slice. -/
structure Partition (B : Type) where
  group : List B → List (Slice B)
  ordered : ∀ bs, (group bs).flatMap (·.val) = bs

def singletonPartition (B : Type) : Partition B where
  group bs := bs.map (fun b => Slice.from [b] (by scalar_tac))
  ordered bs := by simp [List.flatMap_map]

structure Routing where
  sha256 : Provider
  sha512 : Provider
  batches256 : Partition (Array U8 64#usize)
  batches512 : Partition (Array U8 128#usize)

/-- Observations are total-correctness postconditions of the selected Rust
provider on every input. No digest correctness property is assumed. -/
def Observed (route : Routing) (algs : Algorithms) : Prop :=
  (∀ m, finish256 route.sha256 (route.batches256.group (blocks 64#usize (padded 64 8 m))) ⦃
    out => out = algs.sha256 m ⦄) ∧
  (∀ m, finish512 route.sha512 (route.batches512.group (blocks 128#usize (padded 128 16 m))) ⦃
    out => out = algs.sha512 m ⦄)

theorem observed_iff (route : Routing) (algs : Algorithms) :
    Observed route algs ↔ algs = nativeAlgorithms := by
  have existsNative : Observed route nativeAlgorithms :=
    ⟨fun m => finish256_spec _ _ _ (route.batches256.ordered _),
     fun m => finish512_spec _ _ _ (route.batches512.ordered _)⟩
  constructor
  · intro h
    have same256 : algs.sha256 = nativeAlgorithms.sha256 := funext fun m => by
      obtain ⟨out,e1,e2⟩ := WP.spec_exists (WP.spec_and (h.1 m) (existsNative.1 m))
      exact e1.symm.trans e2
    have same512 : algs.sha512 = nativeAlgorithms.sha512 := funext fun m => by
      obtain ⟨out,e1,e2⟩ := WP.spec_exists (WP.spec_and (h.2 m) (existsNative.2 m))
      exact e1.symm.trans e2
    cases algs
    congr
  · rintro rfl; exact existsNative

/-- The unique whole-digest behavior produced by these two selected providers
gives all six FIPS 205 suite results. Selection and block grouping can differ
between SHA-256 and SHA-512. -/
theorem suite_on_platform (route : Routing) (s : StandardSet) (seed : Bytes) (addr : Adrs)
    (secret m1 m2 : Bytes) (rows : List Bytes) (r root key rand : Bytes) (msg : List (List Bytes))
    (hk : key.length = (params s).n) :
    ∃! algs, Observed route algs ∧
      suite s seed addr.bytes secret m1 m2 rows r root key rand msg algs =
        standard (params s) seed addr secret m1 m2 rows r root key rand msg := by
  refine ⟨nativeAlgorithms,⟨(observed_iff _ _).mpr rfl,suite_is_fips _ _ _ _ _ _ _ _ _ _ _ _ hk⟩,?_⟩
  intro algs h
  exact (observed_iff _ _).mp h.1

end slhdsa.RcSlhSha2

import RcSlhSha2.Reblock
import RcSlhSha2.Finalize

namespace slhdsa.RcSlhSha2
open Aeneas Aeneas.Std Result Spec

private def runBatches {W B : Type} (run : List W → Slice B → Result (List W)) :
    List W → List (Slice B) → Result (List W)
  | st, [] => ok st
  | st, b :: bs => do
    let next ← run st b
    runBatches run next bs

private theorem batches_spec {W B : Type}
    (round : List W → B → List W) (run : List W → Slice B → Result (List W))
    (step : ∀ s (b : Slice B), s.length = 8 → run s b ⦃ out => out = b.val.foldl round s ⦄)
    (keep : ∀ s b, (round s b).length = 8)
    (st : List W) (hs : st.length = 8) (groups : List (Slice B)) :
    runBatches run st groups ⦃ out => out = (groups.flatMap (·.val)).foldl round st ⦄ := by
  have shape (s : List W) (oklen : s.length = 8) (xs : List B) :
      (xs.foldl round s).length = 8 := by
    induction xs generalizing s with
    | nil => exact oklen
    | cons b bs ih => exact ih _ (keep _ _)
  induction groups generalizing st with
  | nil => exact (WP.spec_ok _).mpr rfl
  | cons x xs ih =>
    unfold runBatches
    apply WP.spec_bind (step st x hs)
    intro out eq
    rw [eq]
    simpa only [List.flatMap_cons,List.foldl_append] using ih _ (shape st hs x.val)

def call256 (target : Provider) (st : List SHA256.Word) (b : Slice (Array U8 64#usize)) :=
  if h : st.length = 8 then
    run256 target (.from (st.map (fun w => ⟨w⟩ : SHA256.Word → U32)) (by simpa using h)) b
  else fail .panic

def call512 (target : Provider) (st : List SHA512.Word) (b : Slice (Array U8 128#usize)) :=
  if h : st.length = 8 then
    run512 target (.from (st.map (fun w => ⟨w⟩ : SHA512.Word → U64)) (by simpa using h)) b
  else fail .panic

private theorem call256_spec (target : Provider) (st : List SHA256.Word) (h : st.length=8)
    (b : Slice (Array U8 64#usize)) :
    call256 target st b ⦃ out => out = X86.Stream.fold256 st b.val ⦄ := by
  simp only [call256,dite_eq_left h]
  apply WP.spec_mono (run256_spec _ _ _)
  intro out eq; simpa [wv,List.map_map,Function.comp_def] using eq

private theorem call512_spec (target : Provider) (st : List SHA512.Word) (h : st.length=8)
    (b : Slice (Array U8 128#usize)) :
    call512 target st b ⦃ out => out = X86.Stream.fold512 st b.val ⦄ := by
  simp only [call512,dite_eq_left h]
  apply WP.spec_mono (run512_spec _ _ _)
  intro out eq; simpa [S512.wv,List.map_map,Function.comp_def] using eq

def finish256 (target : Provider) (groups : List (Slice (Array U8 64#usize))) : Result Bytes := do
  let out ← runBatches (call256 target) initial256 groups
  ok (out.flatMap (fun w => toByte w.toNat 4))

def finish512 (target : Provider) (groups : List (Slice (Array U8 128#usize))) : Result Bytes := do
  let out ← runBatches (call512 target) initial512 groups
  ok (out.flatMap (fun w => toByte w.toNat 8))

private theorem fold_map {A B S : Type} (convert : A → B) (f : S → B → S) (s : S) (xs : List A) :
    xs.foldl (fun state x => f state (convert x)) s = (xs.map convert).foldl f s :=
  List.foldl_map.symm

/-- Covers every partition of the padded input into valid Rust slices,
including empty updates and an odd leading SHA-512 block followed by AVX2 pairs. -/
theorem finish256_spec (target : Provider) (m : Bytes) (groups : List (Slice (Array U8 64#usize)))
    (partition : groups.flatMap (·.val) = blocks 64#usize (padded 64 8 m)) :
    finish256 target groups ⦃ out => out = digest256 m ⦄ := by
  apply WP.spec_bind (@batches_spec SHA256.Word (Array U8 64#usize)
    (fun st b => SHA256.compress st (bytes b.val)) (call256 target)
    (fun st b hs => call256_spec target st hs b) (fun _ _ => compress_length _ _)
    initial256 (by decide) groups)
  intro out eq
  apply (WP.spec_ok _).mpr
  rw [eq,partition,fold_map (fun b : Array U8 64#usize => bytes b.val) SHA256.compress,
    blocks_bytes,padded256,initial256_eq,digest256_eq]
  unfold SHA256.sha256
  rw [List.foldl_map]
  rfl

theorem finish512_spec (target : Provider) (m : Bytes) (groups : List (Slice (Array U8 128#usize)))
    (partition : groups.flatMap (·.val) = blocks 128#usize (padded 128 16 m)) :
    finish512 target groups ⦃ out => out = digest512 m ⦄ := by
  apply WP.spec_bind (@batches_spec SHA512.Word (Array U8 128#usize)
    (fun st b => SHA512.compress st (bytes b.val)) (call512 target)
    (fun st b hs => call512_spec target st hs b) (fun _ _ => compress512_length _ _)
    initial512 (by decide) groups)
  intro out eq
  apply (WP.spec_ok _).mpr
  rw [eq,partition,fold_map (fun b : Array U8 128#usize => bytes b.val) SHA512.compress,
    blocks_bytes,padded512,initial512_eq,digest512_eq]
  unfold SHA512.sha512
  rw [List.foldl_map]
  rfl

theorem finish256_raw (target : Provider) (m : Bytes) (groups : List (Slice (Array U8 64#usize)))
    (order : raw (groups.flatMap (·.val)) = padded 64 8 m) :
    finish256 target groups ⦃ out => out = digest256 m ⦄ := by
  apply finish256_spec _ _ _ (blocks_of_raw (by decide) _ _ _ order)
  apply Nat.dvd_of_mod_eq_zero
  rw [padded256, ← slhdsa.padFrom_zero]
  exact slhdsa.padFrom_length 0 m

theorem finish512_raw (target : Provider) (m : Bytes) (groups : List (Slice (Array U8 128#usize)))
    (order : raw (groups.flatMap (·.val)) = padded 128 16 m) :
    finish512 target groups ⦃ out => out = digest512 m ⦄ := by
  apply finish512_spec _ _ _ (blocks_of_raw (by decide) _ _ _ order)
  apply Nat.dvd_of_mod_eq_zero
  rw [padded512, ← S512.padFrom_zero]
  exact S512.padFrom_length 0 m

theorem fragmented256 (target : Provider) (parts : List Bytes) (groups : List (Slice (Array U8 64#usize)))
    (order : raw (groups.flatMap (·.val)) = (filled 64 parts).finalize 64 8) :
    finish256 target groups ⦃ out => out = digest256 parts.flatten ⦄ := by
  apply finish256_raw
  exact order.trans (finalized_parts _ _ (by decide) _)

theorem fragmented512 (target : Provider) (parts : List Bytes) (groups : List (Slice (Array U8 128#usize)))
    (order : raw (groups.flatMap (·.val)) = (filled 128 parts).finalize 128 16) :
    finish512 target groups ⦃ out => out = digest512 parts.flatten ⦄ := by
  apply finish512_raw
  exact order.trans (finalized_parts _ _ (by decide) _)

end slhdsa.RcSlhSha2

import RcSlhSha2.Proof
import Rcavx.Top
import Rcni.Top
import Rcsoft.Proof
import Rcsoft256.Proof

namespace slhdsa.RcSlhSha2
open Aeneas Aeneas.Std Result Spec

inductive Provider where
  | arm (apple : Bool) | x86 | software

/-- Each branch invokes the independently checked locked provider backend. -/
def run256 (target : Provider) (st : Array U32 8#usize) (bs : Slice (Array U8 64#usize)) :
    Result (List SHA256.Word) :=
  match target with
  | .arm apple => ok (RcArmCode.execute apple (wv st.val) bs.val)
  | .x86 => do let out ← RcNiRust.sha256.x86_sha.compress st bs; ok (wv out.val)
  | .software => do let out ← RcSoft256.sha256.soft.unroll.compress st bs; ok (wv out.val)

def run512 (target : Provider) (st : Array U64 8#usize) (bs : Slice (Array U8 128#usize)) :
    Result (List SHA512.Word) :=
  match target with
  | .arm apple => ok (RcArmCode.S512.execute apple (S512.wv st.val) bs.val)
  | .x86 => do let out ← RcAvxRust.sha512.x86_avx2.compress st bs; ok (S512.wv out.val)
  | .software => do let out ← RcSoft.sha512.soft.unroll.compress st bs; ok (S512.wv out.val)

theorem run256_spec (target : Provider) (st : Array U32 8#usize) (bs : Slice (Array U8 64#usize)) :
    run256 target st bs ⦃ out => out = X86.Stream.fold256 (wv st.val) bs.val ⦄ := by
  cases target with
  | arm apple => exact (WP.spec_ok _).mpr (RcArmCode.execute_is_fips apple bs.val _ (by simp))
  | x86 => unfold run256; step with Intel.RustCrypto.compress_spec as ⟨_,h⟩; exact h
  | software => unfold run256; step with RcSoft256Proof.execute_is_fips as ⟨_,h⟩; exact h

theorem run512_spec (target : Provider) (st : Array U64 8#usize) (bs : Slice (Array U8 128#usize)) :
    run512 target st bs ⦃ out => out = X86.Stream.fold512 (S512.wv st.val) bs.val ⦄ := by
  cases target with
  | arm apple => exact (WP.spec_ok _).mpr (RcArmCode.S512.execute_is_fips apple bs.val _)
  | x86 => unfold run512; step with X86.RustCrypto512.compress_spec as ⟨_,h⟩; exact h
  | software => unfold run512; step with RcSoftProof.execute_is_fips as ⟨_,h⟩; exact h

def pack {width : Usize} (bs : Bytes) (good : bs.length = width.val) : Array U8 width :=
  .from (bs.map fun b => ⟨b⟩) (by simpa using good)

theorem unpack {width : Usize} (bs : Bytes) (good : bs.length = width.val) :
    bytes (pack bs good).val = bs := by simp [pack,bytes,List.map_map,Function.comp_def]

/-- `p` can be any byte stream. Include just the complete blocks, in order. -/
def blocks (width : Usize) (p : Bytes) : List (Array U8 width) :=
  (List.range (p.length / width.val)).pmap (P := fun i => i < p.length / width.val)
    (fun i hi => pack ((p.drop (width.val*i)).take width.val) (by
      simp only [List.length_take,List.length_drop]
      apply Nat.min_eq_left
      have positive : 0 < width.val := Nat.pos_of_ne_zero (by rintro zero; simp [zero] at hi)
      have h := (Nat.le_div_iff_mul_le positive).mp (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul, Nat.mul_comm i width.val] at h
      omega))
    (fun _ h => List.mem_range.mp h)

theorem blocks_bytes (width : Usize) (p : Bytes) :
    (blocks width p).map (fun b => bytes b.val) =
      (List.range (p.length/width.val)).map (fun i => (p.drop (width.val*i)).take width.val) := by
  simp [blocks, List.map_pmap,unpack,List.pmap_eq_map]

end slhdsa.RcSlhSha2

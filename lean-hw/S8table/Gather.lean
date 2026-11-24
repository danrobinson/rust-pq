import S8table.Funs
import Digest256.Read
import Streamround.Schedule
open Aeneas Aeneas.Std Result
open core.core_arch.x86
open S8tableRust.core.core_arch.x86
namespace slhdsa.X86.Stream.Eight
open S512.Gather (flat flat_length)
set_option maxHeartbeats 2000000

abbrev control : __m256i := fun j => slhdsa.Intel.get ⟨0x00010203,0x04050607,0x08090a0b,0x0c0d0e0f⟩ j.val
def stride (v : __m256i) := ∀ j : Fin 8, (v j).toInt * 4 = (j.val*64 : Nat)

theorem shuffle (v : __m256i) : avx2._mm256_shuffle_epi8 v control ⦃ r => ∀ j, r j = Store.reverse32 (v j) ⦄ := by
  simp only [avx2._mm256_shuffle_epi8,step_simps]
  intro j
  fin_cases j <;> rfl

theorem gathered (blocks : Array (Array U8 64#usize) 8#usize) (v : __m256i) (hs : stride v)
    (k : Nat) (hk : k < 16) :
    (do let x ← avx2._mm256_i32gather_epi32 4#i32 ⟨flat blocks.val,4*k⟩ v
        avx2._mm256_shuffle_epi8 x control)
      ⦃ r => ∀ j, r j = (Spec.SHA256.schedule (bytes blocks.val[j.val]!.val))[k]! ⦄ := by
  let p : GatherRust.ReadPtr I32 := ⟨flat blocks.val,4*k⟩
  have addr (j : Fin 8) : address p 4#i32 v j = (j.val*64+4*k : Nat) := by
    change ((4*k : Nat) : Int) + 4*(v j).toInt = _
    rw [Int.mul_comm,hs j]; omega
  have total : (flat blocks.val).length = 512 := by rw [flat_length]; simp
  have safe (j : Fin 8) : 0 ≤ address p 4#i32 v j ∧ address p 4#i32 v j + 4 ≤ (p.allocation.length : Int) := by
    rw [addr]; change _ ∧ _ ≤ ((flat blocks.val).length : Int); rw [total]; have := j.isLt; omega
  change (do let x ← avx2._mm256_i32gather_epi32 4#i32 p v; avx2._mm256_shuffle_epi8 x control) ⦃ _ => _ ⦄
  unfold avx2._mm256_i32gather_epi32
  rw [if_pos ⟨by decide,safe⟩]; simp only [bind_ok]
  step with shuffle as ⟨out,rev⟩
  rename_i j
  have endpos : j.val*64+4*k+4 ≤ (flat blocks.val).length := by rw [total]; have := j.isLt; omega
  rw [rev,addr,Int.toNat_natCast,Digest.big_after_little _ _ endpos,slhdsa.schedule_lt16 _ _ hk]
  exact Digest.flat_word blocks.val j.val _ (by simpa using j.isLt) (by change 4*k+4 ≤ 64; omega)
end slhdsa.X86.Stream.Eight

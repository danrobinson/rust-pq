import S8table.Initial
import Streamscalar.Ordered
open Aeneas Aeneas.Std Result
open core.core_arch.x86
namespace slhdsa.X86.Stream.Eight
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000

private theorem literalAdd (a b : Usize) (h : a.val+b.val ≤ 64) :
    a+b = ok (UScalar.ofNat (a.val+b.val) (by change _ ≤ 4294967295; omega) : Usize) := by
  obtain ⟨v,eq,val⟩ := spec_imp_exists (Usize.add_spec (x := a) (y := b) (by scalar_tac))
  rw [eq]; congr 1; exact UScalar.eq_of_val_eq val

theorem table_fips (blocks : Array (Array U8 64#usize) 8#usize) :
    S8tableRust.sha256.stream.schedule blocks ⦃ out => ordered256 out blocks 64 ⦄ := by
  have rows : ordered256 (Array.repeat 64#usize (Array.repeat 8#usize 0#u32)) blocks 0 :=
    fun i h => False.elim (Nat.not_lt_zero i h)
  have offset_spec : avx._mm256_set_epi32 112#i32 96#i32 80#i32 64#i32 48#i32 32#i32 16#i32 0#i32
      ⦃ out => stride out ⦄ := by
    unfold avx._mm256_set_epi32
    apply (WP.spec_ok _).mpr
    intro j
    fin_cases j <;> decide
  have swap_spec : (do let x ← sse2._mm_set_epi32 202182159#i32 134810123#i32 67438087#i32 66051#i32
                       S8tableRust.core.core_arch.x86.avx2._mm256_broadcastsi128_si256 x) = ok control := by
    simp only [sse2._mm_set_epi32,S8tableRust.core.core_arch.x86.avx2._mm256_broadcastsi128_si256,bind_ok]
    congr 1
  unfold S8tableRust.sha256.stream.schedule
  step with offset_spec as ⟨offsets,hs⟩
  rw [← Std.bind_assoc,swap_spec]
  simp (config := {maxSteps := 500000}) (disch := decide) only [bind_ok,
    show 0#usize + 1#usize = ok 1#usize from literalAdd _ _ (by decide),
    show 0#usize + 2#usize = ok 2#usize from literalAdd _ _ (by decide),
    show 0#usize + 3#usize = ok 3#usize from literalAdd _ _ (by decide),
    show 0#usize + 4#usize = ok 4#usize from literalAdd _ _ (by decide),
    show 0#usize + 5#usize = ok 5#usize from literalAdd _ _ (by decide),
    show 0#usize + 6#usize = ok 6#usize from literalAdd _ _ (by decide),
    show 0#usize + 7#usize = ok 7#usize from literalAdd _ _ (by decide),
    show 8#usize + 1#usize = ok 9#usize from literalAdd _ _ (by decide),
    show 8#usize + 2#usize = ok 10#usize from literalAdd _ _ (by decide),
    show 8#usize + 3#usize = ok 11#usize from literalAdd _ _ (by decide),
    show 8#usize + 4#usize = ok 12#usize from literalAdd _ _ (by decide),
    show 8#usize + 5#usize = ok 13#usize from literalAdd _ _ (by decide),
    show 8#usize + 6#usize = ok 14#usize from literalAdd _ _ (by decide),
    show 8#usize + 7#usize = ok 15#usize from literalAdd _ _ (by decide),
    show 16#usize + 1#usize = ok 17#usize from literalAdd _ _ (by decide),
    show 16#usize + 2#usize = ok 18#usize from literalAdd _ _ (by decide),
    show 16#usize + 3#usize = ok 19#usize from literalAdd _ _ (by decide),
    show 16#usize + 4#usize = ok 20#usize from literalAdd _ _ (by decide),
    show 16#usize + 5#usize = ok 21#usize from literalAdd _ _ (by decide),
    show 16#usize + 6#usize = ok 22#usize from literalAdd _ _ (by decide),
    show 16#usize + 7#usize = ok 23#usize from literalAdd _ _ (by decide),
    show 24#usize + 1#usize = ok 25#usize from literalAdd _ _ (by decide),
    show 24#usize + 2#usize = ok 26#usize from literalAdd _ _ (by decide),
    show 24#usize + 3#usize = ok 27#usize from literalAdd _ _ (by decide),
    show 24#usize + 4#usize = ok 28#usize from literalAdd _ _ (by decide),
    show 24#usize + 5#usize = ok 29#usize from literalAdd _ _ (by decide),
    show 24#usize + 6#usize = ok 30#usize from literalAdd _ _ (by decide),
    show 24#usize + 7#usize = ok 31#usize from literalAdd _ _ (by decide),
    show 32#usize + 1#usize = ok 33#usize from literalAdd _ _ (by decide),
    show 32#usize + 2#usize = ok 34#usize from literalAdd _ _ (by decide),
    show 32#usize + 3#usize = ok 35#usize from literalAdd _ _ (by decide),
    show 32#usize + 4#usize = ok 36#usize from literalAdd _ _ (by decide),
    show 32#usize + 5#usize = ok 37#usize from literalAdd _ _ (by decide),
    show 32#usize + 6#usize = ok 38#usize from literalAdd _ _ (by decide),
    show 32#usize + 7#usize = ok 39#usize from literalAdd _ _ (by decide),
    show 40#usize + 1#usize = ok 41#usize from literalAdd _ _ (by decide),
    show 40#usize + 2#usize = ok 42#usize from literalAdd _ _ (by decide),
    show 40#usize + 3#usize = ok 43#usize from literalAdd _ _ (by decide),
    show 40#usize + 4#usize = ok 44#usize from literalAdd _ _ (by decide),
    show 40#usize + 5#usize = ok 45#usize from literalAdd _ _ (by decide),
    show 40#usize + 6#usize = ok 46#usize from literalAdd _ _ (by decide),
    show 40#usize + 7#usize = ok 47#usize from literalAdd _ _ (by decide),
    show 48#usize + 1#usize = ok 49#usize from literalAdd _ _ (by decide),
    show 48#usize + 2#usize = ok 50#usize from literalAdd _ _ (by decide),
    show 48#usize + 3#usize = ok 51#usize from literalAdd _ _ (by decide),
    show 48#usize + 4#usize = ok 52#usize from literalAdd _ _ (by decide),
    show 48#usize + 5#usize = ok 53#usize from literalAdd _ _ (by decide),
    show 48#usize + 6#usize = ok 54#usize from literalAdd _ _ (by decide),
    show 48#usize + 7#usize = ok 55#usize from literalAdd _ _ (by decide),
    show 56#usize + 1#usize = ok 57#usize from literalAdd _ _ (by decide),
    show 56#usize + 2#usize = ok 58#usize from literalAdd _ _ (by decide),
    show 56#usize + 3#usize = ok 59#usize from literalAdd _ _ (by decide),
    show 56#usize + 4#usize = ok 60#usize from literalAdd _ _ (by decide),
    show 56#usize + 5#usize = ok 61#usize from literalAdd _ _ (by decide),
    show 56#usize + 6#usize = ok 62#usize from literalAdd _ _ (by decide),
    show 56#usize + 7#usize = ok 63#usize from literalAdd _ _ (by decide)]
  step with initial blocks offsets hs as ⟨w,window⟩
  iterate 63
    apply WP.spec_bind (expand_fips _ _ blocks (by decide) (by assumption))
    rintro ⟨win,row⟩ ⟨window,h⟩
    apply WP.spec_bind (Array.update_spec _ _ _ (by simp <;> decide))
    intro table write
    have rows' := write_ordered256 _ blocks _ row (by decide) (by assumption) (fun j hj => h ⟨j,hj⟩)
    rw [← write] at rows'
  apply WP.spec_bind (expand_fips 63#usize _ blocks (by decide) (by assumption))
  rintro ⟨win,row⟩ ⟨_,h⟩
  apply WP.spec_mono (Array.update_spec _ 63#usize row (by simp))
  intro table write
  rw [write]
  exact write_ordered256 _ blocks 63#usize row (by decide) (by assumption) (fun j hj => h ⟨j,hj⟩)
end slhdsa.X86.Stream.Eight

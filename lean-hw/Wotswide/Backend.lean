import Wotswide.Digest
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots.Wide

theorem same256 (buf : Array U8 640#usize) (total : Usize) (st : Array U32 8#usize)
    (aligned : total.val%64 = 0) (size : total.val ≤ 640) :
    WotsWideRust.hash.thash_values_loop1 buf total st 0#usize =
      slhdsa.hash.thash_values_loop1 buf total st 0#usize := by
  obtain ⟨x,hx,sx⟩ := spec_imp_exists (digest256 buf total (slhdsa.wv st.val) st 0#usize aligned size (by simp) (by simp) (by simp))
  obtain ⟨y,hy,sy⟩ := spec_imp_exists (slhdsa.thash_values_loop1_spec buf total (slhdsa.wv st.val) st 0#usize aligned size (by simp) (by simp) (by simp))
  rw [hx,hy]
  congr 1
  apply Aeneas.Std.Array.ext
  have words := congrArg (List.map (fun v : BitVec 32 => (⟨v⟩ : U32))) (sx.trans sy.symm)
  simpa [slhdsa.wv,List.map_map,Function.comp_def] using words

theorem same512 (buf : Array U8 2304#usize) (total : Usize) (st : Array U64 8#usize)
    (aligned : total.val%128 = 0) (size : total.val ≤ 2304) :
    WotsWideRust.hash.thash_values_loop3 buf total st 0#usize =
      slhdsa.hash.thash_values_loop3 buf total st 0#usize := by
  obtain ⟨x,hx,sx⟩ := spec_imp_exists (digest512 buf total (slhdsa.S512.wv st.val) st 0#usize aligned size (by simp) (by simp) (by simp))
  obtain ⟨y,hy,sy⟩ := spec_imp_exists (slhdsa.thash_values_loop3_spec buf total (slhdsa.S512.wv st.val) st 0#usize aligned size (by simp) (by simp) (by simp))
  rw [hx,hy]
  congr 1
  apply Aeneas.Std.Array.ext
  have words := congrArg (List.map (fun v : BitVec 64 => (⟨v⟩ : U64))) (sx.trans sy.symm)
  simpa [slhdsa.S512.wv,List.map_map,Function.comp_def] using words

end slhdsa.X86.Wots.Wide

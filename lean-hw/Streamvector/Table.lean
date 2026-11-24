import Streamvector.Initial
import Streamscalar.Ordered
open Aeneas Aeneas.Std Result
open core.core_arch.x86.avx512f
namespace slhdsa.X86.Stream
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem reorder {n} (a b c d : BitVec n) : a+b+(c+d)=b+d+a+c := by ac_rfl

private abbrev Words32 := Array U32 16#usize
private abbrev Words64 := Array U64 8#usize

private theorem cast32 (v : Reg) (j : Fin 16) :
    (LaneRepr.castBits v : Words32).val[j.val]!.bv = v j := by
  have eq : (LaneRepr.castBits v : Words32).val = List.ofFn (fun j : Fin 16 => (⟨v j⟩ : U32)) := Array.from_val _ _
  rw [eq,List.getElem!_ofFn _ j.val j.isLt]

private theorem cast64 (v : Reg) (j : Fin 8) :
    (LaneRepr.castBits v : Words64).val[j.val]!.bv = word64 v j := by
  have eq : (LaneRepr.castBits v : Words64).val = List.ofFn (fun j : Fin 8 => (⟨word64 v j⟩ : U64)) := Array.from_val _ _
  rw [eq,List.getElem!_ofFn _ j.val j.isLt]

private theorem setSame {α} [Inhabited α] (xs : List α) (i : Nat) (x : α) (hi : i < xs.length) :
    (xs.set i x)[i]! = x := by simp [hi]
private theorem setOther {α} [Inhabited α] (xs : List α) (i k : Nat) (x : α) (hne : i ≠ k) :
    (xs.set i x)[k]! = xs[k]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hne]

open Spec.SHA256 in
theorem scheduleBody256 (it next : core.ops.range.Range Usize) (i : Usize)
    (w : Array Reg 16#usize) (table : Array (Array U32 16#usize) 64#usize)
    (blocks : Array (Array U8 64#usize) 16#usize) (ht : i.val < 64)
    (more : core.iter.range.IteratorRange.next core.iter.range.StepUsize it = ok (some i,next))
    (old : vectorWindow256 w blocks i.val) (prior : ordered256 table blocks i.val) :
    StreamVectorRust.sha256.stream.prescheduled_loop0_loop0.body it table w ⦃ flow => ∃ table' w',
      flow = ControlFlow.cont (next,table',w') ∧ vectorWindow256 w' blocks (i.val+1) ∧
      ordered256 table' blocks (i.val+1) ⦄ := by
  let W := fun j : Fin 16 => schedule (bytes blocks.val[j.val]!.val)
  have hr : Ring w W i.val := fun k lo hi j => old j k lo hi
  have recurrence (k : Nat) (lo : 16 ≤ k) (hi : k < 64) (j : Fin 16) : (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! + ssig0 (W j)[k-15]! + (W j)[k-16]! := slhdsa.schedule_rec (bytes blocks.val[j.val]!.val) k lo hi
  unfold StreamVectorRust.sha256.stream.prescheduled_loop0_loop0.body
  rw [more]
  simp only [bind_ok]
  apply WP.spec_bind (Pₘ := fun r => Ring r W (i.val+1) ∧ ∀ j, r.val[i.val%16]! j = (W j)[i.val]!)
  · split
    · rename_i hi
      have late : 16 ≤ i.val := by scalar_tac
      simp only [_mm512_ror_epi32, _mm512_srli_epi32, _mm512_ternarylogic_epi32,
        _mm512_add_epi32, bind_ok]
      step*
      have readSlot (v : Reg) (idx : Usize) (k : Nat) (ev : v = w.val[idx.val]!)
          (ei : idx.val = k % 16) (hlo : i.val - 16 ≤ k) (hk : k < i.val) (j : Fin 16) :
          v j = (W j)[k]! := by rw [ev, ei]; exact hr k hlo (by omega) j
      have hx := readSlot x i2 (i.val-15) (by rw [getElem!_pos w.val i2.val (by scalar_tac)]; exact x_post) (by omega) (by omega) (by omega)
      have hy := readSlot y i4 (i.val-2) (by rw [getElem!_pos w.val i4.val (by scalar_tac)]; exact y_post) (by omega) (by omega) (by omega)
      have h16 := readSlot mi7 i5 (i.val-16) (by rw [getElem!_pos w.val i5.val (by scalar_tac)]; exact mi7_post) (by omega) (by omega) (by omega)
      have h7 := readSlot mi8 i7 (i.val-7) (by rw [getElem!_pos w.val i7.val (by scalar_tac)]; exact mi8_post) (by omega) (by omega) (by omega)
      have hn : ∀ j, r.val[i.val%16]! j = (W j)[i.val]! := by
        intro j
        rw [r_post, Array.set_val_eq, i5_post]
        have bound : i.val % 16 < w.val.length := by simp; omega
        rw [setSame _ _ _ bound]
        rw [recurrence _ late ht j]
        simp only [show (150#i32).bv.toNat % 256 = 150 by decide,
          show (7#i32).bv.toNat % 32 = 7 by decide,
          show (18#i32).bv.toNat % 32 = 18 by decide,
          show (17#i32).bv.toNat % 32 = 17 by decide,
          show (19#i32).bv.toNat % 32 = 19 by decide,
          show (3#u32).bv.toNat % 256 = 3 by decide,
          show (10#u32).bv.toNat % 256 = 10 by decide, xor3, hx, hy, h16, h7, ssig0, ssig1]
        exact reorder _ _ _ _
      refine ⟨?_, hn⟩
      intro k hlo hhi j
      by_cases he : k = i.val
      · subst k; exact hn j
      · have hnslot : i5.val ≠ k%16 := by omega
        rw [r_post, Array.set_val_eq]
        rw [setOther _ _ _ _ hnslot]
        exact hr k (by omega) (by omega) j
    · rename_i hi
      have late : i.val < 16 := by scalar_tac
      simp only [step_simps]
      refine ⟨?_, hr i.val (by omega) (by omega)⟩
      intro k hlo hhi j
      exact hr k (by omega) (by omega) j
  · rintro r ⟨ring,word⟩
    simp only [_mm512_set1_epi32,_mm512_add_epi32,lift,bind_ok,core.intrinsics.transmute]
    step as ⟨idx,hi⟩
    step as ⟨v,hv⟩
    step as ⟨key,hk⟩
    have keyEq : key.bv = Spec.SHA256.K[i.val]! := by
      have same : StreamVectorRust.sha256.K = slhdsa.sha256.K := by unfold StreamVectorRust.sha256.K slhdsa.sha256.K; rfl
      rw [hk,same,← slhdsa.K_eq,slhdsa.wv_getElem! _ _ (by simpa using ht)]
    step as ⟨table',write⟩
    refine ⟨table',r,rfl,fun j k lo hi => ring k lo hi j,?_⟩
    rw [write]
    apply write_ordered256 table blocks i _ ht prior
    intro lane bound
    let j : Fin 16 := ⟨lane,bound⟩
    have read := word j
    rw [← hi,getElem!_pos _ _ (by scalar_tac),← hv] at read
    change _ = Spec.SHA256.K[i.val]! + (W j)[i.val]!
    rw [← keyEq,← read]
    rw [cast32 _ j]
    exact BitVec.add_comm _ _


open Spec.SHA512 in
theorem scheduleBody512 (it next : core.ops.range.Range Usize) (i : Usize)
    (w : Array Reg 16#usize) (table : Array (Array U64 8#usize) 80#usize)
    (blocks : Array (Array U8 128#usize) 8#usize) (ht : i.val < 80)
    (more : core.iter.range.IteratorRange.next core.iter.range.StepUsize it = ok (some i,next))
    (old : vectorWindow512 w blocks i.val) (prior : ordered512 table blocks i.val) :
    StreamVectorRust.sha512.stream.prescheduled_loop0_loop0.body it table w ⦃ flow => ∃ table' w',
      flow = ControlFlow.cont (next,table',w') ∧ vectorWindow512 w' blocks (i.val+1) ∧
      ordered512 table' blocks (i.val+1) ⦄ := by
  let W := fun j : Fin 8 => schedule (bytes blocks.val[j.val]!.val)
  have hr : S512.Ring w W i.val := fun k lo hi j => old j k lo hi
  have recurrence (k : Nat) (lo : 16 ≤ k) (hi : k < 80) (j : Fin 8) : (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! + ssig0 (W j)[k-15]! + (W j)[k-16]! := slhdsa.H512.schedule_rec (bytes blocks.val[j.val]!.val) k lo hi
  unfold StreamVectorRust.sha512.stream.prescheduled_loop0_loop0.body
  rw [more]
  simp only [bind_ok]
  apply WP.spec_bind (Pₘ := fun r => S512.Ring r W (i.val+1) ∧ ∀ j, word64 r.val[i.val%16]! j = (W j)[i.val]!)
  · split
    · rename_i hi
      have late : 16 ≤ i.val := by scalar_tac
      simp only [_mm512_ror_epi64, _mm512_srli_epi64, _mm512_ternarylogic_epi64,
        _mm512_add_epi64, bind_ok]
      step*
      have readSlot (v : Reg) (idx : Usize) (k : Nat) (ev : v = w.val[idx.val]!)
          (ei : idx.val = k % 16) (hlo : i.val - 16 ≤ k) (hk : k < i.val) (j : Fin 8) :
          word64 v j = (W j)[k]! := by rw [ev, ei]; exact hr k hlo (by omega) j
      have hx := readSlot x i2 (i.val-15) (by rw [getElem!_pos w.val i2.val (by scalar_tac)]; exact x_post) (by omega) (by omega) (by omega)
      have hy := readSlot y i4 (i.val-2) (by rw [getElem!_pos w.val i4.val (by scalar_tac)]; exact y_post) (by omega) (by omega) (by omega)
      have h16 := readSlot mi7 i5 (i.val-16) (by rw [getElem!_pos w.val i5.val (by scalar_tac)]; exact mi7_post) (by omega) (by omega) (by omega)
      have h7 := readSlot mi8 i7 (i.val-7) (by rw [getElem!_pos w.val i7.val (by scalar_tac)]; exact mi8_post) (by omega) (by omega) (by omega)
      have hn : ∀ j, word64 r.val[i.val%16]! j = (W j)[i.val]! := by
        intro j
        rw [r_post, Array.set_val_eq, i5_post]
        have bound : i.val % 16 < w.val.length := by simp; omega
        rw [setSame _ _ _ bound]
        rw [recurrence _ late ht j]
        simp only [show (150#i32).bv.toNat % 256 = 150 by decide,
          show (1#i32).bv.toNat % 64 = 1 by decide,
          show (8#i32).bv.toNat % 64 = 8 by decide,
          show (19#i32).bv.toNat % 64 = 19 by decide,
          show (61#i32).bv.toNat % 64 = 61 by decide,
          show (7#u32).bv.toNat % 256 = 7 by decide,
          show (6#u32).bv.toNat % 256 = 6 by decide, word64_ofWords64, xor3, hx, hy, h16, h7, ssig0, ssig1]
        exact reorder _ _ _ _
      refine ⟨?_, hn⟩
      intro k hlo hhi j
      by_cases he : k = i.val
      · subst k; exact hn j
      · have hnslot : i5.val ≠ k%16 := by omega
        rw [r_post, Array.set_val_eq]
        rw [setOther _ _ _ _ hnslot]
        exact hr k (by omega) (by omega) j
    · rename_i hi
      have late : i.val < 16 := by scalar_tac
      simp only [step_simps]
      refine ⟨?_, hr i.val (by omega) (by omega)⟩
      intro k hlo hhi j
      exact hr k (by omega) (by omega) j
  · rintro r ⟨ring,word⟩
    simp only [_mm512_set1_epi64,_mm512_add_epi64,lift,bind_ok,core.intrinsics.transmute]
    step as ⟨idx,hi⟩
    step as ⟨v,hv⟩
    step as ⟨key,hk⟩
    have keyEq : key.bv = Spec.SHA512.K[i.val]! := by
      have same : StreamVectorRust.sha512.K = slhdsa.sha512.K := by unfold StreamVectorRust.sha512.K slhdsa.sha512.K; rfl
      rw [hk,same,← slhdsa.S512.K_eq,slhdsa.S512.wv_getElem! _ _ (by simpa using ht)]
    step as ⟨table',write⟩
    refine ⟨table',r,rfl,fun j k lo hi => ring k lo hi j,?_⟩
    rw [write]
    apply write_ordered512 table blocks i _ ht prior
    intro lane bound
    let j : Fin 8 := ⟨lane,bound⟩
    have read := word j
    rw [← hi,getElem!_pos _ _ (by scalar_tac),← hv] at read
    change _ = Spec.SHA512.K[i.val]! + (W j)[i.val]!
    rw [← keyEq,← read]
    rw [cast64 _ j]
    simp only [word64_ofWords64]
    exact BitVec.add_comm _ _


open Spec.SHA512 in
theorem scheduleWord512 (i : Usize) (w : Array Reg 16#usize)
    (blocks : Array (Array U8 128#usize) 8#usize) (ht : i.val < 80)
    (old : vectorWindow512 w blocks i.val) :
    StreamVectorRust.sha512.stream.schedule_word w i ⦃ out =>
      vectorWindow512 out.2 blocks (i.val+1) ∧
      ∀ lane, lane < 8 → out.1.val[lane]!.bv =
        Spec.SHA512.K[i.val]! + (schedule (bytes blocks.val[lane]!.val))[i.val]! ⦄ := by
  let W := fun j : Fin 8 => schedule (bytes blocks.val[j.val]!.val)
  have hr : S512.Ring w W i.val := fun k lo hi j => old j k lo hi
  have recurrence (k : Nat) (lo : 16 ≤ k) (hi : k < 80) (j : Fin 8) : (W j)[k]! = ssig1 (W j)[k-2]! + (W j)[k-7]! + ssig0 (W j)[k-15]! + (W j)[k-16]! := slhdsa.H512.schedule_rec (bytes blocks.val[j.val]!.val) k lo hi
  unfold StreamVectorRust.sha512.stream.schedule_word
  apply WP.spec_bind (Pₘ := fun r => S512.Ring r W (i.val+1) ∧ ∀ j, word64 r.val[i.val%16]! j = (W j)[i.val]!)
  · split
    · rename_i hi
      have late : 16 ≤ i.val := by scalar_tac
      simp only [_mm512_ror_epi64, _mm512_srli_epi64, _mm512_ternarylogic_epi64,
        _mm512_add_epi64, bind_ok]
      step*
      have readSlot (v : Reg) (idx : Usize) (k : Nat) (ev : v = w.val[idx.val]!)
          (ei : idx.val = k % 16) (hlo : i.val - 16 ≤ k) (hk : k < i.val) (j : Fin 8) :
          word64 v j = (W j)[k]! := by rw [ev, ei]; exact hr k hlo (by omega) j
      have hx := readSlot x i2 (i.val-15) (by rw [getElem!_pos w.val i2.val (by scalar_tac)]; exact x_post) (by omega) (by omega) (by omega)
      have hy := readSlot y i4 (i.val-2) (by rw [getElem!_pos w.val i4.val (by scalar_tac)]; exact y_post) (by omega) (by omega) (by omega)
      have h16 := readSlot mi7 i5 (i.val-16) (by rw [getElem!_pos w.val i5.val (by scalar_tac)]; exact mi7_post) (by omega) (by omega) (by omega)
      have h7 := readSlot mi8 i7 (i.val-7) (by rw [getElem!_pos w.val i7.val (by scalar_tac)]; exact mi8_post) (by omega) (by omega) (by omega)
      have hn : ∀ j, word64 r.val[i.val%16]! j = (W j)[i.val]! := by
        intro j
        rw [r_post, Array.set_val_eq, i5_post]
        have bound : i.val % 16 < w.val.length := by simp; omega
        rw [setSame _ _ _ bound]
        rw [recurrence _ late ht j]
        simp only [show (150#i32).bv.toNat % 256 = 150 by decide,
          show (1#i32).bv.toNat % 64 = 1 by decide,
          show (8#i32).bv.toNat % 64 = 8 by decide,
          show (19#i32).bv.toNat % 64 = 19 by decide,
          show (61#i32).bv.toNat % 64 = 61 by decide,
          show (7#u32).bv.toNat % 256 = 7 by decide,
          show (6#u32).bv.toNat % 256 = 6 by decide, word64_ofWords64, xor3, hx, hy, h16, h7, ssig0, ssig1]
        exact reorder _ _ _ _
      refine ⟨?_, hn⟩
      intro k hlo hhi j
      by_cases he : k = i.val
      · subst k; exact hn j
      · have hnslot : i5.val ≠ k%16 := by omega
        rw [r_post, Array.set_val_eq]
        rw [setOther _ _ _ _ hnslot]
        exact hr k (by omega) (by omega) j
    · rename_i hi
      have late : i.val < 16 := by scalar_tac
      simp only [step_simps]
      refine ⟨?_, hr i.val (by omega) (by omega)⟩
      intro k hlo hhi j
      exact hr k (by omega) (by omega) j
  · rintro r ⟨ring,word⟩
    simp only [_mm512_set1_epi64,_mm512_add_epi64,lift,bind_ok,core.intrinsics.transmute]
    step as ⟨idx,hi⟩
    step as ⟨v,hv⟩
    step as ⟨key,hk⟩
    have keyEq : key.bv = Spec.SHA512.K[i.val]! := by
      have same : StreamVectorRust.sha512.K = slhdsa.sha512.K := by unfold StreamVectorRust.sha512.K slhdsa.sha512.K; rfl
      rw [hk,same,← slhdsa.S512.K_eq,slhdsa.S512.wv_getElem! _ _ (by simpa using ht)]
    refine ⟨fun j k lo hi => ring k lo hi j,?_⟩
    intro lane bound
    let j : Fin 8 := ⟨lane,bound⟩
    have read := word j
    rw [← hi,getElem!_pos _ _ (by scalar_tac),← hv] at read
    change _ = Spec.SHA512.K[i.val]! + (W j)[i.val]!
    rw [← keyEq,← read]
    rw [cast64 _ j]
    simp only [word64_ofWords64]
    exact BitVec.add_comm _ _


end slhdsa.X86.Stream

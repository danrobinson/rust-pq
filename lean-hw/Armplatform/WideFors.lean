import Armplatform.WideForsProgram
import Slhdsa.Proofs.Slh

open Aeneas Aeneas.Std Result
namespace slhdsa.WideFors

/-- The native stack loop computes the absolute FIPS tree index for each active row. -/
theorem absolute_indices (a : U32) (k : Usize) (raw idx : Array U32 35#usize)
    (ha : a.val ≤ 14) (hk : k.val ≤ 35) (hd : ∀ j < k.val, (raw.val[j]!).val < 2 ^ a.val) :
    fors.arm.pk_from_sig_loop0 ⟨0#usize,k⟩ a raw idx ⦃ out =>
      ∀ j < k.val, (out.val[j]!).val = j * 2 ^ a.val + (raw.val[j]!).val ⦄ := by
  unfold fors.arm.pk_from_sig_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.Range Usize × Array U32 35#usize => k.val - q.1.start.val)
    (inv := fun q => q.1.end = k ∧ q.1.start.val ≤ k.val ∧
      ∀ j < q.1.start.val, (q.2.val[j]!).val = j * 2 ^ a.val + (raw.val[j]!).val)
  · rintro ⟨it,acc⟩ ⟨he,hi,hacc⟩
    simp only at he hi hacc
    unfold fors.arm.pk_from_sig_loop0.body
    by_cases live : it.start.val < it.end.val
    · have hj : it.start.val < k.val := he ▸ live
      obtain ⟨shift, bound⟩ := fors_shl_arith _ _ ha (by omega : it.start.val < 35)
      step with core.iter.range.IteratorRange.next_Usize_some_spec it live as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step as ⟨i1, hc⟩
      have hc' : i1.val = it.start.val := by rw [hc]; exact cast_u32_usize_val _ (by omega)
      step as ⟨i2, hs, _⟩
      have hs' : i2.val = it.start.val * 2 ^ a.val := by
        rw [hs,hc']; simpa [U32.size,U32.numBits] using shift
      step as ⟨digit,hr⟩
      have hraw : raw.val[it.start.val]! = digit := by simp (disch := scalar_tac) [hr,getElem!_pos]
      have hdigit := hd _ hj
      rw [hraw] at hdigit
      step as ⟨n,hn'⟩
      step as ⟨out,hw⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro j hj'
      rw [hw, Array.set_val_eq]
      by_cases eq : j = it.start.val
      · subst j
        simp (disch := scalar_tac) [List.getElem!_eq_getElem?_getD, List.getElem?_set_self,hn',hs',hraw,hr]
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
        simpa [List.getElem!_eq_getElem?_getD] using hacc j (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,nxt,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = k.val := by rw [he] at live; omega
      simpa only [eq] using hacc
  · simp

/-- The stack buffer keeps the compressed-address prefix and unwritten suffix byte-for-byte. -/
def packed {N B : Usize} (rows : Array (Array U8 N) 35#usize)
    (buf : Array U8 B) (i : Nat) :=
  buf.val.take 22 ++ (List.range i).flatMap (fun j => rows.val[j]!.val) ++ buf.val.drop (22 + N.val*i)

private theorem flat_length {N : Usize} (rows : Array (Array U8 N) 35#usize) (i : Nat) :
    ((List.range i).flatMap (fun j => rows.val[j]!.val)).length = N.val*i := by
  induction i with
  | zero => simp
  | succ i ih => simp [List.range_succ, ih, Nat.mul_succ, Nat.mul_comm]

theorem pack_roots {N B : Usize} (k : Usize) (rows : Array (Array U8 N) 35#usize) (buf : Array U8 B)
    (hk : k.val ≤ 35) (room : 22 + N.val*k.val ≤ B.val) :
    packRoots ⟨0#usize,k⟩ rows buf ⦃ out => out.val = packed rows buf k.val ⦄ := by
  unfold packRoots
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.Range Usize × Array U8 B => k.val - q.1.start.val)
    (inv := fun q => q.1.end = k ∧ q.1.start.val ≤ k.val ∧ q.2.val = packed rows buf q.1.start.val)
  · rintro ⟨it,acc⟩ ⟨he,hi,hw⟩
    simp only at he hi hw
    unfold packRoots.body
    by_cases live : it.start.val < it.end.val
    · have hj : it.start.val < k.val := he ▸ live
      have room' : 22 + N.val*(it.start.val+1) ≤ B.val := by
        have := Nat.mul_le_mul_left N.val (show it.start.val+1 ≤ k.val by omega)
        omega
      have hb := B.hBounds
      have hl := Nat.mul_le_mul_left N.val (show it.start.val ≤ it.start.val+1 by omega)
      step with core.iter.range.IteratorRange.next_Usize_some_spec it live as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step*
      all_goals try scalar_tac
      · rw [s_post1, s1_post]; simp; rw [i5_post, i4_post, i3_post, i2_post, i1_post, Nat.mul_succ]; omega
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      rw [s_post2, s2_post, s1_post, a_post, i2_post, i1_post, hw]
      rw [hn]
      unfold packed
      have hlen : (buf.val.take 22 ++ (List.range it.start.val).flatMap (fun j => rows.val[j]!.val)).length =
          22 + N.val*it.start.val := by simp [flat_length, Nat.mul_comm, min_eq_left (show 22 ≤ B.val by omega)]
      rw [setSlice_gen _ _ _ _ hlen.symm (by simp; rw [Nat.mul_succ] at room'; omega)]
      simp (disch := scalar_tac) [List.range_succ, List.drop_drop,Nat.mul_succ,List.append_assoc,
        getElem!_pos, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      rw [Nat.add_comm 1 it.start.val, List.range_succ, Nat.mul_succ]
      simp (disch := scalar_tac) [List.append_assoc, getElem!_pos, Nat.add_comm]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,nxt,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = k.val := by rw [he] at live; omega
      simpa only [eq] using hw
  · simp [packed]

theorem pack_roots_sha256 (k : Usize) (rows : Array (Array U8 16#usize) 35#usize) (buf : Array U8 640#usize)
    (hk : k.val ≤ 35) :
    fors.arm.pk_from_sig_loop2 ⟨0#usize,k⟩ rows buf ⦃ out => out.val = packed rows buf k.val ⦄ :=
  pack_roots k rows buf hk (by scalar_tac)

theorem pack_roots_sha512 {N : Usize} (k : Usize) (rows : Array (Array U8 N) 35#usize) (buf : Array U8 1280#usize)
    (hk : k.val ≤ 35) (hn : N.val ≤ 32) :
    fors.arm.pk_from_sig_loop4 ⟨0#usize,k⟩ rows buf ⦃ out => out.val = packed rows buf k.val ⦄ :=
  pack_roots k rows buf hk (by have := Nat.mul_le_mul hn hk; scalar_tac)

theorem compress_fallback (buf : Array U8 1280#usize) (total : Usize) (S0 : List Spec.SHA512.Word)
    (st : Array U64 8#usize) (off : Usize) (ht : total.val % 128 = 0) (htle : total.val ≤ 1280)
    (hoff : off.val % 128 = 0) (hle : off.val ≤ total.val)
    (hinv : S512.wv st.val = (List.range (off.val / 128)).foldl
      (fun st k => Spec.SHA512.compress st (Spec.SHA512.blockAt (bytes buf.val) k)) S0) :
    fors.arm.pk_from_sig_loop5 buf total st off ⦃ r =>
      S512.wv r.val = S512.hashFrom S0 ((bytes buf.val).take total.val) ⦄ := by
  unfold fors.arm.pk_from_sig_loop5
  apply loop.spec_decr_nat
    (measure := fun (q : Array U64 8#usize × Usize) => total.val - q.2.val)
    (inv := fun q => q.2.val % 128 = 0 ∧ q.2.val ≤ total.val ∧
      S512.wv q.1.val = (List.range (q.2.val / 128)).foldl
        (fun st k => Spec.SHA512.compress st (Spec.SHA512.blockAt (bytes buf.val) k)) S0)
  · rintro ⟨st, off⟩ ⟨hoff, hle, hinv⟩
    simp only [fors.arm.pk_from_sig_loop5.body]
    simp only at hoff hle hinv
    split
    · rename_i hlt
      have h128 : off.val + 128 ≤ total.val := by scalar_tac
      step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      have e : off1.val / 128 = off.val / 128 + 1 := by scalar_tac
      have e2 : 128 * (off.val / 128) = off.val := by omega
      rw [e, List.range_succ, List.foldl_append, ← hinv, st1_post, s_post]
      simp [Spec.SHA512.blockAt, e2]
    · rename_i hge
      have : off.val = total.val := by scalar_tac
      simp only [step_simps]
      rw [this] at hinv
      rw [hinv, hashFrom512_take _ _ _ ht (by simp; omega)]
  · exact ⟨hoff, hle, hinv⟩

end slhdsa.WideFors

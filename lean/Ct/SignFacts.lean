import Ct.Slh
import Ct.Sim
import Slhdsa.Proofs.Api
import Slhdsa.Proofs.Checked

/-!
# Functional facts used by the signing theorems

(Adapted from the single-set tree's `lean/Ct/SignFacts.lean` to the hash length `N` and the
parameter set `p`.) Taken from the functional-correctness proofs of `Slhdsa/Proofs` through
erasure: which calls return (so that the simulator, run on zero seeds, returns), and the values
of a few primitives (blocks of a byte string, `extend_from_slice`, array comparison).
-/

open Aeneas Aeneas.Std Ct

namespace Ct.SignFacts

/-- A computation whose erasure has a `WP.spec` returns. -/
theorem returns_of_spec {α : Type} {m : Leak α} {m0 : Result α} (he : m.erase = m0) {P : α → Prop}
    (hs : WP.spec m0 P) : ∃ b, m.erase = .ok b ∧ P b := by
  obtain ⟨v, hv, hp⟩ := slhdsa.spec_imp_exists hs
  exact ⟨v, he.trans hv, hp⟩

/-- A `Rel` lemma, a returning run of the first side, and a functional theorem for the second
side: the second side returns with the same trace. -/
theorem sim_of_spec {α β : Type} {m : Leak α} {m' : Leak β} {R : α → β → Prop} (h : Rel m m' R)
    {a : α} {t : Trace} (h1 : m.run = .ok (a, t)) {m0 : Result β} (he : m'.erase = m0)
    {P : β → Prop} (hs : WP.spec m0 P) : ∃ b, m'.run = .ok (b, t) ∧ R a b ∧ P b := by
  obtain ⟨b, hb, hp⟩ := returns_of_spec he hs
  obtain ⟨h2, hR⟩ := h.sim h1 hb
  exact ⟨b, h2, hR, hp⟩

/-- Functional facts of a returning instrumented run. -/
theorem spec_of_run {α : Type} {m : Leak α} {m0 : Result α} (he : m.erase = m0) {P : α → Prop}
    (hs : WP.spec m0 P) {a : α} {t : Trace} (h : m.run = .ok (a, t)) : P a := by
  obtain ⟨b, hb, hp⟩ := returns_of_spec he hs
  have := Leak.erase_eq_ok.mpr ⟨t, h⟩
  rw [hb] at this
  simp only [Result.ok.injEq] at this
  subst this
  exact hp

theorem slice_ext {s s' : Slice U8} (h : s.val = s'.val) : s = s' := Slice.ext s s' h

/-! ## `extend_from_slice` on bytes -/

theorem extend_u8 {v : alloc.vec.Vec U8} {s : Slice U8} {w : alloc.vec.Vec U8}
    (h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = .ok w) :
    w.val = v.val ++ s.val ∧ v.length + s.length ≤ Usize.max := by
  by_cases hl : v.length + s.length ≤ Usize.max
  · obtain ⟨r, hr, hv, -⟩ := slhdsa.spec_imp_exists (slhdsa.util_extend_from_slice_u8_spec v s hl)
    rw [hr] at h
    simp only [Result.ok.injEq] at h
    subst h
    exact ⟨hv, hl⟩
  · simp [alloc.vec.Vec.extend_from_slice, hl] at h

theorem extend_run {v : alloc.vec.Vec U8} {s : Slice U8} {w : alloc.vec.Vec U8} {t : Trace}
    (h : (slhdsa_leak.alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s).run = .ok (w, t)) :
    w.val = v.val ++ s.val ∧ v.length + s.length ≤ Usize.max ∧
      t = [.extend v.length s.length] := by
  obtain ⟨h1, rfl⟩ := Leak.prim_eq_ok.mp h
  exact ⟨(extend_u8 h1).1, (extend_u8 h1).2, rfl⟩

theorem extend_run_of {v : alloc.vec.Vec U8} {s : Slice U8} (hl : v.length + s.length ≤ Usize.max) :
    ∃ w, (slhdsa_leak.alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s).run =
      .ok (w, [.extend v.length s.length]) ∧ w.val = v.val ++ s.val := by
  obtain ⟨r, hr, hv, -⟩ := slhdsa.spec_imp_exists (slhdsa.util_extend_from_slice_u8_spec v s hl)
  exact ⟨r, Leak.prim_eq_ok.mpr ⟨hr, rfl⟩, hv⟩

/-- The extension of vectors of the same lengths returns, with the same trace. -/
theorem extend_sim {v v' : alloc.vec.Vec U8} {s s' : Slice U8} {w : alloc.vec.Vec U8} {t : Trace}
    (h : (slhdsa_leak.alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s).run = .ok (w, t))
    (hv : v.length = v'.length) (hs : s.length = s'.length) :
    ∃ w', (slhdsa_leak.alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v' s').run = .ok (w', t) ∧
      w'.val = v'.val ++ s'.val := by
  obtain ⟨-, hl, rfl⟩ := extend_run h
  obtain ⟨w', h', hw'⟩ := extend_run_of (v := v') (s := s') (by rw [← hv, ← hs]; exact hl)
  exact ⟨w', by rw [h', hv, hs], hw'⟩

/-! ## Blocks, comparison -/

theorem block_ok (N : Usize) (s : Slice U8) (i : Usize) (h : (i.val + 1) * N.val ≤ s.length) :
    ∃ r, slhdsa.util.block N s i = .ok r ∧ r.val = (s.val.drop (i.val * N.val)).take N.val := by
  obtain ⟨r, hr, hv⟩ := slhdsa.spec_imp_exists (slhdsa.block_spec N s i h)
  exact ⟨r, hr, hv⟩

theorem block_run_ok (N : Usize) (s : Slice U8) (i : Usize) (h : (i.val + 1) * N.val ≤ s.length) :
    ∃ r t, (slhdsa_leak.util.block N s i).run = .ok (r, t) ∧
      r.val = (s.val.drop (i.val * N.val)).take N.val := by
  obtain ⟨r, hr, hv⟩ := block_ok N s i h
  obtain ⟨t, ht⟩ := Leak.erase_eq_ok.mp ((slhdsa_leak.util.block.erase_eq N s i).trans hr)
  exact ⟨r, t, ht, hv⟩

theorem block_run_val {N : Usize} {s : Slice U8} {i : Usize} {r : Array U8 N} {t : Trace}
    (h : (slhdsa_leak.util.block N s i).run = .ok (r, t)) (hl : (i.val + 1) * N.val ≤ s.length) :
    r.val = (s.val.drop (i.val * N.val)).take N.val := by
  obtain ⟨r', t', h', hv⟩ := block_run_ok N s i hl
  obtain ⟨rfl, -⟩ := Leak.run_ok_det h h'
  exact hv

theorem eq_run {N : Usize} {a b : Array U8 N} {c : Bool} {t : Trace}
    (h : (slhdsa_leak.core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b).run =
      .ok (c, t)) : c = decide (a.val = b.val) ∧ t = [.cmp (commonPrefix a.val b.val) N.val] := by
  obtain ⟨h1, rfl⟩ := Leak.prim_eq_ok.mp h
  obtain ⟨v, hv, hp⟩ := slhdsa.spec_imp_exists (slhdsa.ht_array_eq_spec a b)
  rw [hv] at h1
  simp only [Result.ok.injEq] at h1
  subst h1
  exact ⟨hp, rfl⟩

theorem commonPrefix_self (l : List U8) : commonPrefix l l = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [commonPrefix, ih]

theorem eq_self_run {N : Usize} (a : Array U8 N) :
    (slhdsa_leak.core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a a).run =
      .ok (true, [.cmp N.val N.val]) := by
  obtain ⟨v, hv, hp⟩ := slhdsa.spec_imp_exists (slhdsa.ht_array_eq_spec a a)
  refine Leak.prim_eq_ok.mpr ⟨?_, ?_⟩
  · rw [hv, hp]; simp
  · rw [commonPrefix_self, a.property]

/-- The leaf index of the next layer is below `2^hp`. -/
theorem leaf_bound (p : slhdsa.params.Params) (hhp : p.hp.val ≤ 9) (tree i i1 : U64)
    (hi : 1#u64 <<< p.hp = Result.ok i)
    (hi1 : i - 1#u64 = Result.ok i1) : (UScalar.cast .U32 (tree &&& i1)).val < 2 ^ p.hp.val := by
  obtain ⟨v, hv, hp, -⟩ := slhdsa.spec_imp_exists
    (U64.ShiftLeft_spec (1#u64) p.hp (by omega))
  rw [hv] at hi
  simp only [Result.ok.injEq] at hi
  subst hi
  have hpow : 2 ^ p.hp.val ≤ 2 ^ 9 := Nat.pow_le_pow_right (by omega) hhp
  have h2 : v.val = 2 ^ p.hp.val := by
    rw [hp]
    have e : (1#u64 : U64).val <<< p.hp.val = 2 ^ p.hp.val := by simp [Nat.one_shiftLeft]
    rw [e]
    exact Nat.mod_eq_of_lt (by
      calc 2 ^ p.hp.val ≤ 2 ^ 9 := hpow
        _ < U64.size := by simp [U64.size, U64.numBits])
  have h3 := Ct.Arith.sub_ok hi1
  have hpos : 0 < 2 ^ p.hp.val := Nat.pos_of_ne_zero (by simp)
  have h3' : i1.val = 2 ^ p.hp.val - 1 := by simp at h3; omega
  have h4 : (tree &&& i1).val = tree.val % 2 ^ p.hp.val := by
    rw [UScalar.val_and, h3']
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  rw [UScalar.cast_val_eq, h4]
  have : tree.val % 2 ^ p.hp.val < 2 ^ p.hp.val := Nat.mod_lt _ hpos
  simp only [UScalarTy.numBits]
  calc tree.val % 2 ^ p.hp.val % 2 ^ 32 ≤ tree.val % 2 ^ p.hp.val := Nat.mod_le _ _
    _ < 2 ^ p.hp.val := this

/-- A range of a vector has the length of the range. -/
theorem vec_range_len {v : alloc.vec.Vec U8} {r : core.ops.range.Range Usize} {s : Slice U8}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8) v r = Result.ok s) :
    s.length = r.end.val - r.start.val ∧ r.end.val ≤ v.length := by
  simp only [alloc.vec.Vec.index, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index] at h
  split at h
  · simp only [Result.ok.injEq] at h; subst h
    rename_i hc
    simp only [UScalar.le_equiv] at hc
    simp [Slice.length, List.slice_length, alloc.vec.Vec.length, alloc.vec.Vec.val] at hc ⊢
    omega
  · simp at h

end Ct.SignFacts

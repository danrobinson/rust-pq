import Slhdsa.Proofs.Hw.ChainRun
open Aeneas Aeneas.Std Result

/-! `enter`, `leave` and the loops of `chain_all`
(`../../lean-hw/Slhdsa/Proofs/Hw/ChainLoop.lean` generalised to the hash
length `N`: `enter` also loads the value's second vector and the bytes after
it, and `leave` writes them back for `N > 16`). -/

namespace slhdsa
open Spec.SHA256

set_option linter.unusedSimpArgs false

/-! ## `leave` -/

@[step]
theorem hw_store_be_spec (hw : Arm.haveSha2 = true) (b : Slice U8) (at' : Usize) (v : U4) (h : at'.val + 16 ≤ b.length) :
    sha256.hw.arm.store_be b at' v ⦃ r => r = b.setSlice! at'.val (sha256.hw.arm.be_bytes v) ⦄ := by
  unfold sha256.hw.arm.store_be
  rw [if_pos hw, if_pos (by scalar_tac)]
  exact (WP.spec_ok _).mpr rfl

theorem bytes_be_bytes (v : U4) : bytes (sha256.hw.arm.be_bytes v) = vbytes v := by
  simp [bytes, sha256.hw.arm.be_bytes, vbytes, List.map_append]

theorem be_bytes_length (v : U4) : (sha256.hw.arm.be_bytes v).length = 16 := by
  simp [sha256.hw.arm.be_bytes, Arm.beBytes]

/-- The block after `leave` wrote the counter and the value's first vector. -/
theorem leave_shape16 (B c : Spec.Bytes) (hB : B.length = 64) (hc : c.length = 4) (x : Arm.V) :
    (B.take 18 ++ c ++ B.drop 22).take 22 ++ vbytes x ++ (B.take 18 ++ c ++ B.drop 22).drop 38 =
      B.take 18 ++ c ++ vbytes x ++ B.drop 38 := by
  apply List.ext_getElem
  · simp [hB, hc]; try omega
  · intro n h1 h2
    have hm : min 18 B.length = 18 := by omega
    simp only [List.getElem_append, List.length_take, List.length_append, List.getElem_take,
      List.getElem_drop, List.length_drop, vbytes_length, hm, hc, hB]
    split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- The block after `leave` wrote the counter and both vectors of the value. -/
theorem leave_shape (B c : Spec.Bytes) (hB : B.length = 64) (hc : c.length = 4) (x v : Arm.V) :
    ((B.take 18 ++ c ++ B.drop 22).take 38 ++ vbytes v ++ (B.take 18 ++ c ++ B.drop 22).drop 54).take 22 ++
      vbytes x ++
      ((B.take 18 ++ c ++ B.drop 22).take 38 ++ vbytes v ++ (B.take 18 ++ c ++ B.drop 22).drop 54).drop 38 =
      B.take 18 ++ c ++ (vbytes x ++ vbytes v) ++ B.drop 54 := by
  have l18 : (B.take 18).length = 18 := by simp [hB]
  have e1 : (B.take 18 ++ c ++ B.drop 22).take 38 = B.take 18 ++ c ++ (B.drop 22).take 16 := by
    rw [List.take_append, List.take_of_length_le (by simp [l18, hc]), List.length_append, l18, hc]
  have e2 : (B.take 18 ++ c ++ B.drop 22).drop 54 = B.drop 54 := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by simp [l18, hc]), List.length_append, l18, hc,
      List.drop_drop]
    simp
  have l38 : (B.take 18 ++ c ++ (B.drop 22).take 16).length = 38 := by simp [l18, hc, hB]
  have l22 : (B.take 18 ++ c).length = 22 := by simp [l18, hc]
  rw [e1, e2, List.append_assoc _ (vbytes v), List.take_append_of_le_length (by omega),
    List.drop_left' l38, List.append_assoc (B.take 18 ++ c), List.take_left' l22]
  simp

theorem take8_explicit (B : Spec.Bytes) (i : Nat) (h : i + 8 ≤ B.length) :
    (B.drop i).take 8 = [B[i]!, B[i + 1]!, B[i + 2]!, B[i + 3]!, B[i + 4]!, B[i + 5]!, B[i + 6]!,
      B[i + 7]!] := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    have hn : n < 8 := by simpa using h2
    simp only [List.getElem_take, List.getElem_drop]
    rw [← getElem!_eq _ _ (by omega)]
    interval_cases n <;> rfl

/-- For n = 24, what `leave` writes at bytes 38..54 is the value's last eight
bytes and the eight bytes that `enter` saved. -/
theorem leave24 (B : Spec.Bytes) (hB : B.length = 64) (xb : Arm.V) (hn : Norm 24 xb) :
    vbytes (Arm.ORR xb (Arm.AND (beV B 38) high2V)) ++ B.drop 54 = (vbytes xb).take 8 ++ B.drop 46 := by
  obtain ⟨a, b, c, d⟩ := xb
  obtain ⟨hc, hd⟩ := hn rfl
  simp only at hc hd
  subst hc hd
  rw [drop_split B 46 8, take8_explicit B 46 (by omega)]
  simp [vbytes, Arm.ORR, Arm.AND, high2V, beV, and_ones, beBytes_word]
  simp [Arm.beBytes]

theorem orr_and_zero (xb w : Arm.V) : Arm.ORR xb (Arm.AND w zV) = xb := by
  obtain ⟨a, b, c, d⟩ := xb
  simp [Arm.ORR, Arm.AND, zV]

theorem ctr_bytes (block : Array U8 64#usize) (t : U32) (i i2 i4 : U32)
    (hi : i.val = t.val >>> 24) (hi2 : i2.val = t.val >>> 16) (hi4 : i4.val = t.val >>> 8) :
    bytes ((((block.set 18#usize (UScalar.cast UScalarTy.U8 i)).set 19#usize (UScalar.cast UScalarTy.U8 i2)).set
      20#usize (UScalar.cast UScalarTy.U8 i4)).set 21#usize (UScalar.cast UScalarTy.U8 t)).val =
      (bytes block.val).take 18 ++ Spec.toByte t.val 4 ++ (bytes block.val).drop 22 := by
  simp only [Array.set_val_eq, bytes_set, show (18#usize).val = 18 from rfl,
    show (19#usize).val = 19 from rfl, show (20#usize).val = 20 from rfl,
    show (21#usize).val = 21 from rfl]
  rw [set4_eq _ (by simp), toByte4_eq, cast_u8_bv32, cast_u8_bv32, cast_u8_bv32, cast_u8_bv32, hi, hi2, hi4]

theorem setBlk16_eq (B : Spec.Bytes) (c : Nat) (x xb : Arm.V) :
    setBlk 16 B c x xb = B.take 18 ++ Spec.toByte c 4 ++ vbytes x ++ B.drop 38 := by
  simp only [setBlk, valB]
  rw [List.take_left' (vbytes_length _)]

theorem leave_final32 (B : Spec.Bytes) (c : Nat) (x xb tl : Arm.V) (ht : tl = Arm.AND (beV B 38) zV) :
    B.take 18 ++ Spec.toByte c 4 ++ (vbytes x ++ vbytes (Arm.ORR xb tl)) ++ B.drop 54 = setBlk 32 B c x xb := by
  rw [ht, orr_and_zero]
  simp only [setBlk, valB]
  rw [List.take_of_length_le (l := vbytes x ++ vbytes xb) (by simp)]

theorem leave_final24 (B : Spec.Bytes) (hB : B.length = 64) (c : Nat) (x xb tl : Arm.V)
    (ht : tl = Arm.AND (beV B 38) high2V) (hn : Norm 24 xb) :
    B.take 18 ++ Spec.toByte c 4 ++ (vbytes x ++ vbytes (Arm.ORR xb tl)) ++ B.drop 54 = setBlk 24 B c x xb := by
  rw [ht]
  simp only [setBlk, valB, List.append_assoc]
  rw [leave24 B hB xb hn, List.take_append (l₁ := vbytes x), List.take_of_length_le (l := vbytes x) (by simp),
    vbytes_length]
  simp

theorem leave_spec (hw : Arm.haveSha2 = true) (N : Usize) (hN : KN N.val) (slot : sha256.hw.Slot)
    (block : Array U8 64#usize) (h : 1 ≤ slot.t.val)
    (htail : slot.tail = tailV N.val (bytes block.val)) (hnorm : Norm N.val slot.xb) :
    sha256.hw.leave N slot block ⦃ b =>
      bytes b.val = setBlk N.val (bytes block.val) (slot.t.val - 1) slot.x slot.xb ⦄ := by
  unfold sha256.hw.leave
  have hB : (bytes block.val).length = 64 := by simp
  rcases KN_cases hN with hN' | hN' | hN' <;> subst hN' <;> ntac
  · step*
    have h4 := ctr_bytes block t i i2 i4 i_post i2_post i4_post
    have hres : bytes (to_slice_mut_back s1).val =
        ((bytes block.val).take 18 ++ Spec.toByte (slot.t.val - 1) 4 ++ (bytes block.val).drop 22).take 22 ++
          vbytes slot.x ++
          ((bytes block.val).take 18 ++ Spec.toByte (slot.t.val - 1) 4 ++ (bytes block.val).drop 22).drop 38 := by
      rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by rw [s1_post]; simp [be_bytes_length]; scalar_tac),
        s1_post, Slice.setSlice!_val, bytes_setSlice _ _ _ (by rw [be_bytes_length, s_post]; simp), s_post,
        bytes_be_bytes, be_bytes_length, index_mut_back_post, block3_post, block2_post, block1_post, i1_post,
        i3_post, i5_post, i6_post, h4, t_post]
    exact hres.trans ((leave_shape16 _ _ hB (toByte_length4 _) _).trans (setBlk16_eq _ _ _ _).symm)
  all_goals
    step*
    obtain ⟨s5, back5⟩ := x
    have hs5 := x_post
    have hb5 := x_post1
    clear x_post x_post1
    simp only at hs5 hb5
    step as ⟨uxt, huxt⟩
    step as ⟨s6, hs6⟩
    step*
    have h4 := ctr_bytes block t i i2 i4 i_post i2_post i4_post
    have hres : bytes (to_slice_mut_back s1).val =
        (((bytes block.val).take 18 ++ Spec.toByte (slot.t.val - 1) 4 ++ (bytes block.val).drop 22).take 38 ++
          vbytes (Arm.ORR slot.xb slot.tail) ++
          ((bytes block.val).take 18 ++ Spec.toByte (slot.t.val - 1) 4 ++ (bytes block.val).drop 22).drop 54).take 22 ++
        vbytes slot.x ++
        (((bytes block.val).take 18 ++ Spec.toByte (slot.t.val - 1) 4 ++ (bytes block.val).drop 22).take 38 ++
          vbytes (Arm.ORR slot.xb slot.tail) ++
          ((bytes block.val).take 18 ++ Spec.toByte (slot.t.val - 1) 4 ++ (bytes block.val).drop 22).drop 54).drop 38 := by
      have l6 : s6.length = 64 := by rw [hs6]; simp [be_bytes_length]; rw [hs5]; simp
      rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by rw [s1_post]; simp [be_bytes_length]; scalar_tac),
        s1_post, Slice.setSlice!_val, bytes_setSlice _ _ _ (by rw [be_bytes_length, s_post]; simp), s_post,
        hb5, Array.from_slice_val _ _ l6, hs6, Slice.setSlice!_val,
        bytes_setSlice _ _ _ (by rw [be_bytes_length, hs5]; simp), hs5, huxt,
        bytes_be_bytes, bytes_be_bytes, be_bytes_length, index_mut_back_post, block3_post, block2_post,
        block1_post, i1_post, i3_post, i5_post, i6_post, h4, t_post]
      rfl
    first
      | (have ht : slot.tail = Arm.AND (beV (bytes block.val) 38) high2V := by
           rw [htail]; simp only [tailV, ktV, v24, ite_true, ite_false, Nat.reduceEqDiff]; rfl
         exact hres.trans ((leave_shape _ _ hB (toByte_length4 _) _ _).trans
           (leave_final24 _ hB _ _ _ _ ht (by simpa [v24] using hnorm))))
      | (have ht : slot.tail = Arm.AND (beV (bytes block.val) 38) zV := by
           rw [htail]; simp only [tailV, ktV, v32, ite_true, ite_false, Nat.reduceEqDiff]; rfl
         exact hres.trans ((leave_shape _ _ hB (toByte_length4 _) _ _).trans (leave_final32 _ _ _ _ _ ht)))

/-! ## `enter` -/

/-- The cache of rounds 0..3 is right for `state`. -/
def FirstOk (st : List Word) (f : sha256.hw.First) : Prop :=
  f.known = true →
    f.a1 = Arm.SHA256H (vOf st 0) (vOf st 4) (Arm.ADD (beV (bytes f.head.val) 0) (vOf K 0)) ∧
    f.e1 = Arm.SHA256H2 (vOf st 4) (vOf st 0) (Arm.ADD (beV (bytes f.head.val) 0) (vOf K 0))

theorem chain_allM_eq (l1 l2 : List U8) (h : l1.length = l2.length) :
    List.allM (fun (x : U8 × U8) => (ok (decide (x.1.val = x.2.val)) : Result Bool)) (List.zip l1 l2)
      = ok (decide (l1 = l2)) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> first | rfl | simp at h
  | cons x xs ih =>
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, List.allM]
      by_cases hxy : x = y
      · subst hxy
        simp [ih ys h]
      · have : ¬ x.val = y.val := fun hv => hxy (by scalar_tac)
        simp [hxy, this]
        rfl

@[step]
theorem chain_array_eq_spec (a b : Array U8 16#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b ⦃ r => r = decide (a.val = b.val) ⦄ := by
  unfold core.array.equality.PartialEqArray.eq
  simp
  rw [chain_allM_eq _ _ (by simp)]
  simp

theorem beV_take16 (B : Spec.Bytes) : beV (B.take 16) 0 = beV B 0 := by
  simp only [beV, word, getElem!_take' _ _ _ (by omega : (0:Nat) < 16)]
  simp only [Nat.zero_add, getElem!_take' _ _ _ (by omega : (1:Nat) < 16),
    getElem!_take' _ _ _ (by omega : (2:Nat) < 16), getElem!_take' _ _ _ (by omega : (3:Nat) < 16),
    getElem!_take' _ _ _ (by omega : (4:Nat) < 16), getElem!_take' _ _ _ (by omega : (5:Nat) < 16),
    getElem!_take' _ _ _ (by omega : (6:Nat) < 16), getElem!_take' _ _ _ (by omega : (7:Nat) < 16),
    getElem!_take' _ _ _ (by omega : (8:Nat) < 16), getElem!_take' _ _ _ (by omega : (9:Nat) < 16),
    getElem!_take' _ _ _ (by omega : (10:Nat) < 16), getElem!_take' _ _ _ (by omega : (11:Nat) < 16),
    getElem!_take' _ _ _ (by omega : (12:Nat) < 16), getElem!_take' _ _ _ (by omega : (13:Nat) < 16),
    getElem!_take' _ _ _ (by omega : (14:Nat) < 16), getElem!_take' _ _ _ (by omega : (15:Nat) < 16)]

theorem mask1_eq : vOf (wv sha256.hw.MASK1.val) 0 = mask1V := by
  simp only [sha256.hw.MASK1]; rfl

theorem mask2_eq : vOf (wv sha256.hw.MASK2.val) 0 = mask2V := by
  simp only [sha256.hw.MASK2]; rfl

theorem mask224_eq : vOf (wv sha256.hw.MASK2_24.val) 0 = mask224V := by
  simp only [sha256.hw.MASK2_24]; rfl

theorem all_eq : vOf (wv sha256.hw.ALL.val) 0 = allV := by
  simp only [sha256.hw.ALL]; rfl

theorem high2_eq : vOf (wv sha256.hw.HIGH2.val) 0 = high2V := by
  simp only [sha256.hw.HIGH2]; rfl

theorem zero4_eq : vOf (wv (Array.repeat 4#usize 0#u32).val) 0 = zV := by
  rfl

theorem enter_spec (hw : Arm.haveSha2 = true) (N : Usize) (hN : KN N.val) (state : Array U32 8#usize)
    (block : Array U8 64#usize) (t e : U32) (lane : Usize)
    (first : sha256.hw.First) (hf : FirstOk (wv state.val) first) :
    sha256.hw.enter N state block t e lane first ⦃ r =>
      FirstOk (wv state.val) r.2 ∧ SlotOk N.val (wv state.val) (bytes block.val) r.1 ∧
      r.1.x = beV (bytes block.val) 22 ∧ r.1.xb = xb0 N.val (bytes block.val) ∧
      r.1.t = t ∧ r.1.end = e ∧ r.1.lane = lane ⦄ := by
  unfold sha256.hw.enter
  rcases KN_cases hN with hN' | hN' | hN' <;> subst hN' <;> ntac
  all_goals
    step*
    have hhead : (to_slice_mut_back s3).val = block.val.take 16 := by
      rw [to_slice_mut_back_post, Array.from_slice_val _ _ (by rw [s3_post]; scalar_tac), s3_post,
        s2_post]
      simp [List.slice]
    have hh0 : beV (bytes (to_slice_mut_back s3).val) 0 = beV (bytes block.val) 0 := by
      rw [hhead, bytes_take, beV_take16]
    have hB : (bytes block.val).length = 64 := by simp
    split
    · step*
      split
      · rename_i hkn hxt
        have hx : first.head.val = (to_slice_mut_back s3).val := by
          have := x_post ▸ hxt; simpa using this
        obtain ⟨ha1, he1⟩ := hf hkn
        step*
        subst_vars
        refine ⟨hf, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
          simp only [toU, Array.val_to_slice, mask1_eq, mask2_eq, mask224_eq, all_eq, low2_eq, high2_eq,
            zero4_eq, K_slice_eq, K_eq, ha1, he1, hx, hh0, k2V, k3V, kbV, ktV, xb0, tailV, v16, v24, v32,
            ite_true, ite_false, Nat.reduceEqDiff] <;> exact rfl
      · step*
        subst_vars
        refine ⟨fun _ => ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
          simp only [toU, Array.val_to_slice, mask1_eq, mask2_eq, mask224_eq, all_eq, low2_eq, high2_eq,
            zero4_eq, K_slice_eq, K_eq, hh0, k2V, k3V, kbV, ktV, xb0, tailV, v16, v24, v32,
            ite_true, ite_false, Nat.reduceEqDiff] <;> exact rfl
    · step*
      subst_vars
      refine ⟨fun _ => ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
        simp only [toU, Array.val_to_slice, mask1_eq, mask2_eq, mask224_eq, all_eq, low2_eq, high2_eq,
          zero4_eq, K_slice_eq, K_eq, hh0, k2V, k3V, kbV, ktV, xb0, tailV, v16, v24, v32,
          ite_true, ite_false, Nat.reduceEqDiff] <;> exact rfl

/-! ## The least number of steps left -/

theorem min_loop0_spec (slots : Array sha256.hw.Slot 4#usize) (n : Usize) (r : U32) (j : Usize)
    (hn : n.val ≤ 4) (hj : j.val ≤ n.val)
    (hpos : ∀ i < n.val, (slots.val[i]!).t.val < (slots.val[i]!).end.val)
    (hr1 : 1 ≤ r.val) (hr : ∀ i < j.val, r.val ≤ (slots.val[i]!).end.val - (slots.val[i]!).t.val) :
    sha256.hw.chain_all_loop0_loop0 slots n r j ⦃ r' =>
      1 ≤ r'.val ∧ ∀ i < n.val, r'.val ≤ (slots.val[i]!).end.val - (slots.val[i]!).t.val ⦄ := by
  unfold sha256.hw.chain_all_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (q : U32 × Usize) => n.val - q.2.val)
    (inv := fun q => q.2.val ≤ n.val ∧ 1 ≤ q.1.val ∧
      ∀ i < q.2.val, q.1.val ≤ (slots.val[i]!).end.val - (slots.val[i]!).t.val)
  · rintro ⟨r, j⟩ ⟨hj, hr1, hr⟩
    simp only [sha256.hw.chain_all_loop0_loop0.body]
    simp only at hj hr1 hr
    have hpj : ∀ (h : j.val < n.val), (slots.val[j.val]'(by simp; omega)).t.val <
        (slots.val[j.val]'(by simp; omega)).end.val := by
      intro h; have := hpos j.val h; rwa [getElem!_eq _ _ (by simp; omega)] at this
    step*
    · have := hpj (by scalar_tac)
      have hge : (slots.val[j.val]!).end.val - (slots.val[j.val]!).t.val = left.val := by
        rw [left_post, s_post, getElem!_eq _ _ (by simp; scalar_tac)]
      split
      all_goals
        step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp (by rw [j1_post] at hi; exact hi) with hi | hi
        · have := hr i hi; scalar_tac
        · subst hi; rw [hge]; try scalar_tac
    all_goals try exact ⟨hr1, fun i hi => hr i (by scalar_tac)⟩
  · exact ⟨hj, hr1, hr⟩

/-! ## Writing back finished chains -/

/-- A slot that still has steps to do. -/
def keepB (sl : sha256.hw.Slot) : Bool := decide (sl.t.val < sl.end.val)

theorem take_succ_arr {α} [Inhabited α] (l : List α) (j : Nat) (h : j < l.length) :
    l.take (j + 1) = l.take j ++ [l[j]!] := by
  rw [List.take_succ_eq_append_getElem h, getElem!_eq _ _ h]

theorem pw_prefix (S : List sha256.hw.Slot) (n j : Nat) (hj : j < n) (hjS : j < S.length)
    (hpw : (S.take n).Pairwise (fun a b => a.lane.val < b.lane.val)) :
    ∀ sl ∈ S.take j, sl.lane.val < (S[j]!).lane.val := by
  have h1 : (S.take (j + 1)).Pairwise (fun a b => a.lane.val < b.lane.val) := by
    have := hpw.sublist (List.take_sublist (j + 1) (S.take n))
    rwa [List.take_take, Nat.min_eq_left (by omega)] at this
  rw [take_succ_arr _ _ hjS, List.pairwise_append] at h1
  intro sl hsl
  exact h1.2.2 sl hsl _ (by simp)

theorem compact_step (S : List sha256.hw.Slot) (j : Nat) (hjS : j < S.length) (P : sha256.hw.Slot → Prop) :
    (∀ sl ∈ S.take (j + 1), P sl) ↔ (∀ sl ∈ S.take j, P sl) ∧ P (S[j]!) := by
  rw [take_succ_arr _ _ hjS]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · intro h; exact ⟨fun sl hs => h sl (Or.inl hs), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ sl (hs | rfl)
    · exact h1 sl hs
    · exact h2

/-- The state of the write-back loop after `j` of the `n` slots of `S`. -/
def CInv (n' n : Nat) (blocks0 : Slice (Array U8 64#usize)) (S : Array sha256.hw.Slot 4#usize)
    (blocks : Slice (Array U8 64#usize)) (slots : Array sha256.hw.Slot 4#usize) (k j : Nat) : Prop :=
  k ≤ j ∧ j ≤ n ∧ blocks.length = blocks0.length ∧
  slots.val.take k = (S.val.take j).filter keepB ∧
  (∀ i, j ≤ i → slots.val[i]! = S.val[i]!) ∧
  (∀ sl ∈ S.val.take j, keepB sl = false →
    bytes (blocks.val[sl.lane.val]!).val =
      setBlk n' (bytes (blocks0.val[sl.lane.val]!).val) (sl.t.val - 1) sl.x sl.xb) ∧
  (∀ b, (∀ sl ∈ S.val.take j, keepB sl = false → sl.lane.val ≠ b) → blocks.val[b]! = blocks0.val[b]!)

theorem cinv_step (n' n : Nat) (hn : n ≤ 4) (blocks0 : Slice (Array U8 64#usize))
    (S : Array sha256.hw.Slot 4#usize)
    (hpw : (S.val.take n).Pairwise (fun a b => a.lane.val < b.lane.val))
    (blocks : Slice (Array U8 64#usize)) (slots : Array sha256.hw.Slot 4#usize) (k j : Nat)
    (hj : j < n) (hI : CInv n' n blocks0 S blocks slots k j) :
    -- kept
    (keepB (S.val[j]!) = true → ∀ (k1 : Usize), k1.val = k + 1 → ∀ kk : Usize, kk.val = k →
      CInv n' n blocks0 S blocks (slots.set kk (S.val[j]!)) k1.val (j + 1)) ∧
    -- finished
    (keepB (S.val[j]!) = false → ∀ (b : Array U8 64#usize),
      bytes b.val = setBlk n' (bytes (blocks.val[(S.val[j]!).lane.val]!).val) ((S.val[j]!).t.val - 1)
        (S.val[j]!).x (S.val[j]!).xb →
      (S.val[j]!).lane.val < blocks.length →
      CInv n' n blocks0 S (blocks.set (S.val[j]!).lane b) slots k (j + 1)) ∧
    -- the block of chain `j` is still untouched
    blocks.val[(S.val[j]!).lane.val]! = blocks0.val[(S.val[j]!).lane.val]! := by
  obtain ⟨hkj, hjn, hlen, hk, hr, hd, hu⟩ := hI
  have hjS : j < S.val.length := by simp; omega
  have hlt := pw_prefix S.val n j hj hjS hpw
  refine ⟨fun hkp k1 hk1 kk hkk => ?_, fun hkp b hb hl => ?_,
    hu _ (fun sl' hsl' _ => by have := hlt sl' hsl'; omega)⟩
  · refine ⟨by omega, by omega, hlen, ?_, ?_, ?_, ?_⟩
    · rw [hk1, Array.set_val_eq, hkk, take_set_succ _ _ _ (by simp; omega), hk, take_succ_arr _ _ hjS,
        List.filter_append, List.filter_singleton, hkp, cond_true]
    · intro i hi
      rw [Array.set_val_eq, getElem!_set_ne' _ _ _ _ (by omega)]
      exact hr i (by omega)
    · intro sl hsl hks
      rw [take_succ_arr _ _ hjS] at hsl
      rcases List.mem_append.mp hsl with hsl | hsl
      · exact hd sl hsl hks
      · rw [List.mem_singleton.mp hsl, hkp] at hks; cases hks
    · intro bb hbb
      exact hu bb (fun sl hsl hks => hbb sl (by rw [take_succ_arr _ _ hjS]; simp [hsl]) hks)
  · refine ⟨by omega, by omega, by simp [hlen], ?_, ?_, ?_, ?_⟩
    · rw [hk, take_succ_arr _ _ hjS, List.filter_append, List.filter_singleton, hkp, cond_false,
        List.append_nil]
    · intro i hi; exact hr i (by omega)
    · intro sl hsl hks
      rw [take_succ_arr _ _ hjS] at hsl
      rcases List.mem_append.mp hsl with hsl | hsl
      · have hne : (S.val[j]!).lane.val ≠ sl.lane.val := by have := hlt sl hsl; omega
        rw [Slice.set_val_eq, getElem!_set_ne' _ _ _ _ hne]
        exact hd sl hsl hks
      · rw [List.mem_singleton.mp hsl]
        rw [Slice.set_val_eq, getElem!_set_self' _ _ _ (by simpa using hl), hb,
          hu _ (fun sl' hsl' _ => by have := hlt sl' hsl'; omega)]
    · intro bb hbb
      have hne : (S.val[j]!).lane.val ≠ bb := hbb _ (by rw [take_succ_arr _ _ hjS]; simp) hkp
      rw [Slice.set_val_eq, getElem!_set_ne' _ _ _ _ hne]
      exact hu bb (fun sl hsl hks => hbb sl (by rw [take_succ_arr _ _ hjS]; simp [hsl]) hks)

theorem mem_take_n (S : List sha256.hw.Slot) (n j : Nat) (hj : j < n) (hjS : j < S.length) :
    S[j]! ∈ S.take n := by
  rw [getElem!_eq _ _ hjS]
  exact List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩

theorem compact_loop1_spec (hw : Arm.haveSha2 = true) (N : Usize) (hN : KN N.val) (n : Usize)
    (blocks0 : Slice (Array U8 64#usize))
    (S : Array sha256.hw.Slot 4#usize) (blocks : Slice (Array U8 64#usize))
    (slots : Array sha256.hw.Slot 4#usize) (k j : Usize) (hn : n.val ≤ 4)
    (hpw : (S.val.take n.val).Pairwise (fun a b => a.lane.val < b.lane.val))
    (hfin : ∀ sl ∈ S.val.take n.val, keepB sl = false → 1 ≤ sl.t.val ∧ sl.lane.val < blocks0.length ∧
      sl.tail = tailV N.val (bytes (blocks0.val[sl.lane.val]!).val) ∧ Norm N.val sl.xb)
    (hI : CInv N.val n.val blocks0 S blocks slots k.val j.val) :
    sha256.hw.chain_all_loop0_loop1 N blocks slots n k j ⦃ r =>
      CInv N.val n.val blocks0 S r.1 r.2.1 r.2.2.val n.val ⦄ := by
  unfold sha256.hw.chain_all_loop0_loop1
  apply loop.spec_decr_nat
    (measure := fun (q : Slice (Array U8 64#usize) × Array sha256.hw.Slot 4#usize × Usize × Usize) =>
      n.val - q.2.2.2.val)
    (inv := fun q => CInv N.val n.val blocks0 S q.1 q.2.1 q.2.2.1.val q.2.2.2.val)
  · rintro ⟨blocks, slots, k, j⟩ hI
    simp only [sha256.hw.chain_all_loop0_loop1.body]
    simp only at hI
    have hI' := hI
    obtain ⟨hkj, hjn, hlen, hk, hr, hd, hu⟩ := hI'
    split
    · have hj : j.val < n.val := by scalar_tac
      have hjS : j.val < S.val.length := by simp; omega
      have hsj : slots.val[j.val]'(by simp; omega) = S.val[j.val]! := by
        rw [← getElem!_eq _ _ (by simp; omega)]; exact hr _ (le_refl _)
      have hst := cinv_step N.val n.val hn blocks0 S hpw blocks slots k.val j.val hj hI
      have hmem := mem_take_n S.val n.val j.val hj hjS
      step as ⟨s, hs⟩
      rw [hsj] at hs
      subst hs
      clear hsj
      step*
      · refine ⟨?_, by scalar_tac⟩
        rw [a_post, j1_post]
        exact hst.1 (by simp only [keepB, decide_eq_true_eq]; scalar_tac) k1 k1_post k rfl
      · have hkf : keepB (S.val[j.val]!) = false := by
          simp only [keepB, decide_eq_false_iff_not]; scalar_tac
        have hf := hfin _ hmem hkf
        scalar_tac
      · have hkf : keepB (S.val[j.val]!) = false := by
          simp only [keepB, decide_eq_false_iff_not]; scalar_tac
        have hf := hfin _ hmem hkf
        have htl : (S.val[j.val]!).tail = tailV N.val (bytes a.val) := by
          rw [a_post, ← getElem!_eq _ _ (by scalar_tac), hst.2.2]; exact hf.2.2.1
        step with leave_spec hw N hN _ _ hf.1 htl hf.2.2.2 as ⟨a1, ha1⟩
        step*
        refine ⟨?_, by scalar_tac⟩
        rw [j1_post, index_mut_back_post]
        refine hst.2.1 hkf a1 ?_ (by scalar_tac)
        rw [ha1, a_post, getElem!_eq blocks.val _ (by scalar_tac)]
    · have : j.val = n.val := by scalar_tac
      simp only [WP.spec_ok]
      convert hI using 1; exact this.symm
  · exact hI

theorem min_loop2_spec (slots : Array sha256.hw.Slot 4#usize) (n : Usize) (r : U32) (j : Usize)
    (hn : n.val ≤ 4) (hj : j.val ≤ n.val)
    (hpos : ∀ i < n.val, (slots.val[i]!).t.val < (slots.val[i]!).end.val)
    (hr1 : 1 ≤ r.val) (hr : ∀ i < j.val, r.val ≤ (slots.val[i]!).end.val - (slots.val[i]!).t.val) :
    sha256.hw.chain_all_loop0_loop2 slots n r j ⦃ r' =>
      1 ≤ r'.val ∧ ∀ i < n.val, r'.val ≤ (slots.val[i]!).end.val - (slots.val[i]!).t.val ⦄ := by
  unfold sha256.hw.chain_all_loop0_loop2
  apply loop.spec_decr_nat
    (measure := fun (q : U32 × Usize) => n.val - q.2.val)
    (inv := fun q => q.2.val ≤ n.val ∧ 1 ≤ q.1.val ∧
      ∀ i < q.2.val, q.1.val ≤ (slots.val[i]!).end.val - (slots.val[i]!).t.val)
  · rintro ⟨r, j⟩ ⟨hj, hr1, hr⟩
    simp only [sha256.hw.chain_all_loop0_loop2.body]
    simp only at hj hr1 hr
    have hpj : ∀ (h : j.val < n.val), (slots.val[j.val]'(by simp; omega)).t.val <
        (slots.val[j.val]'(by simp; omega)).end.val := by
      intro h; have := hpos j.val h; rwa [getElem!_eq _ _ (by simp; omega)] at this
    step*
    · have := hpj (by scalar_tac)
      have hge : (slots.val[j.val]!).end.val - (slots.val[j.val]!).t.val = left.val := by
        rw [left_post, s_post, getElem!_eq _ _ (by simp; scalar_tac)]
      split
      all_goals
        step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp (by rw [j1_post] at hi; exact hi) with hi | hi
        · have := hr i hi; scalar_tac
        · subst hi; rw [hge]; try scalar_tac
    all_goals try exact ⟨hr1, fun i hi => hr i (by scalar_tac)⟩
  · exact ⟨hj, hr1, hr⟩

theorem compact_loop3_spec (hw : Arm.haveSha2 = true) (N : Usize) (hN : KN N.val) (n : Usize)
    (blocks0 : Slice (Array U8 64#usize))
    (S : Array sha256.hw.Slot 4#usize) (blocks : Slice (Array U8 64#usize))
    (slots : Array sha256.hw.Slot 4#usize) (k j : Usize) (hn : n.val ≤ 4)
    (hpw : (S.val.take n.val).Pairwise (fun a b => a.lane.val < b.lane.val))
    (hfin : ∀ sl ∈ S.val.take n.val, keepB sl = false → 1 ≤ sl.t.val ∧ sl.lane.val < blocks0.length ∧
      sl.tail = tailV N.val (bytes (blocks0.val[sl.lane.val]!).val) ∧ Norm N.val sl.xb)
    (hI : CInv N.val n.val blocks0 S blocks slots k.val j.val) :
    sha256.hw.chain_all_loop0_loop3 N blocks slots n k j ⦃ r =>
      CInv N.val n.val blocks0 S r.1 r.2.1 r.2.2.val n.val ⦄ := by
  unfold sha256.hw.chain_all_loop0_loop3
  apply loop.spec_decr_nat
    (measure := fun (q : Slice (Array U8 64#usize) × Array sha256.hw.Slot 4#usize × Usize × Usize) =>
      n.val - q.2.2.2.val)
    (inv := fun q => CInv N.val n.val blocks0 S q.1 q.2.1 q.2.2.1.val q.2.2.2.val)
  · rintro ⟨blocks, slots, k, j⟩ hI
    simp only [sha256.hw.chain_all_loop0_loop3.body]
    simp only at hI
    have hI' := hI
    obtain ⟨hkj, hjn, hlen, hk, hr, hd, hu⟩ := hI'
    split
    · have hj : j.val < n.val := by scalar_tac
      have hjS : j.val < S.val.length := by simp; omega
      have hsj : slots.val[j.val]'(by simp; omega) = S.val[j.val]! := by
        rw [← getElem!_eq _ _ (by simp; omega)]; exact hr _ (le_refl _)
      have hst := cinv_step N.val n.val hn blocks0 S hpw blocks slots k.val j.val hj hI
      have hmem := mem_take_n S.val n.val j.val hj hjS
      step as ⟨s, hs⟩
      rw [hsj] at hs
      subst hs
      clear hsj
      step*
      · refine ⟨?_, by scalar_tac⟩
        rw [a_post, j1_post]
        exact hst.1 (by simp only [keepB, decide_eq_true_eq]; scalar_tac) k1 k1_post k rfl
      · have hkf : keepB (S.val[j.val]!) = false := by
          simp only [keepB, decide_eq_false_iff_not]; scalar_tac
        have hf := hfin _ hmem hkf
        scalar_tac
      · have hkf : keepB (S.val[j.val]!) = false := by
          simp only [keepB, decide_eq_false_iff_not]; scalar_tac
        have hf := hfin _ hmem hkf
        have htl : (S.val[j.val]!).tail = tailV N.val (bytes a.val) := by
          rw [a_post, ← getElem!_eq _ _ (by scalar_tac), hst.2.2]; exact hf.2.2.1
        step with leave_spec hw N hN _ _ hf.1 htl hf.2.2.2 as ⟨a1, ha1⟩
        step*
        refine ⟨?_, by scalar_tac⟩
        rw [j1_post, index_mut_back_post]
        refine hst.2.1 hkf a1 ?_ (by scalar_tac)
        rw [ha1, a_post, getElem!_eq blocks.val _ (by scalar_tac)]
    · have : j.val = n.val := by scalar_tac
      simp only [WP.spec_ok]
      convert hI using 1; exact this.symm
  · exact hI

end slhdsa

import Slhdsa.Proofs.Hw.ChainModel
open Aeneas Aeneas.Std Result

/-! The lanes of the hardware chain kernel: `lane_step`, `lane_tick`, `tick`,
`period` and `run`. -/

namespace slhdsa
open Spec.SHA256

set_option linter.unusedSimpArgs false

instance : Inhabited core.core_arch.arm_shared.neon.uint32x4_t := inferInstanceAs (Inhabited Arm.V)
deriving instance Inhabited for sha256.hw.Slot

/-! ## The wrappers

Their results are stated through `toU`, the identity from `Arm.V` to the Rust
vector type, so that rewriting with them keeps terms well typed at reducible
transparency. -/

abbrev U4 := core.core_arch.arm_shared.neon.uint32x4_t

/-- A vector as the Rust vector type (the identity). -/
def toU (v : Arm.V) : U4 := v

@[simp] theorem toU_eq (v : Arm.V) : (toU v : Arm.V) = v := rfl

@[step] theorem hw_zero_spec : sha256.hw.arm.zero ⦃ r => r = toU zV ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_pair_spec (a b : U32) :
    sha256.hw.arm.pair a b ⦃ r => r = toU ⟨a.bv, b.bv, 0#32, 0#32⟩ ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_add_spec (a b : U4) :
    sha256.hw.arm.add a b ⦃ r => r = toU (Arm.ADD a b) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_or_spec (a b : U4) :
    sha256.hw.arm.or a b ⦃ r => r = toU (Arm.ORR a b) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_and_spec (a b : U4) :
    sha256.hw.arm.and a b ⦃ r => r = toU (Arm.AND a b) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_shr16_spec (a : U4) :
    sha256.hw.arm.shr16 a ⦃ r => r = toU (Arm.USHR a 16) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_shl16_spec (a : U4) :
    sha256.hw.arm.shl16 a ⦃ r => r = toU (Arm.SHL a 16) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_ext2_spec (a b : U4) :
    sha256.hw.arm.ext2 a b ⦃ r => r = toU (Arm.EXT2 a b) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_ext3_spec (a b : U4) :
    sha256.hw.arm.ext3 a b ⦃ r => r = toU (Arm.EXT3 a b) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_sha256h_spec (a b w : U4) :
    sha256.hw.arm.sha256h a b w ⦃ r => r = toU (Arm.SHA256H a b w) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_sha256h2_spec (a b w : U4) :
    sha256.hw.arm.sha256h2 a b w ⦃ r => r = toU (Arm.SHA256H2 a b w) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_sha256su0_spec (a b : U4) :
    sha256.hw.arm.sha256su0 a b ⦃ r => r = toU (Arm.SHA256SU0 a b) ⦄ := (WP.spec_ok _).mpr rfl
@[step] theorem hw_sha256su1_spec (a b c : U4) :
    sha256.hw.arm.sha256su1 a b c ⦃ r => r = toU (Arm.SHA256SU1 a b c) ⦄ := (WP.spec_ok _).mpr rfl

@[step]
theorem hw_load_words_spec (w : Slice U32) (at' : Usize) (h : at'.val + 4 ≤ w.length) :
    sha256.hw.arm.load_words w at' ⦃ r => r = toU (vOf (wv w.val) at'.val) ⦄ := by
  unfold sha256.hw.arm.load_words
  rw [if_pos (by scalar_tac)]
  simp only [vOf, toU]
  rw [wv_getElem! _ _ (by scalar_tac), wv_getElem! _ _ (by scalar_tac),
    wv_getElem! _ _ (by scalar_tac), wv_getElem! _ _ (by scalar_tac),
    getElem!_eq _ _ (by scalar_tac), getElem!_eq _ _ (by scalar_tac),
    getElem!_eq _ _ (by scalar_tac), getElem!_eq _ _ (by scalar_tac)]
  exact (WP.spec_ok _).mpr rfl

@[step]
theorem hw_load_be_spec (b : Slice U8) (at' : Usize) (h : at'.val + 16 ≤ b.length) :
    sha256.hw.arm.load_be b at' ⦃ r => r = toU (beV (bytes b.val) at'.val) ⦄ := by
  unfold sha256.hw.arm.load_be
  rw [if_pos (by scalar_tac)]
  simp only [beV, word, Arm.beWord, Nat.add_assoc, Nat.reduceAdd, toU]
  have e : ∀ i, i < 16 → (b.val[at'.val + i]!).bv = (bytes b.val)[at'.val + i]! := by
    intro i hi
    rw [bytes_getElem! _ _ (by scalar_tac), getElem!_eq _ _ (by scalar_tac)]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
    e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega),
    e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega), e 14 (by omega),
    e 15 (by omega)]
  exact (WP.spec_ok _).mpr rfl

theorem set4_self {α} [Inhabited α] (a : Std.Array α 4#usize) (i : Nat) (x : α) (h : i < 4) :
    (a.val.set i x)[i]! = x := getElem!_set_self' _ _ _ (by simp; omega)

theorem get4 {α} [Inhabited α] (a : Std.Array α 4#usize) (i : Nat) (h : i < a.val.length) :
    a.val[i] = a.val[i]! := (getElem!_eq _ _ h).symm

theorem K_slice_eq : wv sha256.K.to_slice.val = K := by rw [Array.val_to_slice, K_eq]

/-- Lane `l` of the working variables of a run. -/
def lane (s : sha256.hw.Lanes) (l : Nat) : LV :=
  (s.x.val[l]!, ⟨s.abcd.val[l]!, s.efgh.val[l]!, (s.m.val[l]!).val⟩)

/-- The step number `i` (1..=15) of lane `LANE` of `L` at tick `J`. -/
def laneI (L J LANE : Nat) : Nat := (J + 15 - 15 * LANE / L) % 15 + 1

theorem off_lt (L LANE : Nat) (h : LANE < L) : 15 * LANE / L < 15 := by
  rw [Nat.div_lt_iff_lt_mul (by omega)]; exact Nat.mul_lt_mul_of_pos_left h (by omega)

/-! ### `lpure` at each kind of step -/

theorem lpure_1 (abcd0 : U4) (sl : sha256.hw.Slot) (T : Word) (v : LV) :
    lpure abcd0 sl T 1 v =
      (v.1, ⟨Arm.SHA256H sl.a1 sl.e1 (Arm.ADD (mkM1 sl.c1 T v.1) (vOf K 4)),
        Arm.SHA256H2 sl.e1 sl.a1 (Arm.ADD (mkM1 sl.c1 T v.1) (vOf K 4)),
        [Arm.SHA256SU1 (Arm.SHA256SU0 sl.m0 (mkM1 sl.c1 T v.1)) (mkM2 sl.c2 v.1) sl.m3,
          Arm.SHA256SU1 (Arm.SHA256SU0 (mkM1 sl.c1 T v.1) (mkM2 sl.c2 v.1)) sl.m3
            (Arm.SHA256SU1 (Arm.SHA256SU0 sl.m0 (mkM1 sl.c1 T v.1)) (mkM2 sl.c2 v.1) sl.m3),
          mkM2 sl.c2 v.1, sl.m3]⟩) := by
  simp [lpure, kstep, initK] <;> rfl

theorem lpure_lt12 (abcd0 : U4) (sl : sha256.hw.Slot) (T : Word) (i : Nat) (v : LV)
    (h1 : i ≠ 1) (h12 : i < 12) :
    lpure abcd0 sl T i v =
      (v.1, ⟨Arm.SHA256H v.2.abcd v.2.efgh (Arm.ADD v.2.m[i % 4]! (vOf K (4 * i))),
        Arm.SHA256H2 v.2.efgh v.2.abcd (Arm.ADD v.2.m[i % 4]! (vOf K (4 * i))),
        v.2.m.set (i % 4) (Arm.SHA256SU1 (Arm.SHA256SU0 v.2.m[i % 4]! v.2.m[(i + 1) % 4]!)
          v.2.m[(i + 2) % 4]! v.2.m[(i + 3) % 4]!)⟩) := by
  simp [lpure, kstep, h1, h12, show i ≠ 15 by omega]

theorem lpure_ge12 (abcd0 : U4) (sl : sha256.hw.Slot) (T : Word) (i : Nat) (v : LV)
    (h1 : 12 ≤ i) (h15 : i < 15) :
    lpure abcd0 sl T i v =
      (v.1, ⟨Arm.SHA256H v.2.abcd v.2.efgh (Arm.ADD v.2.m[i % 4]! (vOf K (4 * i))),
        Arm.SHA256H2 v.2.efgh v.2.abcd (Arm.ADD v.2.m[i % 4]! (vOf K (4 * i))), v.2.m⟩) := by
  simp [lpure, kstep, show i ≠ 1 by omega, show ¬ i < 12 by omega, show i ≠ 15 by omega]

theorem lpure_15 (abcd0 : U4) (sl : sha256.hw.Slot) (T : Word) (v : LV) :
    lpure abcd0 sl T 15 v =
      (Arm.ADD (Arm.SHA256H v.2.abcd v.2.efgh (Arm.ADD v.2.m[15 % 4]! (vOf K (4 * 15)))) abcd0,
        ⟨Arm.SHA256H v.2.abcd v.2.efgh (Arm.ADD v.2.m[15 % 4]! (vOf K (4 * 15))), v.2.efgh, v.2.m⟩) := by
  simp [lpure, kstep]

set_option maxHeartbeats 2000000 in
theorem lane_step_spec (L J LANE : Usize) (abcd0 : U4) (slots : Array sha256.hw.Slot 4#usize)
    (p : U32) (s : sha256.hw.Lanes)
    (hL : L.val ≤ 4) (hLANE : LANE.val < L.val) (hJ : J.val < 15)
    (hp : laneI L.val J.val LANE.val = 1 → (slots.val[LANE.val]!).t.val + p.val ≤ U32.max) :
    sha256.hw.lane_step L J LANE abcd0 slots p s ⦃ r =>
      (∀ l, l ≠ LANE.val → lane r l = lane s l) ∧
      lane r LANE.val = lpure abcd0 (slots.val[LANE.val]!)
        (BitVec.ofNat 32 ((slots.val[LANE.val]!).t.val + p.val)) (laneI L.val J.val LANE.val)
        (lane s LANE.val) ⦄ := by
  have hoff := off_lt L.val LANE.val hLANE
  have hLl : LANE.val < 4 := by omega
  unfold sha256.hw.lane_step
  step*
  have hI : laneI L.val J.val LANE.val = i4.val := by
    unfold laneI; rw [i_post] at off_post; omega
  have hcases : i4.val = 1 ∨ (2 ≤ i4.val ∧ i4.val < 12) ∨ (12 ≤ i4.val ∧ i4.val < 15) ∨
      i4.val = 15 := by omega
  rw [hI]
  rcases hcases with hc | hc | hc | hc
  · rw [hc, lpure_1]
    have hp' := hp (by rw [hI]; exact hc)
    split
    · step as ⟨z, hz⟩
      step as ⟨s2, hs2⟩
      step as ⟨t, ht⟩
      · rw [hs2, ← getElem!_eq _ _ (by simp; omega)]; exact hp'
      have htb : t.bv = BitVec.ofNat 32 ((slots.val[LANE.val]!).t.val + p.val) := by
        rw [← U32.BitVec_ofNat_val, ht, hs2, getElem!_eq _ _ (by simp; omega)]
      step as ⟨uxt0, huxt0⟩
      step as ⟨hi, hhi⟩
      step as ⟨lo, hlo⟩
      step as ⟨i5, hi5, hi5b⟩
      step as ⟨i6, hi6, hi6b⟩
      step*
      subst_vars
      refine ⟨fun l hl => ?_, ?_⟩
      · simp only [lane, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (Ne.symm hl)]
      · simp only [i7_post] at i8_post
        simp only [i9_post] at i10_post
        simp only [i11_post] at i12_post
        simp only [lane, Array.set_val_eq, List.set_set, set4_self _ _ _ hLl, get4, K_slice_eq,
          List.getElem_set_self]
        simp only [Array.make_val]
        simp only [i5_post, i6_post, i8_post, i10_post, i12_post, hc, hi5b, hi6b, htb]
        simp only [toU, mkM1, mkM2]
        rfl
    · exfalso; scalar_tac
  · simp only [eq_false (show ¬ i4 = 1#usize by scalar_tac), eq_true (show i4 < 15#usize by scalar_tac),
      eq_true (show i4 < 12#usize by scalar_tac), eq_false (show ¬ i4 = 15#usize by scalar_tac),
      ↓reduceIte, lpure_lt12 _ _ _ _ _ (by omega : i4.val ≠ 1) hc.2]
    step*
    all_goals
      subst_vars
      refine ⟨fun l hl => ?_, ?_⟩
      · simp only [lane, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (Ne.symm hl)]
      · simp only [i7_post] at i8_post
        simp only [i9_post] at i10_post
        simp only [i11_post] at i12_post
        simp only [lane, Array.set_val_eq, set4_self _ _ _ hLl, get4, K_slice_eq]
        simp only [i5_post, i6_post, i8_post, i10_post, i12_post, toU]
        rfl

  · simp only [eq_false (show ¬ i4 = 1#usize by scalar_tac), eq_true (show i4 < 15#usize by scalar_tac),
      eq_false (show ¬ i4 < 12#usize by scalar_tac), eq_false (show ¬ i4 = 15#usize by scalar_tac),
      ↓reduceIte, lpure_ge12 _ _ _ _ _ hc.1 hc.2]
    step*
    all_goals
      subst_vars
      refine ⟨fun l hl => ?_, ?_⟩
      · simp only [lane, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (Ne.symm hl)]
      · simp only [lane, Array.set_val_eq, set4_self _ _ _ hLl, get4, K_slice_eq,
          List.getElem_set_self]
        simp only [i5_post, i6_post, toU]
        rfl

  · simp only [eq_false (show ¬ i4 = 1#usize by scalar_tac), eq_false (show ¬ i4 < 15#usize by scalar_tac),
      eq_false (show ¬ i4 < 12#usize by scalar_tac), eq_true (show i4 = 15#usize by scalar_tac),
      ↓reduceIte, hc, lpure_15]
    step*
    all_goals
      subst_vars
      refine ⟨fun l hl => ?_, ?_⟩
      · simp only [lane, Array.set_val_eq, getElem!_set_ne' _ _ _ _ (Ne.symm hl)]
      · simp only [lane, Array.set_val_eq, set4_self _ _ _ hLl, get4, K_slice_eq,
          List.getElem_set_self]
        simp only [i5_post, i6_post, toU]
        simp only [hc]; rfl


/-! ## `lane_tick`: a lane's schedule -/

/-- The number of lane steps lane with offset `off` has done before global tick
`G` of a run of `steps` hashes. -/
def gidx (off steps G : Nat) : Nat := min (G - off) (15 * steps)

/-- Period `p` of a run of `steps` hashes has phase `φ`. -/
def PhaseOk (φ p steps : Nat) : Prop :=
  (φ = 0 ∧ p = 0) ∨ (φ = 1 ∧ 1 ≤ p ∧ p < steps) ∨ (φ = 2 ∧ p = steps)

theorem active_arith (off steps p J φ : Nat) (hoff : off < 15) (hJ : J < 15) (hs : 1 ≤ steps)
    (hph : PhaseOk φ p steps) (h0 : φ = 0 → off ≤ J) (h2 : φ = 2 → J < off) :
    gidx off steps (15 * p + J) = 15 * p + J - off ∧
    gidx off steps (15 * p + J + 1) = (15 * p + J - off) + 1 ∧
    (J + 15 - off) % 15 + 1 = (15 * p + J - off) % 15 + 1 ∧
    ((J + 15 - off) % 15 + 1 = 1 → p = (15 * p + J - off) / 15 ∧ p < steps) := by
  unfold gidx PhaseOk at *
  rcases hph with ⟨h, hp⟩ | ⟨h, hp1, hp2⟩ | ⟨h, hp⟩
  · have := h0 h; subst hp; omega
  · omega
  · have := h2 h; subst hp; omega

theorem inactive_arith (off steps p J φ : Nat) (hoff : off < 15) (hJ : J < 15)
    (hph : PhaseOk φ p steps) (hin : (φ = 0 ∧ J < off) ∨ (φ = 2 ∧ off ≤ J)) :
    gidx off steps (15 * p + J + 1) = gidx off steps (15 * p + J) := by
  unfold gidx PhaseOk at *
  omega

theorem lpure_T (abcd0 : U4) (sl : sha256.hw.Slot) (T T' : Word) (i : Nat) (v : LV) (h : i ≠ 1) :
    lpure abcd0 sl T i v = lpure abcd0 sl T' i v := by
  simp [lpure, h]

theorem lane_tick_active (L J LANE : Usize) (abcd0 : U4) (slots : Array sha256.hw.Slot 4#usize)
    (p : U32) (s : sha256.hw.Lanes) (steps : Nat)
    (hL : L.val ≤ 4) (hlv : LANE.val < L.val) (hJ : J.val < 15)
    (hov : LANE.val < L.val → (slots.val[LANE.val]!).t.val + steps ≤ U32.max)
    (ha : gidx (15 * LANE.val / L.val) steps (15 * p.val + J.val) = 15 * p.val + J.val - 15 * LANE.val / L.val ∧
      gidx (15 * LANE.val / L.val) steps (15 * p.val + J.val + 1) =
        (15 * p.val + J.val - 15 * LANE.val / L.val) + 1 ∧
      (J.val + 15 - 15 * LANE.val / L.val) % 15 + 1 =
        (15 * p.val + J.val - 15 * LANE.val / L.val) % 15 + 1 ∧
      ((J.val + 15 - 15 * LANE.val / L.val) % 15 + 1 = 1 →
        p.val = (15 * p.val + J.val - 15 * LANE.val / L.val) / 15 ∧ p.val < steps)) :
    sha256.hw.lane_step L J LANE abcd0 slots p s ⦃ r =>
      (∀ l, l ≠ LANE.val → lane r l = lane s l) ∧
      (LANE.val < L.val →
        Good abcd0 (slots.val[LANE.val]!) (gidx (15 * LANE.val / L.val) steps (15 * p.val + J.val))
          (lane s LANE.val) →
        Good abcd0 (slots.val[LANE.val]!) (gidx (15 * LANE.val / L.val) steps (15 * p.val + J.val + 1))
          (lane r LANE.val)) ∧
      (¬ LANE.val < L.val → lane r LANE.val = lane s LANE.val) ⦄ := by
  obtain ⟨e1, e2, e3, e4⟩ := ha
  have hp : laneI L.val J.val LANE.val = 1 → (slots.val[LANE.val]!).t.val + p.val ≤ U32.max := by
    intro h; have := e4 h; have := hov hlv; omega
  apply WP.spec_mono (lane_step_spec L J LANE abcd0 slots p s hL hlv hJ hp)
  rintro r ⟨h1, h2⟩
  refine ⟨h1, fun _ hg => ?_, fun h => absurd hlv h⟩
  rw [e2, h2]
  rw [e1] at hg
  have hg' := Good_step _ _ _ _ hg
  unfold laneI
  rw [e3]
  by_cases hi1 : (15 * p.val + J.val - 15 * LANE.val / L.val) % 15 + 1 = 1
  · have := (e4 (by rw [e3]; exact hi1)).1
    rw [← this] at hg'
    exact hg'
  · rw [lpure_T _ _ _ _ _ _ hi1]
    exact hg'

theorem lane_tick_spec (L PHASE J LANE : Usize) (abcd0 : U4) (slots : Array sha256.hw.Slot 4#usize)
    (p : U32) (s : sha256.hw.Lanes) (steps : Nat)
    (hL : L.val ≤ 4) (hJ : J.val < 15) (hs : 1 ≤ steps) (hph : PhaseOk PHASE.val p.val steps)
    (hov : LANE.val < L.val → (slots.val[LANE.val]!).t.val + steps ≤ U32.max) :
    sha256.hw.lane_tick L PHASE J LANE abcd0 slots p s ⦃ r =>
      (∀ l, l ≠ LANE.val → lane r l = lane s l) ∧
      (LANE.val < L.val →
        Good abcd0 (slots.val[LANE.val]!) (gidx (15 * LANE.val / L.val) steps (15 * p.val + J.val))
          (lane s LANE.val) →
        Good abcd0 (slots.val[LANE.val]!) (gidx (15 * LANE.val / L.val) steps (15 * p.val + J.val + 1))
          (lane r LANE.val)) ∧
      (¬ LANE.val < L.val → lane r LANE.val = lane s LANE.val) ⦄ := by
  unfold sha256.hw.lane_tick
  by_cases hl : LANE < L
  · have hlv : LANE.val < L.val := by scalar_tac
    have hoff := off_lt L.val LANE.val hlv
    simp only [hl, ↓reduceIte]
    have hph' := hph
    unfold PhaseOk at hph'
    step*
    all_goals rw [i_post] at off_post
    · -- active
      have ha := active_arith (15 * LANE.val / L.val) steps p.val J.val PHASE.val hoff hJ hs hph
        (fun _ => by scalar_tac) (fun _ => by scalar_tac)
      exact lane_tick_active L J LANE abcd0 slots p s steps hL hlv hJ hov ha
    · have e := inactive_arith (15 * LANE.val / L.val) steps p.val J.val PHASE.val hoff hJ hph
        (by scalar_tac)
      exact ⟨fun _ _ => trivial, fun _ hg => e ▸ hg, fun _ => trivial⟩
    · have ha := active_arith (15 * LANE.val / L.val) steps p.val J.val PHASE.val hoff hJ hs hph
        (fun _ => by scalar_tac) (fun _ => by scalar_tac)
      exact lane_tick_active L J LANE abcd0 slots p s steps hL hlv hJ hov ha
    · have ha := active_arith (15 * LANE.val / L.val) steps p.val J.val PHASE.val hoff hJ hs hph
        (fun _ => by scalar_tac) (fun _ => by scalar_tac)
      exact lane_tick_active L J LANE abcd0 slots p s steps hL hlv hJ hov ha
    · have e := inactive_arith (15 * LANE.val / L.val) steps p.val J.val PHASE.val hoff hJ hph
        (by scalar_tac)
      exact ⟨fun _ _ => trivial, fun _ hg => e ▸ hg, fun _ => trivial⟩
  · simp only [hl, ↓reduceIte]
    have hlv : ¬ LANE.val < L.val := by scalar_tac
    exact (WP.spec_ok _).mpr ⟨fun _ _ => rfl, fun h => absurd h hlv, fun _ => rfl⟩

/-! ## `tick` and `period` -/

theorem tick_spec (L PHASE J : Usize) (abcd0 : U4) (slots : Array sha256.hw.Slot 4#usize)
    (p : U32) (s : sha256.hw.Lanes) (steps : Nat)
    (hL : L.val ≤ 4) (hJ : J.val < 15) (hs : 1 ≤ steps) (hph : PhaseOk PHASE.val p.val steps)
    (hov : ∀ l < L.val, (slots.val[l]!).t.val + steps ≤ U32.max)
    (hg : ∀ l < L.val, Good abcd0 (slots.val[l]!) (gidx (15 * l / L.val) steps (15 * p.val + J.val))
      (lane s l)) :
    sha256.hw.tick L PHASE J abcd0 slots p s ⦃ r =>
      ∀ l < L.val, Good abcd0 (slots.val[l]!) (gidx (15 * l / L.val) steps (15 * p.val + J.val + 1))
        (lane r l) ⦄ := by
  unfold sha256.hw.tick
  step with lane_tick_spec L PHASE J 0#usize abcd0 slots p s steps hL hJ hs hph
    (fun h => hov _ h) as ⟨s1, a1, b1, c1⟩
  step with lane_tick_spec L PHASE J 1#usize abcd0 slots p s1 steps hL hJ hs hph
    (fun h => hov _ h) as ⟨s2, a2, b2, c2⟩
  step with lane_tick_spec L PHASE J 2#usize abcd0 slots p s2 steps hL hJ hs hph
    (fun h => hov _ h) as ⟨s3, a3, b3, c3⟩
  apply WP.spec_mono (lane_tick_spec L PHASE J 3#usize abcd0 slots p s3 steps hL hJ hs hph
    (fun h => hov _ h))
  rintro s4 ⟨a4, b4, c4⟩
  simp only [show (3#usize : Usize).val = 3 from rfl] at a4 b4
  intro l hl
  have hl4 : l < 4 := by omega
  interval_cases l
  · rw [a4 0 (by simp), a3 0 (by simp), a2 0 (by simp)]
    exact b1 hl (hg 0 hl)
  · rw [a4 1 (by simp), a3 1 (by simp)]
    apply b2 hl
    rw [a1 1 (by simp)]
    exact hg 1 hl
  · rw [a4 2 (by simp)]
    apply b3 hl
    rw [a2 2 (by simp), a1 2 (by simp)]
    exact hg 2 hl
  · apply b4 hl
    rw [a3 3 (by simp), a2 3 (by simp), a1 3 (by simp)]
    exact hg 3 hl

end slhdsa

import Slhdsa.Proofs.Hw.ChainLoop
open Aeneas Aeneas.Std Result

/-! The main loop of `chain_all` (the single-set tree's `lean-hw/Slhdsa/Proofs/Hw/ChainMain.lean` (git `26aa3d8`)
generalised to the hash length `nh`: a slot's value is the pair `x`, `xb`). -/

namespace slhdsa
open Spec.SHA256

set_option linter.unusedSimpArgs false

/-- A slot after `r` steps of `run`. -/
def advF (nh : Nat) (abcd0 efgh0 : Arm.V) (r : Nat) (sl : sha256.hw.Slot) : sha256.hw.Slot :=
  { sl with x := (Xseq nh abcd0 efgh0 sl r).1, xb := (Xseq nh abcd0 efgh0 sl r).2, t := ⟨BitVec.ofNat 32 (sl.t.val + r)⟩ }

theorem advF_t (nh : Nat) (abcd0 efgh0 : Arm.V) (r : Nat) (sl : sha256.hw.Slot) (h : sl.t.val + r < 2 ^ 32) :
    (advF nh abcd0 efgh0 r sl).t.val = sl.t.val + r := by
  simp only [advF]
  show (BitVec.ofNat 32 (sl.t.val + r)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem adv_eq (nh : Nat) (abcd0 efgh0 : Arm.V) (r : Nat) (sl sl' : sha256.hw.Slot)
    (h : Adv sl sl' (Xseq nh abcd0 efgh0 sl r) r) (hr : sl.t.val + r < 2 ^ 32) :
    sl' = advF nh abcd0 efgh0 r sl := by
  obtain ⟨h1, h2⟩ := h
  rw [h1]
  unfold advF
  congr 1
  apply U32.bv_eq_imp_eq
  show sl'.t.bv = BitVec.ofNat 32 (sl.t.val + r)
  rw [← h2]; exact (U32.BitVec_ofNat_val _).symm

theorem run_dispatch (N n : Usize) (state : Array U32 8#usize) (slots : Array sha256.hw.Slot 4#usize)
    (r : U32) (h1 : 1 ≤ n.val) (h4 : n.val ≤ 4) :
    (if n = 4#usize then sha256.hw.run N 4#usize state slots r
      else if n = 3#usize then sha256.hw.run N 3#usize state slots r
      else if n = 2#usize then sha256.hw.run N 2#usize state slots r
      else sha256.hw.run N 1#usize state slots r) = sha256.hw.run N n state slots r := by
  split_ifs with ha hb hc
  · rw [ha]
  · rw [hb]
  · rw [hc]
  · have : n = 1#usize := by scalar_tac
    rw [this]

theorem run_take (nh : Nat) (L : Nat) (hL : L ≤ 4) (abcd0 efgh0 : Arm.V) (r : Nat)
    (slots S : Array sha256.hw.Slot 4#usize)
    (hov : ∀ l < L, (slots.val[l]!).t.val + r < 2 ^ 32)
    (h : ∀ l < 4, (l < L → Adv (slots.val[l]!) (S.val[l]!) (Xseq nh abcd0 efgh0 (slots.val[l]!) r) r)) :
    S.val.take L = (slots.val.take L).map (advF nh abcd0 efgh0 r) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < L := by simp at h1; omega
    simp only [List.getElem_take, List.getElem_map]
    rw [← getElem!_eq S.val i (by simp; omega), ← getElem!_eq slots.val i (by simp; omega)]
    exact adv_eq _ _ _ _ _ _ (h i (by omega) hi) (hov i hi)

theorem sum_sub_lt (A : List sha256.hw.Slot) (f : sha256.hw.Slot → Nat) (r : Nat) (hr : 1 ≤ r)
    (hne : A ≠ []) (hle : ∀ sl ∈ A, r ≤ f sl) :
    (A.map (fun sl => f sl - r)).sum < (A.map f).sum := by
  induction A with
  | nil => exact absurd rfl hne
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := hle a (by simp)
    by_cases hA : A = []
    · subst hA; simp; omega
    · have := ih hA (fun sl hs => hle sl (by simp [hs]))
      omega

theorem sum_filter_le (A : List sha256.hw.Slot) (f : sha256.hw.Slot → Nat) (p : sha256.hw.Slot → Bool) :
    ((A.filter p).map f).sum ≤ (A.map f).sum := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    split
    · simp only [List.map_cons, List.sum_cons]; omega
    · omega

theorem pw_inj (A : List sha256.hw.Slot) (hpw : A.Pairwise (fun a b => a.lane.val < b.lane.val))
    (a b : sha256.hw.Slot) (ha : a ∈ A) (hb : b ∈ A) (h : a.lane.val = b.lane.val) : a = b := by
  induction A with
  | nil => simp at ha
  | cons c A ih =>
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; have := hpw.1 _ hb'; omega
    · subst hb'; have := hpw.1 _ ha'; omega
    · exact ih hpw.2 ha' hb'

/-! ## The invariant of the main loop -/

section
variable (nh : Nat) (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize)) (start «end» : Slice U32)

/-- Slot `sl` holds chain `sl.lane`, `sl.t − start` steps in, with steps left. -/
def SlotInv (sl : sha256.hw.Slot) : Prop :=
  sl.lane.val < blocks0.length ∧
  SlotOk nh (wv state.val) (bytes (blocks0.val[sl.lane.val]!).val) sl ∧
  (start.val[sl.lane.val]!).val ≤ sl.t.val ∧ sl.t.val < sl.end.val ∧
  sl.end.val = («end».val[sl.lane.val]!).val ∧
  (sl.x, sl.xb) = Yseq nh (wv state.val) (bytes (blocks0.val[sl.lane.val]!).val) (start.val[sl.lane.val]!).val
    (sl.t.val - (start.val[sl.lane.val]!).val)

/-- The invariant of the main loop of `chain_all`: the chains before `next` are
finished in memory or in a slot (with their block untouched); the others are
untouched. -/
def MInv (blocks : Slice (Array U8 64#usize)) (slots : Array sha256.hw.Slot 4#usize)
    (first : sha256.hw.First) (n next : Nat) : Prop :=
  n ≤ 4 ∧ next ≤ blocks0.length ∧ blocks.length = blocks0.length ∧ FirstOk (wv state.val) first ∧
  (∀ sl ∈ slots.val.take n, SlotInv nh state blocks0 start «end» sl ∧ sl.lane.val < next) ∧
  (slots.val.take n).Pairwise (fun a b => a.lane.val < b.lane.val) ∧
  (∀ i < blocks0.length, (next ≤ i ∨ ∃ sl ∈ slots.val.take n, sl.lane.val = i) →
    blocks.val[i]! = blocks0.val[i]!) ∧
  (∀ i < blocks0.length, i < next → (∀ sl ∈ slots.val.take n, sl.lane.val ≠ i) →
    bytes (blocks.val[i]!).val = runBlock nh (wv state.val) (bytes (blocks0.val[i]!).val)
      (start.val[i]!).val («end».val[i]!).val)

end

/-- The measure of the main loop. -/
def Mmeas (len next : Nat) (A : List sha256.hw.Slot) : Nat :=
  (len - next) * 2 ^ 35 + (A.map (fun sl => sl.end.val - sl.t.val)).sum

theorem SlotOk_advF (nh : Nat) (st : List Word) (B : Spec.Bytes) (abcd0 efgh0 : Arm.V) (r : Nat)
    (sl : sha256.hw.Slot) : SlotOk nh st B (advF nh abcd0 efgh0 r sl) = SlotOk nh st B sl := rfl

theorem take_ne_nil (l : List sha256.hw.Slot) (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ l.length) :
    l.take n ≠ [] := by
  intro h; have := congrArg List.length h; rw [List.length_take, List.length_nil] at this; omega

theorem u32_lt (x : U32) : x.val < 2 ^ 32 := by
  scalar_tac

/-- After a run of `r` steps and the write-back. -/
theorem run_branch_inv (nh : Nat) (hnh : KN nh) (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize))
    (start «end» : Slice U32) (blocks : Slice (Array U8 64#usize)) (slots : Array sha256.hw.Slot 4#usize)
    (first : sha256.hw.First) (n next : Nat)
    (hI : MInv nh state blocks0 start «end» blocks slots first n next) (hn1 : 1 ≤ n) (r : Nat) (hr1 : 1 ≤ r)
    (hr : ∀ sl ∈ slots.val.take n, r ≤ sl.end.val - sl.t.val)
    (S : Array sha256.hw.Slot 4#usize)
    (hS : S.val.take n = (slots.val.take n).map (advF nh (vOf (wv state.val) 0) (vOf (wv state.val) 4) r))
    (blocks' : Slice (Array U8 64#usize)) (slots2 : Array sha256.hw.Slot 4#usize) (k : Nat)
    (hC : CInv nh n blocks S blocks' slots2 k n) :
    MInv nh state blocks0 start «end» blocks' slots2 first k next ∧
    Mmeas blocks0.length next (slots2.val.take k) < Mmeas blocks0.length next (slots.val.take n) := by
  obtain ⟨hn4, hnext, hlen, hf, hA, hpw, hmem, hfin⟩ := hI
  obtain ⟨hkn, -, hlen', hk, -, hd, hu⟩ := hC
  set a := vOf (wv state.val) 0 with ha
  set ef := vOf (wv state.val) 4 with hef
  set A := slots.val.take n with hAdef
  have hst : (wv state.val).length = 8 := by simp
  -- facts about the advanced slots
  have hbound : ∀ sl ∈ A, sl.t.val + r < 2 ^ 32 := by
    intro sl hsl; have := hr sl hsl; have := (hA sl hsl).1.2.2.2.1; have := u32_lt sl.end; omega
  have hlane : ∀ sl, (advF nh a ef r sl).lane = sl.lane := fun _ => rfl
  have hend : ∀ sl, (advF nh a ef r sl).end = sl.end := fun _ => rfl
  have hpwS : (S.val.take n).Pairwise (fun a b => a.lane.val < b.lane.val) := by
    rw [hS, List.pairwise_map]; exact hpw
  have hmemS : ∀ sl, sl ∈ S.val.take n ↔ ∃ sl0 ∈ A, advF nh a ef r sl0 = sl := by
    intro sl; rw [hS, List.mem_map]
  have hA' : slots2.val.take k = (S.val.take n).filter keepB := hk
  refine ⟨⟨by omega, hnext, by rw [hlen', hlen], hf, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- the slots still running
    intro sl hsl
    rw [hA', List.mem_filter] at hsl
    obtain ⟨hsl, hkp⟩ := hsl
    obtain ⟨sl0, hsl0, rfl⟩ := (hmemS sl).mp hsl
    obtain ⟨⟨hl0, hok0, hs0, ht0, he0, hx0⟩, hln0⟩ := hA sl0 hsl0
    have ht := advF_t nh a ef r sl0 (hbound sl0 hsl0)
    simp only [keepB, decide_eq_true_eq] at hkp
    have hB : (bytes (blocks0.val[sl0.lane.val]!).val).length = 64 := by simp
    refine ⟨⟨hl0, hok0, ?_, hkp, he0, ?_⟩, hln0⟩
    · show (start.val[sl0.lane.val]!).val ≤ (advF nh a ef r sl0).t.val
      rw [ht]; omega
    · show Xseq nh a ef sl0 r = Yseq nh _ (bytes (blocks0.val[sl0.lane.val]!).val) (start.val[sl0.lane.val]!).val
        ((advF nh a ef r sl0).t.val - (start.val[sl0.lane.val]!).val)
      rw [ht, Xseq_Yseq _ hnh _ hst _ hB _ sl0 hok0 hs0 hx0 r (by have := hbound sl0 hsl0; omega)]
      congr 1; omega
  · rw [hA']; exact hpwS.filter _
  · -- untouched blocks
    intro i hi h
    rw [hu i ?_]
    · apply hmem i hi
      rcases h with h | ⟨sl1, hsl1, hl1⟩
      · exact Or.inl h
      · right
        rw [hA', List.mem_filter] at hsl1
        obtain ⟨sl0, hsl0, rfl⟩ := (hmemS sl1).mp hsl1.1
        exact ⟨sl0, hsl0, hl1⟩
    · intro sl hsl hkp hli
      rcases h with h | ⟨sl1, hsl1, hl1⟩
      · obtain ⟨sl0, hsl0, rfl⟩ := (hmemS sl).mp hsl
        have := (hA sl0 hsl0).2; rw [hlane] at hli; omega
      · rw [hA', List.mem_filter] at hsl1
        have := pw_inj _ hpwS sl sl1 hsl hsl1.1 (by rw [hli, hl1])
        rw [this, hsl1.2] at hkp; cases hkp
  · -- finished chains
    intro i hi hin hnot
    by_cases hex : ∃ sl0 ∈ A, sl0.lane.val = i
    · obtain ⟨sl0, hsl0, hl0⟩ := hex
      have hslS : advF nh a ef r sl0 ∈ S.val.take n := (hmemS _).mpr ⟨sl0, hsl0, rfl⟩
      have hkf : keepB (advF nh a ef r sl0) = false := by
        cases hkb : keepB (advF nh a ef r sl0)
        · rfl
        · exact absurd hl0 (hnot (advF nh a ef r sl0) (by rw [hA', List.mem_filter]; exact ⟨hslS, hkb⟩))
      have hw := hd _ hslS hkf
      rw [hlane, hl0] at hw
      rw [hw, hmem i hi (Or.inr ⟨sl0, hsl0, hl0⟩)]
      obtain ⟨⟨hl0', hok0, hs0, ht0, he0, hx0⟩, hln0⟩ := hA sl0 hsl0
      have ht := advF_t nh a ef r sl0 (hbound sl0 hsl0)
      simp only [keepB, decide_eq_false_iff_not, hend] at hkf
      have hrr := hr sl0 hsl0
      rw [hl0] at hs0 he0 hx0 hok0
      have hte : sl0.t.val + r = («end».val[i]!).val := by omega
      have hB : (bytes (blocks0.val[i]!).val).length = 64 := by simp
      have e1 := runBlock_Yseq nh hnh (wv state.val) _ hB (start.val[i]!).val
        (sl0.t.val + r - 1 - (start.val[i]!).val)
      rw [show (start.val[i]!).val + (sl0.t.val + r - 1 - (start.val[i]!).val + 1) =
        («end».val[i]!).val by omega] at e1
      rw [e1, ht]
      show setBlk nh _ (sl0.t.val + r - 1) (Xseq nh a ef sl0 r).1 (Xseq nh a ef sl0 r).2 = _
      rw [Xseq_Yseq _ hnh _ hst _ hB _ sl0 hok0 hs0 hx0 r (by have := hbound sl0 hsl0; omega)]
      have hidx : sl0.t.val - (start.val[i]!).val + r = sl0.t.val + r - 1 - (start.val[i]!).val + 1 := by
        omega
      have hc : (start.val[i]!).val + (sl0.t.val + r - 1 - (start.val[i]!).val) = sl0.t.val + r - 1 := by
        omega
      rw [hidx, hc]
    · have hno : ∀ sl ∈ A, sl.lane.val ≠ i := fun sl hsl h => hex ⟨sl, hsl, h⟩
      rw [hu i (fun sl hsl _ => by
        obtain ⟨sl0, hsl0, rfl⟩ := (hmemS sl).mp hsl
        rw [hlane]; exact hno sl0 hsl0)]
      exact hfin i hi hin hno
  · -- the measure
    unfold Mmeas
    have h1 := sum_filter_le (S.val.take n) (fun sl => sl.end.val - sl.t.val) keepB
    rw [← hA'] at h1
    have h2 : ((S.val.take n).map (fun sl => sl.end.val - sl.t.val)).sum =
        (A.map (fun sl => (sl.end.val - sl.t.val) - r)).sum := by
      rw [hS, List.map_map]
      congr 1
      apply List.map_congr_left
      intro sl hsl
      simp only [Function.comp, hend, advF_t nh a ef r sl (hbound sl hsl)]
      omega
    have h3 := sum_sub_lt A (fun sl => sl.end.val - sl.t.val) r hr1
      (take_ne_nil _ _ hn1 (by simp; omega)) hr
    omega

/-- After entering chain `next` into slot `n`. -/
theorem enter_inv (nh : Nat) (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize))
    (start «end» : Slice U32) (blocks : Slice (Array U8 64#usize)) (slots : Array sha256.hw.Slot 4#usize)
    (first : sha256.hw.First) (n next : Nat)
    (hI : MInv nh state blocks0 start «end» blocks slots first n next) (hn : n < 4)
    (hnx : next < blocks0.length) (sl : sha256.hw.Slot) (f' : sha256.hw.First)
    (hf' : FirstOk (wv state.val) f')
    (hok : SlotOk nh (wv state.val) (bytes (blocks0.val[next]!).val) sl)
    (hx : sl.x = beV (bytes (blocks0.val[next]!).val) 22)
    (hxb : sl.xb = xb0 nh (bytes (blocks0.val[next]!).val))
    (ht : sl.t.val = (start.val[next]!).val) (he : sl.end.val = («end».val[next]!).val)
    (hl : sl.lane.val = next) (hse : sl.t.val < sl.end.val) (nU : Usize) (hnU : nU.val = n) :
    MInv nh state blocks0 start «end» blocks (slots.set nU sl) f' (n + 1) (next + 1) ∧
    Mmeas blocks0.length (next + 1) ((slots.set nU sl).val.take (n + 1)) <
      Mmeas blocks0.length next (slots.val.take n) := by
  obtain ⟨hn4, hnext, hlen, hf, hA, hpw, hmem, hfin⟩ := hI
  have htake : (slots.set nU sl).val.take (n + 1) = slots.val.take n ++ [sl] := by
    rw [Array.set_val_eq, hnU]; exact take_set_succ _ _ _ (by simp; omega)
  unfold MInv
  rw [htake]
  refine ⟨⟨by omega, by omega, hlen, hf', ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro sl' hsl'
    rcases List.mem_append.mp hsl' with h | h
    · exact ⟨(hA sl' h).1, by have := (hA sl' h).2; omega⟩
    · rw [List.mem_singleton.mp h]
      refine ⟨⟨by omega, by rw [hl]; exact hok, by rw [hl, ht], hse, by rw [hl, he], ?_⟩, by omega⟩
      rw [hl, ht, Nat.sub_self, hx, hxb]; rfl
  · rw [List.pairwise_append]
    refine ⟨hpw, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton.mp hb, hl]; exact (hA a ha).2
  · intro i hi h
    apply hmem i hi
    rcases h with h | ⟨sl', hsl', hl'⟩
    · exact Or.inl (by omega)
    · rcases List.mem_append.mp hsl' with h | h
      · exact Or.inr ⟨sl', h, hl'⟩
      · rw [List.mem_singleton.mp h] at hl'; exact Or.inl (by omega)
  · intro i hi hin hno
    have hne : i ≠ next := fun h => hno sl (by simp) (by rw [hl, h])
    exact hfin i hi (by omega) (fun sl' hsl' => hno sl' (List.mem_append_left _ hsl'))
  · unfold Mmeas
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have := u32_lt sl.end
    have : blocks0.length - next = (blocks0.length - (next + 1)) + 1 := by omega
    rw [this, Nat.add_mul]
    omega

/-- After skipping chain `next`, which has no steps. -/
theorem skip_inv (nh : Nat) (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize))
    (start «end» : Slice U32) (blocks : Slice (Array U8 64#usize)) (slots : Array sha256.hw.Slot 4#usize)
    (first : sha256.hw.First) (n next : Nat)
    (hI : MInv nh state blocks0 start «end» blocks slots first n next)
    (hnx : next < blocks0.length) (hse : («end».val[next]!).val ≤ (start.val[next]!).val) :
    MInv nh state blocks0 start «end» blocks slots first n (next + 1) ∧
    Mmeas blocks0.length (next + 1) (slots.val.take n) < Mmeas blocks0.length next (slots.val.take n) := by
  obtain ⟨hn4, hnext, hlen, hf, hA, hpw, hmem, hfin⟩ := hI
  refine ⟨⟨hn4, by omega, hlen, hf, fun sl h => ⟨(hA sl h).1, by have := (hA sl h).2; omega⟩, hpw,
    fun i hi h => hmem i hi (by rcases h with h | h; exact Or.inl (by omega); exact Or.inr h), ?_⟩, ?_⟩
  · intro i hi hin hno
    by_cases h : i = next
    · subst h
      rw [hmem i hi (Or.inl (le_refl _)), runBlock_le _ _ _ _ _ hse]
    · exact hfin i hi (by omega) hno
  · unfold Mmeas
    have : blocks0.length - next = (blocks0.length - (next + 1)) + 1 := by omega
    rw [this, Nat.add_mul]
    omega

theorem done_inv (nh : Nat) (state : Array U32 8#usize) (blocks0 : Slice (Array U8 64#usize))
    (start «end» : Slice U32) (blocks : Slice (Array U8 64#usize)) (slots : Array sha256.hw.Slot 4#usize)
    (first : sha256.hw.First) (next : Nat)
    (hI : MInv nh state blocks0 start «end» blocks slots first 0 next) (hnx : blocks0.length ≤ next) :
    blocks.length = blocks0.length ∧ ∀ i, i < blocks0.length → bytes (blocks.val[i]!).val =
      runBlock nh (wv state.val) (bytes (blocks0.val[i]!).val) (start.val[i]!).val («end».val[i]!).val := by
  obtain ⟨hn4, hnext, hlen, hf, hA, hpw, hmem, hfin⟩ := hI
  exact ⟨hlen, fun i hi => hfin i hi (by omega) (fun sl h => by simp at h)⟩

end slhdsa

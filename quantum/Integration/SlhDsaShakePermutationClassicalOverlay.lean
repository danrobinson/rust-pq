import Integration.SlhDsaShakePermutationClassicalEvidence

/-! A private prefix trie can be superimposed on the public permutation
transcript as soon as its unexposed capacities avoid the visible ones. -/
namespace Reduction.ShakePermutation.Classic
open Classical
noncomputable section

def active {T : ℕ} (r : Report T) := r.privateRows ∪ r.seen
def tracked {T : ℕ} (r : Report T) (p : List Rate) :=
  (∃ s, Trail r.edges p s) ∨ (p.length ≤ T ∧ p ≠ [] ∧ rowId T p ∈ hidden r)

def Separated {T : ℕ} (H : Row T → Words) (r : Report T) :=
  ¬leaked (hidden r) (denied r) (fun i => capOf (H i))

theorem visible_src {T : ℕ} (r : Report T) {a b} (e : (a,b) ∈ r.edges) : capOf a ∈ denied r := by
  unfold denied forbidden
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨(a,b),e,rfl⟩))))

theorem visible_dst {T : ℕ} (r : Report T) {a b} (e : (a,b) ∈ r.edges) : capOf b ∈ denied r := by
  unfold denied forbidden
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨(a,b),e,rfl⟩))))

theorem trail_denied {T : ℕ} (r : Report T) {p s} (h : Trail r.edges p s) : capOf s ∈ denied r := by
  cases h with
  | root => exact Finset.mem_insert.mpr (Or.inl rfl)
  | step _ e _ => exact visible_dst r e

theorem hidden_state {T : ℕ} (H : Row T → Words) {p : List Rate} (ne : p ≠ []) :
    bankState T H p = H (rowId T p) := by cases p with | nil => contradiction | cons => rfl

theorem hidden_off {T : ℕ} {H : Row T → Words} {r : Report T} (ok : Separated H r)
    {i : Row T} (h : i ∈ hidden r) : capOf (H i) ∉ denied r := fun mem => ok (Or.inl ⟨i,h,mem⟩)

theorem tracked_cap {T : ℕ} {H : Row T → Words} {r : Report T} (ev : Evidence T H r)
    (ok : Separated H r) {p q : List Rate} (hp : tracked r p) (hq : tracked r q)
    (eq : capOf (bankState T H p) = capOf (bankState T H q)) : p = q := by
  rcases hp with ⟨s,hs⟩|⟨lp,pne,ph⟩ <;> rcases hq with ⟨z,hz⟩|⟨lq,qne,qh⟩
  · rw [ev.wires.state_ok hs,ev.wires.state_ok hz] at eq
    exact (ev.wires.unique hs hz eq).1
  · rw [ev.wires.state_ok hs,hidden_state _ qne] at eq
    exact False.elim (hidden_off ok qh (eq ▸ trail_denied r hs))
  · rw [hidden_state _ pne,ev.wires.state_ok hz] at eq
    exact False.elim (hidden_off ok ph (eq.symm ▸ trail_denied r hz))
  · apply rowId_inj lp lq
    by_contra ne
    rw [hidden_state _ pne,hidden_state _ qne] at eq
    exact ok (Or.inr ⟨_,ph,_,qh,ne,eq⟩)

theorem known_trail {T : ℕ} {H : Row T → Words} {r : Report T} (ev : Evidence T H r)
    (room : r.edges.length ≤ T) {p : List Rate} (len : p.length ≤ T) (mem : rowId T p ∈ r.seen) :
    ∃ s, Trail r.edges p s := by
  have w := ev.wires.used _ mem
  have mark : rowId T p = .inl (BList.ofList p len) := by simp only [rowId,dite_eq_left len]
  rw [mark] at w
  obtain ⟨q,s,hs,e⟩ := w
  have eq := rowId_inj ((ev.wires.short hs).trans room) len (e.trans mark.symm)
  exact ⟨s,eq ▸ hs⟩

theorem tracked_private {T : ℕ} {H : Row T → Words} {r : Report T} (ev : Evidence T H r)
    (room : r.edges.length ≤ T) {p : List Rate} (len : p.length ≤ T) (mem : rowId T p ∈ r.privateRows) : tracked r p := by
  by_cases pn : p = []
  · exact Or.inl (pn ▸ ⟨_,Trail.root⟩)
  by_cases known : rowId T p ∈ r.seen
  · exact Or.inl (known_trail ev room len known)
  · exact Or.inr ⟨len,pn,Finset.mem_sdiff.mpr ⟨mem,known⟩⟩

inductive Role {T : ℕ} (r : Report T) : Row T → Prop
  | child (p : List Rate) (b : Rate) (len : (p++[b]).length ≤ T) (parent : tracked r p)
      (current : tracked r (p++[b])) : Role r (rowId T (p++[b]))
  | side (u : Port) (mem : .inr u ∈ r.seen) : Role r (.inr u)

theorem role_active {T : ℕ} {H : Row T → Words} {r : Report T} (ev : Evidence T H r)
    (room : r.edges.length ≤ T) {j : Row T} (mem : j ∈ active r) : Role r j := by
  rcases Finset.mem_union.mp mem with priv|pub
  · obtain ⟨p,b,len,rfl,par⟩ := ev.parents _ priv
    have lp : p.length ≤ T := by simp at len; omega
    refine .child p b len ?_ (tracked_private ev room len priv)
    rcases par with rfl|par
    · exact Or.inl ⟨_,Trail.root⟩
    · exact tracked_private ev room lp par
  · cases j with
    | inr u => exact .side u pub
    | inl a =>
      obtain ⟨p,s,hp,eq⟩ := ev.wires.used _ pub
      cases p using List.reverseRecOn with
      | nil =>
        have pos := ev.nonempty a pub
        simp only [rowId,List.length_nil,Nat.zero_le,dite_true,Sum.inl.injEq] at eq
        subst a
        exact False.elim ((Nat.lt_irrefl 0) pos)
      | append_singleton p b =>
        rw [← eq]
        obtain ⟨z,_,hz,_⟩ := hp.lastEdge
        exact .child p b ((ev.wires.short hp).trans room) (Or.inl ⟨_,hz⟩) (Or.inl ⟨_,hp⟩)

theorem snoc_wire {T : ℕ} (H : Row T → Words) (p : List Rate) (b : Rate) (len : (p++[b]).length ≤ T) :
    wire T H (rowId T (p++[b])) = (join (rateXor b (rateOf (bankState T H p))) (capOf (bankState T H p)),
      bankState T H (p++[b])) := by rw [wire,snoc_demand _ _ _ _ len,snoc_state]; rfl

theorem seen_injective {T : ℕ} {H : Row T → Words} {r : Report T} (ev : Evidence T H r)
    {j k} (hj : j ∈ r.seen) (hk : k ∈ r.seen)
    (eq : (wire T H j).1 = (wire T H k).1 ∨ (wire T H j).2 = (wire T H k).2) : j = k := by
  obtain ⟨π⟩ := ev.wires.compatible
  have a := π.property _ (ev.wires.recorded _ hj)
  have b := π.property _ (ev.wires.recorded _ hk)
  apply ev.wires.distinct _ hj _ hk
  rcases eq with eq|eq
  · exact Prod.ext eq (a.symm.trans ((congrArg π.val eq).trans b))
  · exact Prod.ext (π.val.injective (a.trans (eq.trans b.symm))) eq

private theorem offset_side {T : ℕ} {H : Row T → Words} {r : Report T} (ev : Evidence T H r)
    (ok : Separated H r) {p} (hp : tracked r p) {u : Port} (hu : .inr u ∈ r.seen) :
    capOf (bankState T H p) ≠ capOf (wire T H (.inr u)).1 := by
  rcases hp with ⟨s,tr⟩|⟨_,ne,hidden⟩
  · rw [ev.wires.state_ok tr]; exact (ev.wires.outside _ hu tr).symm
  · rw [hidden_state _ ne]
    exact fun eq => hidden_off ok hidden (eq.symm ▸ visible_src r (ev.wires.recorded _ hu))

theorem overlay_sources {T : ℕ} {H : Row T → Words} {r : Report T} (ev : Evidence T H r)
    (room : r.edges.length ≤ T) (ok : Separated H r) {j k : Row T} (hj : j ∈ active r) (hk : k ∈ active r)
    (eq : (wire T H j).1 = (wire T H k).1) : j = k := by
  rcases role_active ev room hj with ⟨p,b,l,p0,p1⟩|⟨u,hu⟩ <;>
    rcases role_active ev room hk with ⟨q,c,m,q0,q1⟩|⟨v,hv⟩
  · rw [snoc_wire _ _ _ l,snoc_wire _ _ _ m] at eq
    have e := congrArg capOf eq; simp only [cap_join] at e
    obtain rfl := tracked_cap ev ok p0 q0 e
    have a := congrArg (fun s => rateXor (rateOf s) (rateOf (bankState T H p))) eq
    simp only [rate_join,rateXor_cancel] at a
    rw [a]
  · rw [snoc_wire _ _ _ l] at eq
    exact False.elim (offset_side ev ok p0 hv (by simpa only [cap_join] using congrArg capOf eq))
  · rw [snoc_wire _ _ _ m] at eq
    exact False.elim (offset_side ev ok q0 hu (by simpa only [cap_join] using congrArg capOf eq.symm))
  · exact seen_injective ev hu hv (Or.inl eq)

theorem overlay_targets {T : ℕ} {H : Row T → Words} {r : Report T} (ev : Evidence T H r)
    (room : r.edges.length ≤ T) (ok : Separated H r) {j k : Row T} (hj : j ∈ active r) (hk : k ∈ active r)
    (eq : (wire T H j).2 = (wire T H k).2) : j = k := by
  by_cases pubj : j ∈ r.seen
  · by_cases pubk : k ∈ r.seen
    · exact seen_injective ev pubj pubk (Or.inr eq)
    · have hidden : k ∈ hidden r := Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp hk).resolve_right pubk,pubk⟩
      rcases role_active ev room hk with ⟨q,c,m,_,_⟩|⟨_,hk'⟩
      · rw [snoc_wire _ _ _ m,snoc_state] at eq
        exact False.elim (hidden_off ok hidden (congrArg capOf eq ▸ visible_dst r (ev.wires.recorded _ pubj)))
      · contradiction
  · have hidden : j ∈ hidden r := Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp hj).resolve_right pubj,pubj⟩
    rcases role_active ev room hj with ⟨p,b,l,_,p1⟩|⟨_,hj'⟩
    · rcases role_active ev room hk with ⟨q,c,m,_,q1⟩|⟨v,hv⟩
      · rw [snoc_wire _ _ _ l,snoc_wire _ _ _ m] at eq
        rw [tracked_cap ev ok p1 q1 (congrArg capOf eq)]
      · rw [snoc_wire _ _ _ l,snoc_state] at eq
        exact False.elim (hidden_off ok hidden ((congrArg capOf eq).symm ▸ visible_dst r (ev.wires.recorded _ hv)))
    · contradiction

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.overlay_sources
#print axioms Reduction.ShakePermutation.Classic.overlay_targets

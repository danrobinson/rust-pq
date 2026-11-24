import Integration.SlhDsaShakePermutationClassicalForestBound

/-! Recovering ordinary SHAKE block paths from classical two-way permutation records. -/
namespace Reduction.ShakePermutation.Classic
open Classical
noncomputable section

def nextBlock (s x : Words) := rateXor (rateOf x) (rateOf s)

inductive Trail (t : EdgeTrace Words) : List Rate → Words → Prop
  | root : Trail t [] 0
  | step {p s x y} : Trail t p s → (x,y) ∈ t → capOf s = capOf x →
      Trail t (p ++ [nextBlock s x]) y

theorem Trail.weaken {t u : EdgeTrace Words} (sub : ∀ e ∈ t, e ∈ u)
    {p s} (h : Trail t p s) : Trail u p s := by
  induction h with
  | root => exact .root
  | step _ e c ih => exact .step ih (sub _ e) c

theorem Trail.eval {t : EdgeTrace Words} (π : Permutation) (ok : ∀ x y, (x,y) ∈ t → π x = y)
    {p s} (h : Trail t p s) : Fix.ordinary π p = s := by
  induction h with
  | root => rfl
  | @step p s x y _ he hc ih =>
    change (p ++ [nextBlock s x]).foldl _ 0 = _
    rw [List.foldl_append]
    change π (join (rateXor (nextBlock s x) (rateOf (Fix.ordinary π p))) (capOf (Fix.ordinary π p))) = y
    rw [ih,nextBlock,rateXor_cancel,hc,join_split]
    exact ok _ _ he

def isolated (t : EdgeTrace Words) (x y : Words) := capOf y ∉ forbidden wordSplit 0 t x

theorem isolate_parts {t : EdgeTrace Words} {x y} (h : isolated t x y) :
    capOf y ≠ 0 ∧ capOf y ≠ capOf x ∧
      ∀ a b, (a,b) ∈ t → capOf y ≠ capOf a ∧ capOf y ≠ capOf b := by
  change capOf y ∉ insert 0 (insert (capOf x)
    ((t.map (fun e => capOf e.1)).toFinset ∪ (t.map (fun e => capOf e.2)).toFinset)) at h
  simp only [Finset.mem_insert,Finset.mem_union,List.mem_toFinset,not_or] at h
  exact ⟨h.1,h.2.1,fun a b e => ⟨fun eq => h.2.2.1 (List.mem_map.mpr ⟨(a,b),e,eq.symm⟩),
    fun eq => h.2.2.2 (List.mem_map.mpr ⟨(a,b),e,eq.symm⟩)⟩⟩

theorem Trail.separate {t : EdgeTrace Words} {x y p s} (iso : isolated t x y)
    (h : Trail t p s) : capOf y ≠ capOf s := by
  cases h with
  | root => exact (isolate_parts iso).1
  | step _ e _ => exact ((isolate_parts iso).2.2 _ _ e).2

theorem forward_paths {t : EdgeTrace Words} {x y p s} (iso : isolated t x y)
    (h : Trail ((x,y)::t) p s) : Trail t p s ∨
    (s = y ∧ ∃ q z, Trail t q z ∧ capOf z = capOf x ∧ p = q ++ [nextBlock z x]) := by
  induction h with
  | root => exact Or.inl .root
  | @step p s a b _ he hc ih =>
    rcases List.mem_cons.mp he with eq|old
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      rcases ih with prev|⟨rfl,_⟩
      · exact Or.inr ⟨rfl,p,s,prev,hc,rfl⟩
      · exact False.elim ((isolate_parts iso).2.1 hc)
    · rcases ih with prev|⟨rfl,_⟩
      · exact Or.inl (.step prev old hc)
      · exact False.elim (((isolate_parts iso).2.2 _ _ old).1 hc)

theorem inverse_paths {t : EdgeTrace Words} {x y p s} (iso : isolated t x y)
    (h : Trail ((y,x)::t) p s) : Trail t p s := by
  induction h with
  | root => exact .root
  | @step p s a b _ he hc ih =>
    rcases List.mem_cons.mp he with eq|old
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      exact False.elim (ih.separate iso hc.symm)
    · exact .step ih old hc

def UniquePaths (t : EdgeTrace Words) := ∀ ⦃p q s z⦄, Trail t p s → Trail t q z →
  capOf s = capOf z → p = q ∧ s = z

theorem unique_empty : UniquePaths [] := by
  intro p q s z h k _
  cases h with
  | root =>
    cases k with
    | root => exact ⟨rfl,rfl⟩
    | step _ he _ => simp at he
  | step _ he _ => simp at he

theorem unique_forward {t : EdgeTrace Words} {x y} (u : UniquePaths t) (iso : isolated t x y) :
    UniquePaths ((x,y)::t) := by
  intro p q s z a b cap
  rcases forward_paths iso a with ha|⟨rfl,p',s',ha,sc,rfl⟩
  · rcases forward_paths iso b with hb|⟨rfl,_⟩
    · exact u ha hb cap
    · exact False.elim (ha.separate iso cap.symm)
  · rcases forward_paths iso b with hb|⟨rfl,q',z',hb,zc,rfl⟩
    · exact False.elim (hb.separate iso cap)
    · obtain ⟨rfl,rfl⟩ := u ha hb (sc.trans zc.symm)
      exact ⟨rfl,rfl⟩

theorem unique_inverse {t : EdgeTrace Words} {x y} (u : UniquePaths t) (iso : isolated t x y) :
    UniquePaths ((y,x)::t) :=
  by
    intro _ _ _ _ a b cap
    exact u (inverse_paths iso a) (inverse_paths iso b) cap

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.unique_forward

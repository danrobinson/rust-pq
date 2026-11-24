import Integration.SlhDsaShakePermutationClassicalMonitor

namespace Reduction.ShakePermutation.Classic
open Classical
noncomputable section

def view {A : Type} (d : Bool) (e : A × A) := if d then e.swap else e

theorem mem_view {A : Type} (d : Bool) (e : A × A) (t : EdgeTrace A) :
    e ∈ orient d t ↔ ∃ z ∈ t, view d z = e := by
  cases d <;> simp [orient,view,List.mem_map]

theorem view_edge {A : Type} (d : Bool) (x y : A) : view d (edge d x y) = (x,y) := by cases d <;> rfl

structure Assigned {T : ℕ} (H : Row T → Words) (allowed : Finset (Row T)) (m : Monitor (Row T) Words) : Prop where
  owns : ∀ j v, m.values j = some v → v = H j ∧ j ∈ allowed ∧ wire T H j ∈ m.graph
  covers : ∀ e ∈ m.graph, ∃ j, m.values j = some (H j) ∧ wire T H j = e

theorem start_assigned {T : ℕ} (H : Row T → Words) (allowed : Finset (Row T)) :
    Assigned H allowed (start _ _) := ⟨by simp [start],by simp [start]⟩

def NoOverlap {T : ℕ} (H : Row T → Words) (allowed : Finset (Row T)) :=
  ∀ ⦃j k⦄, j ∈ allowed → k ∈ allowed →
    ((wire T H j).1 = (wire T H k).1 ∨ (wire T H j).2 = (wire T H k).2) → j = k

theorem step_assigned {T : ℕ} {H : Row T → Words} {allowed : Finset (Row T)}
    (sep : NoOverlap H allowed) {m : Monitor (Row T) Words} (a : Assigned H allowed m)
    (j : Row T) (d : Bool) (x : Words) (owns : j ∈ allowed) (req : demand T H j = (d,x)) :
    ∃ m', advance H j d x m = some m' ∧ Assigned H allowed m' := by
  have wireEq : wire T H j = edge d x (H j) := by simp only [wire,req]
  have look : view d (wire T H j) = (x,H j) := wireEq ▸ view_edge ..
  have same (u : Words × Words) (hu : u ∈ orient d m.graph) (matchAt : u.1=x ∨ u.2=H j) :
      m.values j = some (H j) ∧ u = (x,H j) := by
    obtain ⟨e,he,vue⟩ := (mem_view d u m.graph).mp hu
    obtain ⟨k,hk,wk⟩ := a.covers e he
    have matchView : (view d (wire T H k)).1 = (view d (wire T H j)).1 ∨
        (view d (wire T H k)).2 = (view d (wire T H j)).2 := by rw [wk,vue,look]; exact matchAt
    have kj := sep (a.owns k _ hk).2.1 owns (by
      cases d <;> simp only [view,Bool.false_eq_true,ite_false,ite_true,Prod.fst_swap,Prod.snd_swap] at matchView
      · exact matchView
      · exact matchView.symm)
    subst k
    exact ⟨hk,vue.symm.trans ((congrArg (view d) wk.symm).trans look)⟩
  unfold advance
  cases hj : m.values j with
  | some v =>
    have own := a.owns j v hj
    have known : old m.graph d x := ⟨H j,(mem_view ..).mpr ⟨_,own.2.2,look⟩⟩
    have val : known.choose = H j := congrArg Prod.snd (same _ known.choose_spec (Or.inl rfl)).2
    simp only [dite_eq_left known,val,own.1,ite_true]
    exact ⟨m,rfl,a⟩
  | none =>
    have missed : ¬old m.graph d x := by
      rintro ⟨v,hv⟩
      have bad := (same _ hv (Or.inl rfl)).1
      simp [hj] at bad
    have unused : freshOut m.graph d (H j) := by
      intro e he eq
      have bad := (same e he (Or.inr eq.symm)).1
      simp [hj] at bad
    simp only [missed,unused,not_true_eq_false,or_self,ite_false]
    refine ⟨_,rfl,?_,?_⟩
    · intro k v e
      by_cases hit : k=j
      · subst k
        change Function.update m.values j (some (H j)) j = some v at e
        simp only [Function.update_self,Option.some.injEq] at e
        exact ⟨e.symm,owns,wireEq ▸ List.mem_cons_self ..⟩
      · have := a.owns k v ((Function.update_of_ne hit _ _).symm.trans e)
        exact ⟨this.1,this.2.1,List.mem_cons_of_mem _ this.2.2⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl|old
      · exact ⟨j,Function.update_self ..,wireEq⟩
      · obtain ⟨k,hk,wk⟩ := a.covers e old
        have ne : k ≠ j := by rintro rfl; simp [hj] at hk
        exact ⟨k,(Function.update_of_ne ne _ _).trans hk,wk⟩

theorem checks_assigned {T : ℕ} {H : Row T → Words} {allowed : Finset (Row T)}
    (sep : NoOverlap H allowed) (p xs : List Rate) (limit : p.length+xs.length ≤ T)
    (within : ∀ j ∈ prefixRows T p xs, j ∈ allowed) (m : Monitor (Row T) Words) (a : Assigned H allowed m) :
    ∃ m', checks T H p xs (some m) = some m' ∧ Assigned H allowed m' := by
  induction xs generalizing p m with
  | nil => exact ⟨m,rfl,a⟩
  | cons b xs ih =>
    simp only [List.length_cons] at limit
    have len : (p++[b]).length ≤ T := by simp; omega
    obtain ⟨n,changed,valid⟩ := step_assigned sep a _ _ _ (within _ (List.mem_cons_self ..)) (snoc_demand T H p b len)
    obtain ⟨o,tail,good⟩ := ih (p++[b]) (by simp; omega) (fun j h => within j (List.mem_cons_of_mem _ h)) n valid
    exact ⟨o,by simpa only [checks,Option.bind_some,changed] using tail,good⟩

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.step_assigned
#print axioms Reduction.ShakePermutation.Classic.checks_assigned

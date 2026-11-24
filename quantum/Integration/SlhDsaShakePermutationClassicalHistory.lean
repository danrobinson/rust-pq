import Integration.SlhDsaShakePermutationClassicalDriver

namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp PermutationConditioning Classical
noncomputable section

theorem rowId_inj {T : ℕ} {p q : List Rate} (hp : p.length ≤ T) (hq : q.length ≤ T)
    (eq : rowId T p = rowId T q) : p = q := by
  simp only [rowId,dite_eq_left hp,dite_eq_left hq,Sum.inl.injEq] at eq
  exact (BList.ofFn_ofList p hp).symm.trans ((congrArg (fun a : Fix.Domain T => List.ofFn a.2) eq).trans (BList.ofFn_ofList q hq))

theorem snoc_inj {A : Type} {p q : List A} {x y : A} (h : p++[x] = q++[y]) : p = q ∧ x = y := by
  have e := congrArg List.reverse h
  simp only [List.reverse_append,List.reverse_singleton,List.cons_append,List.nil_append,List.cons.injEq] at e
  exact ⟨List.reverse_inj.mp e.2,e.1⟩

theorem Trail.lastEdge {t : EdgeTrace Words} {p : List Rate} {r : Rate} {s : Words}
    (h : Trail t (p++[r]) s) : ∃ z a, Trail t p z ∧ (a,s) ∈ t ∧ capOf z = capOf a ∧ r = nextBlock z a := by
  generalize eq : p++[r] = u at h
  cases h with
  | root => simp at eq
  | @step q z a b parent mem same =>
    obtain ⟨rfl,rfl⟩ := snoc_inj eq
    exact ⟨z,a,parent,mem,same,rfl⟩

def TrailBound (t : EdgeTrace Words) := ∀ ⦃p s⦄, Trail t p s → p.length ≤ t.length

def Seen (T : ℕ) (t : EdgeTrace Words) : Row T → Prop
  | .inl a => ∃ p s, Trail t p s ∧ rowId T p = .inl a
  | .inr (d,x) => old t d x

structure History (T : ℕ) (t : EdgeTrace Words) (seen : Finset (Row T)) : Prop where
  compatible : Nonempty (Extensions t)
  unique : UniquePaths t
  short : TrailBound t
  used : ∀ j ∈ seen, Seen T t j

theorem emptyHistory (T : ℕ) : History T [] ∅ where
  compatible := ⟨⟨Equiv.refl _,by simp⟩⟩
  unique := unique_empty
  short := by intro p s h; cases h with
              | root => rfl
              | step _ e _ => simp at e
  used := by simp

theorem publicRow_new {T : ℕ} {t : EdgeTrace Words} {seen : Finset (Row T)}
    (h : History T t seen) (short : t.length < T) (d : Bool) (x : Words) (hx : ¬old t d x) :
    publicRow T t d x ∉ seen := by
  intro mem
  have was := h.used _ mem
  cases d with
  | true => exact hx was
  | false =>
    unfold publicRow at was
    simp only [Bool.false_eq_true,ite_false] at was
    split at was
    · rename_i reached
      obtain ⟨p,s,trail,eq⟩ : ∃ p s, Trail t p s ∧ rowId T p = _ := was
      let q := reached.choose
      let z := reached.choose_spec.choose
      have ht : Trail t q z := reached.choose_spec.choose_spec.1
      have target : capOf z = capOf x := reached.choose_spec.choose_spec.2
      have l : (q ++ [nextBlock z x]).length ≤ T := by have := h.short ht; simp; omega
      have pe := rowId_inj ((h.short trail).trans (Nat.le_of_lt short)) l eq
      rw [pe] at trail
      obtain ⟨z',a,other,edge',cap,block⟩ := trail.lastEdge
      obtain ⟨π⟩ := h.compatible
      have good (a b : Words) (hab : (a,b) ∈ t) : π.val a = b := π.property _ hab
      have same := (ht.eval π.val good).symm.trans (other.eval π.val good)
      subst z'
      have rates : rateOf x = rateOf a := by
        simpa only [nextBlock,rateXor_cancel] using congrArg (fun r => rateXor r (rateOf z)) block
      have xx : x = a := by rw [← join_split x,← join_split a,rates,target.symm.trans cap]
      exact hx ⟨s,xx ▸ edge'⟩
    · exact hx was

theorem iso_unused {t : EdgeTrace Words} {x y : Words} (iso : isolated t x y) (d : Bool) :
    ∀ a ∈ orient d t, y ≠ a.2 := by
  rintro ⟨a,b⟩ mem rfl
  cases d with
  | false => exact ((isolate_parts iso).2.2 _ _ mem).2 rfl
  | true =>
    obtain ⟨⟨c,e⟩,he,eq⟩ := List.mem_map.mp mem
    exact ((isolate_parts iso).2.2 _ _ he).1 (congrArg capOf (Prod.mk.inj eq).2.symm)

theorem old_weaken {A : Type} {t u : EdgeTrace A} (sub : ∀ a ∈ t, a ∈ u) (d : Bool) (x : A) :
    old t d x → old u d x := by
  rintro ⟨y,hy⟩
  refine ⟨y,?_⟩
  cases d with
  | false => exact sub _ hy
  | true => obtain ⟨a,ha,e⟩ := List.mem_map.mp hy; exact List.mem_map.mpr ⟨a,sub _ ha,e⟩

theorem history_step {T : ℕ} {t : EdgeTrace Words} {seen : Finset (Row T)}
    (h : History T t seen) (d : Bool) (x y : Words) (hx : ¬old t d x) (iso : isolated t x y) :
    History T (edge d x y :: t) (insert (publicRow T t d x) seen) := by
  have sub (a) (ha : a ∈ t) : a ∈ edge d x y :: t := List.mem_cons_of_mem _ ha
  let i : UnusedInputs (orient d t) := ⟨x,by rintro ⟨a,b⟩ he rfl; exact hx ⟨b,he⟩⟩
  let v : UnusedOutputs (orient d t) := ⟨y,iso_unused iso d⟩
  constructor
  · cases d with
    | false => exact extensions_cons_nonempty t i v h.compatible
    | true =>
      have ext := extensions_cons_nonempty (t.map Prod.swap) i v (h.compatible.map (inverseExtensionsEquiv t))
      refine ext.map (fun π => ⟨π.val.symm,?_⟩)
      intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact π.val.symm_apply_eq.mpr (π.property _ (List.mem_cons_self ..)).symm
      · exact π.val.symm_apply_eq.mpr (π.property _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,ha,rfl⟩))).symm
  · cases d
    · exact unique_forward h.unique iso
    · exact unique_inverse h.unique iso
  · intro p s hp
    cases d with
    | false =>
      rcases forward_paths iso hp with old|⟨_,p',z,prev,_,rfl⟩
      · exact (h.short old).trans (Nat.le_succ _)
      · simpa only [List.length_append,List.length_cons,List.length_nil,zero_add] using Nat.succ_le_succ (h.short prev)
    | true => exact (h.short (inverse_paths iso hp)).trans (Nat.le_succ _)
  · intro j mem
    rcases Finset.mem_insert.mp mem with rfl|prev
    · cases d with
      | true => exact ⟨y,List.mem_map.mpr ⟨(y,x),List.mem_cons_self ..,rfl⟩⟩
      | false =>
        unfold publicRow
        simp only [Bool.false_eq_true,ite_false]
        split
        · rename_i reached
          exact ⟨_,y,Trail.step (reached.choose_spec.choose_spec.1.weaken sub) (List.mem_cons_self ..)
            reached.choose_spec.choose_spec.2,rfl⟩
        · exact ⟨y,List.mem_cons_self ..⟩
    · cases j with
      | inl j => obtain ⟨p,s,ht,e⟩ := h.used _ prev; exact ⟨p,s,ht.weaken sub,e⟩
      | inr j => exact old_weaken sub _ _ (h.used _ prev)

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.publicRow_new
#print axioms Reduction.ShakePermutation.Classic.history_step

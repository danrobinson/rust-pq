import Integration.SlhDsaShakePermutationLongSelectAbsorb

/-! The native target/collection freshness rules retain a recorded path for each accepted target. -/
namespace Reduction.ShakePermutation.Long.SelectTrace
open Classical Classic SparsePort Phase OracleSpec OracleComp MLink SLHDSA TweakableHash
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
variable (S : Sha2Set) (pk : S.Node) (ar : ℕ)

structure Ledger (h : Select.History S ar) (t : Trace) (L : Log S) : Prop where
  paths : UniquePaths t
  cover : covered S pk t L
  target : ∀ tm ∈ h.1, ∃ w, Trail t (blocks S pk tm.1 tm.2.val) w
  messages : ∀ tm ∈ h.1, ∀ xs, (tm.1,xs) ∈ L → xs = tm.2.val
  logged : ∀ tm ∈ h.1, (tm.1,tm.2.val) ∈ L
  source : ∀ (entry : Bytes 32 × List S.Node), entry ∈ L → TweakReserved Prod.fst h.1 entry.1 ∨ entry.1 ∈ h.2

private theorem target_step {l c t L} (j : Arity.Row S ar) (fresh : TweakFresh Prod.fst l c j.1)
    (old : Ledger S pk ar (l,c) t L) (w : Words) (u : Trace) (trace : Trail u (blocks S pk j.1 j.2.val) w)
    (uq : UniquePaths u) (cov : covered S pk u ((j.1,j.2.val)::L)) (sub : ∀ e ∈ t, e ∈ u) :
    Ledger S pk ar (l++[j],c) u ((j.1,j.2.val)::L) := by
  refine ⟨uq,cov,?_,?_,?_,?_⟩
  · intro tm member
    rcases List.mem_append.mp member with prev|last
    · obtain ⟨v,hv⟩ := old.target _ prev; exact ⟨v,hv.weaken sub⟩
    · obtain rfl := List.mem_singleton.mp last; exact ⟨w,trace⟩
  · intro tm member xs logged
    rcases List.mem_append.mp member with prev|last
    · rcases List.mem_cons.mp logged with now|before
      · exact (fresh.1 ⟨tm,prev,Prod.mk.inj now |>.1⟩).elim
      · exact old.messages tm prev xs before
    · obtain rfl := List.mem_singleton.mp last
      rcases List.mem_cons.mp logged with now|before
      · exact (Prod.mk.inj now).2
      · rcases old.source (tm.1,xs) before with prior|prior
        · exact (fresh.1 prior).elim
        · exact (fresh.2 prior).elim
  · intro tm h
    rcases List.mem_append.mp h with prev|last
    · exact List.mem_cons_of_mem _ (old.logged tm prev)
    · obtain rfl := List.mem_singleton.mp last; exact List.mem_cons_self ..
  · intro entry h
    rcases List.mem_cons.mp h with rfl|prev
    · exact Or.inl ⟨j,List.mem_append_right _ (List.mem_singleton_self _),rfl⟩
    · rcases old.source entry prev with ⟨dm,mem,eq⟩|known
      · exact Or.inl ⟨dm,List.mem_append_left _ mem,eq⟩
      · exact Or.inr known

private theorem collection_step {l c t L} (d : Bytes 32) (xs : List S.Node) (fresh : ¬TweakReserved Prod.fst l d)
    (old : Ledger S pk ar (l,c) t L) (u : Trace) (uq : UniquePaths u) (cov : covered S pk u ((d,xs)::L))
    (sub : ∀ e ∈ t, e ∈ u) : Ledger S pk ar (l,c++[d]) u ((d,xs)::L) := by
  refine ⟨uq,cov,?_,?_,?_,?_⟩
  · intro tm mem; obtain ⟨v,hv⟩ := old.target _ mem; exact ⟨v,hv.weaken sub⟩
  · intro tm mem ys logged
    rcases List.mem_cons.mp logged with now|prev
    · exact (fresh ⟨tm,mem,Prod.mk.inj now |>.1⟩).elim
    · exact old.messages tm mem ys prev
  · exact fun tm mem => List.mem_cons_of_mem _ (old.logged tm mem)
  · intro e he
    rcases List.mem_cons.mp he with rfl|prev
    · exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))
    · rcases old.source e prev with prior|prior
      · exact Or.inl prior
      · exact Or.inr (List.mem_append_left _ prior)

theorem selection_all {D : Type} (p : OracleComp (Select.Spec S ar) D) (h : Select.History S ar) (t : Trace) (L : Log S)
    (ready : Ledger S pk ar h t L) : all (Select.prog S ar pk p h) t (fun r u => ∃ L', Ledger S pk ar r.2 u L') := by
  induction p using OracleComp.inductionOn generalizing h t L with
  | pure v => exact ⟨L,ready⟩
  | query_bind i k ih =>
    simp only [Select.prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    apply bind _ _ t _ (fun z u => ∃ L', Ledger S pk ar z.2 u L') _ (fun ⟨r,h'⟩ u ⟨L',ok⟩ => ih r h' u L' ok)
    obtain ⟨l,c⟩ := h
    rcases i with n|j|v
    · exact fun _ => ⟨L,ready⟩
    · change all (if _ then _ else _) t _
      split
      · exact ⟨L,ready⟩
      next good =>
        apply bind _ (fun y => pure (some y,(l++[j],c))) t (fun z u => ∃ L', Ledger S pk ar z.2 u L') (fun _ u => ∃ L', Ledger S pk ar (l++[j],c) u L') _ (fun _ _ h => h)
        apply hash_all S pk j.1 j.2.val L t ready.paths ready.cover
        intro w u trail uq cov sub
        exact ⟨_,target_step S pk ar j (not_not.mp (fun h => good (Or.inr h))) ready w u trail uq cov sub⟩
    · change all (if _ then _ else _) t _
      split
      · exact ⟨L,ready⟩
      next good =>
        apply bind _ (fun y => pure (some y,(l,c++[v.2.1]))) t (fun z u => ∃ L', Ledger S pk ar z.2 u L') (fun _ u => ∃ L', Ledger S pk ar (l,c++[v.2.1]) u L') _ (fun _ _ h => h)
        apply hash_all S pk v.2.1 v.2.2 L t ready.paths ready.cover
        intro w u _ uq cov sub
        exact ⟨_,collection_step S pk ar _ _ good ready u uq cov sub⟩

theorem ledger_empty : Ledger S pk ar ([],[]) [] [] := by
  refine ⟨unique_empty,?_,by simp,by simp,by simp,by simp⟩
  intro p w h; cases h with
  | root => exact Or.inl rfl
  | step _ mem _ => simp at mem
end
end Reduction.ShakePermutation.Long.SelectTrace
#print axioms Reduction.ShakePermutation.Long.SelectTrace.selection_all

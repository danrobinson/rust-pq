import Integration.SlhDsaShakePermutationLongBankHash

/-! The native target/collection freshness rules retain a recorded path for each accepted target. -/
namespace Reduction.ShakePermutation.Long.BankRun
open Classical Classic SparsePort Phase OracleSpec OracleComp MLink SLHDSA TweakableHash ItsrLabel
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
variable (S : Sha2Set) (pk : S.Node) (ar : ℕ) (π : Permutation) (H : Table)

structure Recorded (h : Select.History S ar) (t : Bank) (L : SelectTrace.Log S) : Prop where
  pins : Pins t H
  cover : Cover S pk π H t L
  target : ∀ tm ∈ h.1, Known π H t (blocks S pk tm.1 tm.2.val)
  messages : ∀ tm ∈ h.1, ∀ xs, (tm.1,xs) ∈ L → xs = tm.2.val
  logged : ∀ tm ∈ h.1, (tm.1,tm.2.val) ∈ L
  source : ∀ (entry : Bytes 32 × List S.Node), entry ∈ L → TweakReserved Prod.fst h.1 entry.1 ∨ entry.1 ∈ h.2

private theorem target_step {l c t L} (j : Arity.Row S ar) (fresh : TweakFresh Prod.fst l c j.1)
    (old : Recorded S pk ar π H (l,c) t L) (u : Bank) (trace : Known π H u (blocks S pk j.1 j.2.val))
    (pin : Pins u H) (cov : Cover S pk π H u ((j.1,j.2.val)::L)) (sub : Ext t u) :
    Recorded S pk ar π H (l++[j],c) u ((j.1,j.2.val)::L) := by
  refine ⟨pin,cov,?_,?_,?_,?_⟩
  · intro tm member
    rcases List.mem_append.mp member with prev|last
    · exact known_ext π H sub (old.target _ prev)
    · obtain rfl := List.mem_singleton.mp last; exact trace
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
    (old : Recorded S pk ar π H (l,c) t L) (u : Bank) (pin : Pins u H) (cov : Cover S pk π H u ((d,xs)::L))
    (sub : Ext t u) : Recorded S pk ar π H (l,c++[d]) u ((d,xs)::L) := by
  refine ⟨pin,cov,?_,?_,?_,?_⟩
  · intro tm mem; exact known_ext π H sub (old.target _ mem)
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

theorem fixed_selection {A : Type} (p : OracleComp (Select.Spec S ar) A) (h : Select.History S ar) (D : Bank) (L : SelectTrace.Log S)
    (ready : Recorded S pk ar π H h D L) : fixedAll H (simulateQ (impl π) (Select.prog S ar pk p h)) D
      (fun r u => ∃ L', Recorded S pk ar π H r.2 u L') := by
  induction p using OracleComp.inductionOn generalizing h D L with
  | pure v => exact ⟨L,ready⟩
  | query_bind i k ih =>
    simp only [Select.prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    apply fixed_bind H _ _ D (fun z u => ∃ L', Recorded S pk ar π H z.2 u L') _ _ (fun ⟨r,h'⟩ u ⟨L',ok⟩ => ih r h' u L' ok)
    obtain ⟨l,c⟩ := h
    rcases i with n|j|v
    · exact fun _ => ⟨L,ready⟩
    · change fixedAll H (simulateQ (impl π) (if _ then _ else _)) D _
      split
      · exact ⟨L,ready⟩
      next good =>
        simp only [simulateQ_bind,simulateQ_pure]
        apply fixed_bind H _ (fun y => pure (some y,(l++[j],c))) D (fun _ u => ∃ L', Recorded S pk ar π H (l++[j],c) u L')
          (fun z u => ∃ L', Recorded S pk ar π H z.2 u L') _ (fun _ _ h => h)
        apply hash_all S pk π H j.1 j.2.val L D ready.pins ready.cover
        intro u pin sub cov trail
        exact ⟨_,target_step S pk ar π H j (not_not.mp (fun h => good (Or.inr h))) ready u trail pin cov sub⟩
    · change fixedAll H (simulateQ (impl π) (if _ then _ else _)) D _
      split
      · exact ⟨L,ready⟩
      next good =>
        simp only [simulateQ_bind,simulateQ_pure]
        apply fixed_bind H _ (fun y => pure (some y,(l,c++[v.2.1]))) D (fun _ u => ∃ L', Recorded S pk ar π H (l,c++[v.2.1]) u L')
          (fun z u => ∃ L', Recorded S pk ar π H z.2 u L') _ (fun _ _ h => h)
        apply hash_all S pk π H v.2.1 v.2.2 L D ready.pins ready.cover
        intro u pin sub cov _
        exact ⟨_,collection_step S pk ar π H _ _ good ready u pin cov sub⟩

theorem recorded_empty : Recorded S pk ar π H ([],[]) (fun _ => none) [] :=
  ⟨fun _ _ e => by contradiction,fun _ _ e => by contradiction,by simp,by simp,by simp,by simp⟩

theorem selection_all {A : Type} (p : OracleComp (Select.Spec S ar) A) :
    all (simulateQ (impl π) (Select.prog S ar pk p ([],[]))) (fun _ => none)
      (fun r D => ∀ H, Pins D H → ∃ L, Recorded S pk ar π H r.2 D L) :=
  deferred _ _ _ (fun H _ => fixed_selection S pk ar π H p _ _ [] (recorded_empty _ _ _ _ _))
end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.selection_all

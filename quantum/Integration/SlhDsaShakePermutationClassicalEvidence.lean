import Integration.SlhDsaShakePermutationClassicalWires

namespace Reduction.ShakePermutation.Classic
open Classical OracleComp OracleSpec MLink PQ.Interactive
noncomputable section

/-- Every newly recorded private prefix includes its immediate parent,
unless that parent is the initial sponge state. -/
theorem prefix_origin (T : ℕ) (q xs : List Rate) (limit : q.length+xs.length ≤ T) (j : Row T)
    (mem : j ∈ prefixRows T q xs) :
    ∃ p b, (p++[b]).length ≤ T ∧ rowId T (p++[b]) = j ∧
      (p = q ∨ rowId T p ∈ prefixRows T q xs) := by
  induction xs generalizing q with
  | nil => simp [prefixRows] at mem
  | cons a xs ih =>
    simp only [prefixRows,List.mem_cons] at mem ⊢
    have h := limit
    simp only [List.length_cons] at h
    rcases mem with rfl|tail
    · exact ⟨q,a,by simp; omega,rfl,Or.inl rfl⟩
    · obtain ⟨p,b,size,eq,rest⟩ := ih (q++[a]) (by simp; omega) tail
      rcases rest with rfl|rest
      · exact ⟨_,_,size,eq,Or.inr (Or.inl rfl)⟩
      · exact ⟨_,_,size,eq,Or.inr (Or.inr rest)⟩

structure Evidence (T : ℕ) (H : Row T → Words) (r : Report T) : Prop where
  wires : Wires T H r.edges r.seen
  nonempty : ∀ a : Fix.Domain T, Sum.inl a ∈ r.seen → 0 < a.1.val
  parents : ∀ j ∈ r.privateRows, ∃ p b, (p++[b]).length ≤ T ∧ rowId T (p++[b]) = j ∧
    (p=[] ∨ rowId T p ∈ r.privateRows)

theorem emptyEvidence (T : ℕ) (H : Row T → Words) : Evidence T H (emptyReport T) :=
  ⟨emptyWires _ _,by simp [emptyReport],by simp [emptyReport]⟩

theorem fresh_pos {T : ℕ} {H : Row T → Words} {r : Report T} (ev : Evidence T H r)
    (short : r.edges.length < T) (d : Bool) (x : Words) (a : Fix.Domain T)
    (eq : Sum.inl a = publicRow T r.edges d x) : 0 < a.1.val := by
  cases d with
  | true => contradiction
  | false =>
    simp only [publicRow,Bool.false_eq_true,ite_false] at eq
    split at eq
    · rename_i hit
      have len : (hit.choose ++ [nextBlock hit.choose_spec.choose x]).length ≤ T := by
        have := ev.wires.short hit.choose_spec.choose_spec.1
        simp; omega
      simp only [rowId,dite_eq_left len,Sum.inl.injEq] at eq
      subst a
      change 0 < (_++[_]).length
      simp
    · contradiction

theorem report_dirty (S : Sha2Set) (N T : ℕ) {Z : Type} (H : Row T → Words) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (Native S N) Z) (r : Report T) (bad : r.clean = false) :
    (report S N T H raw P r).2.clean = false := by
  induction P using OracleComp.inductionOn generalizing r with
  | pure => exact bad
  | query_bind i k ih =>
    let z := reportStep S N T H raw i r
    apply ih z.1 z.2
    rcases i with ⟨d,x⟩|x
    · simp only [z,reportStep,recordPub]; split <;> simp [bad]
    · exact bad

theorem blocksOf_length (N T : ℕ) (h : Completion.blockCap N ≤ T) (x : ShakeApi.Input N) :
    (blocksOf x).length ≤ T := by
  apply le_trans _ h
  simp only [blocksOf,messageBlocks_length,sp,List.length_map,List.length_ofFn,Completion.blockCap]
  exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.le_of_lt_succ x.1.isLt)) _

theorem report_evidence (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T) {Z : Type}
    (H : Row T → Words) (raw : ShakeApi.RawTable S N) (P : OracleComp (Native S N) Z) (q : ℕ)
    (hq : WCount (cost (S := S) (N := N)) P q) (r : Report T) (ok : Evidence T H r)
    (room : r.edges.length + q ≤ T) (clean : (report S N T H raw P r).2.clean = true) :
    Evidence T H (report S N T H raw P r).2 := by
  induction P using OracleComp.inductionOn generalizing q r with
  | pure => exact ok
  | query_bind i k ih =>
    let z := reportStep S N T H raw i r
    have safe : z.2.clean = true := by
      by_contra bad
      have fail := report_dirty S N T H raw (k z.1) z.2 (Bool.eq_false_iff.mpr bad)
      exact Bool.noConfusion (clean.symm.trans fail)
    rcases i with ⟨d,x⟩|x
    · have enough : 1 ≤ q := hq.1
      have hr := hq.2 z.1
      have short : r.edges.length < T := by omega
      change r.edges.length+q ≤ T at room
      apply ih z.1 _ hr z.2 _ _ clean
      · change Evidence T H (recordPub T H r d x).2
        unfold recordPub
        split
        · exact ok
        · rename_i fresh
          have iso : isolated r.edges x (H (publicRow T r.edges d x)) := by
            have hs : r.clean = true ∧ isolated r.edges x (H (publicRow T r.edges d x)) := by
              simpa [z,reportStep,recordPub,fresh] using safe
            exact hs.2
          refine ⟨wire_step ok.wires short d x fresh iso,?_,ok.parents⟩
          intro a mem
          rcases Finset.mem_insert.mp mem with eq|prev
          · exact fresh_pos ok short d x a eq
          · exact ok.nonempty a prev
      · change (recordPub T H r d x).2.edges.length+(q-1) ≤ T
        simp only [recordPub]; split <;> simp <;> omega
    · apply ih z.1 _ (hq.2 z.1) z.2 _ (by change r.edges.length + (q-_) ≤ T; omega) clean
      refine ⟨ok.wires,ok.nonempty,?_⟩
      intro j hj
      rcases Finset.mem_union.mp hj with new|old
      · obtain ⟨p,b,len,eq,par⟩ := prefix_origin T [] (blocksOf x) (by simpa using blocksOf_length N T cap x) j (List.mem_toFinset.mp new)
        exact ⟨p,b,len,eq,par.imp_right (fun h => Finset.mem_union_left _ (List.mem_toFinset.mpr h))⟩
      · obtain ⟨p,b,len,eq,par⟩ := ok.parents _ old
        exact ⟨p,b,len,eq,par.imp_right (Finset.mem_union_right _)⟩
end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.report_evidence

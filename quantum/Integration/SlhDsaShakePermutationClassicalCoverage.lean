import Integration.SlhDsaShakePermutationClassicalMonitorSafe
import Integration.SlhDsaShakePermutationClassicalResolution

namespace Reduction.ShakePermutation.Classic
open Classical OracleSpec OracleComp PQ.Interactive MLink SLHDSA
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section

theorem private_mono (S : Sha2Set) (N T : ℕ) {Z : Type} (H : Row T → Words) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (Native S N) Z) (r : Report T) :
    r.privateRows ⊆ (report S N T H raw P r).2.privateRows := by
  induction P using OracleComp.inductionOn generalizing r with
  | pure => exact Finset.Subset.rfl
  | query_bind i k ih =>
    let z := reportStep S N T H raw i r
    apply Finset.Subset.trans _ (ih z.1 z.2)
    rcases i with ⟨d,x⟩|x
    · simp only [z,reportStep,recordPub]; split <;> simp
    · exact Finset.subset_union_right

theorem full_survives (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T) {Z : Type}
    (H : Row T → Words) (raw : ShakeApi.RawTable S N) (P : OracleComp (Native S N) Z) (q : ℕ)
    (hq : WCount (cost (S := S) (N := N)) P q) (r : Report T) (room : r.edges.length+q ≤ T)
    (known : Evidence T H r) (m : Monitor (Row T) Words)
    (clean : (report S N T H raw P r).2.clean = true)
    (sep : NoOverlap H (active (report S N T H raw P r).2))
    (backed : Assigned H (active (report S N T H raw P r).2) m) :
    detRun (fullStep S N T H raw) (fun _ s => hit s.2.isSome) P (r,some m) = 1 := by
  induction P using OracleComp.inductionOn generalizing q r m with
  | pure => rfl
  | query_bind i k ih =>
    let z := reportStep S N T H raw i r
    let fin := (report S N T H raw (k z.1) z.2).2
    let allowed := active fin
    have sc : z.2.clean = true := by
      by_contra bad
      exact Bool.noConfusion (clean.symm.trans (report_dirty S N T H raw (k z.1) z.2 (Bool.eq_false_iff.mpr bad)))
    have h1 : WCount (cost (S := S) (N := N)) (liftM ((Native S N).query i)) q :=
      wCount_liftM_query _ _ hq.1
    have next := report_evidence S N T cap H raw (liftM ((Native S N).query i)) q h1 r known room sc
    have nextRoom : z.2.edges.length + (q-cost (S := S) i) ≤ T := by
      have price := hq.1
      rcases i with ⟨d,x⟩|x
      · change (recordPub T H r d x).2.edges.length+(q-1) ≤ T
        change 1 ≤ q at price
        simp only [recordPub]; split <;> simp <;> omega
      · change r.edges.length+(q-_) ≤ T; omega
    have cont (m') (hnext : (fullStep S N T H raw i (r,some m)).2 = (z.2,some m')) (hv : Assigned H allowed m') :
        detRun (fullStep S N T H raw) (fun _ s => hit s.2.isSome)
          ((Native S N).query i >>= k) (r,some m) = 1 := by
      have c : (fullStep S N T H raw i (r,some m)).1 = z.1 := by rcases i with ⟨d,x⟩|x <;> rfl
      change detRun _ _ (k (fullStep S N T H raw i (r,some m)).1) (fullStep S N T H raw i (r,some m)).2 = _
      rw [c,hnext]
      exact ih _ _ (hq.2 _) z.2 nextRoom next m' clean sep hv
    rcases i with ⟨d,x⟩|x
    · by_cases oldx : old r.edges d x
      · exact cont m (by simp [fullStep,recordPub,z,reportStep,oldx]) backed
      · let j := publicRow T r.edges d x
        have hj : j ∈ z.2.seen := by simp [j,z,reportStep,recordPub,oldx]
        have ha : j ∈ allowed := Finset.mem_union_right _ (seen_mono S N T H raw (k z.1) z.2 hj)
        have one : 1 ≤ q := hq.1
        have aligned := row_demand known.wires (by omega) d x
        obtain ⟨m',changed,valid⟩ := step_assigned sep backed j d x ha aligned
        exact cont m' (by simp only [fullStep,z,reportStep,oldx,ite_false,Option.bind_some]; rw [changed]) valid
    · have within (j : Row T) (hj : j ∈ prefixRows T [] (blocksOf x)) : j ∈ allowed :=
        Finset.mem_union_left _ (private_mono S N T H raw (k z.1) z.2
          (Finset.mem_union_left _ (List.mem_toFinset.mpr hj)))
      obtain ⟨m',changed,valid⟩ := checks_assigned sep [] _ (by simpa using blocksOf_length N T cap x) within m backed
      exact cont m' (by simpa only [fullStep,z,reportStep,changed]) valid

theorem det_covered (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T) {Z : Type} (H : Row T → Words)
    (raw : ShakeApi.RawTable S N) (P : OracleComp (Native S N) Z) (q : ℕ) (hq : WCount (cost (S := S)) P q)
    (limit : q ≤ T) : let final := (report S N T H raw P (emptyReport T)).2
    1 ≤ detRun (fullStep S N T H raw) (fun _ s => hit s.2.isSome) P (emptyReport T,some (start _ _)) +
      hit (final.clean=false) + hit (leaked (hidden final) (denied final) (fun i => capOf (H i))) := by
  let final := (report S N T H raw P (emptyReport T)).2
  by_cases h : final.clean=true
  · by_cases separated : Separated H final
    · have clean := report_evidence S N T cap H raw P q hq (emptyReport T) (emptyEvidence _ _) (by simpa [emptyReport]) h
      have size : final.edges.length ≤ T := by
        have b := report_mass S N T H raw P q hq (emptyReport T)
        change final.edges.length + final.privateRows.card ≤ mass (emptyReport T) + q at b
        simp only [mass,emptyReport,List.length_nil,Finset.card_empty,zero_add] at b
        omega
      have sep : NoOverlap H (active final) := by
        intro j k hj hk eq; rcases eq with eq|eq
        · exact overlay_sources clean size separated hj hk eq
        · exact overlay_targets clean size separated hj hk eq
      have keep := full_survives S N T cap H raw P q hq (emptyReport T) (by simpa [emptyReport]) (emptyEvidence _ _)
        (start _ _) h sep (start_assigned ..)
      simp only [keep]; exact le_add_right (le_add_right le_rfl)
    · have bad := Classical.byContradiction separated
      change 1 ≤ _ + _ + hit (leaked (hidden final) (denied final) _)
      have e : hit (leaked (hidden final) (denied final) (fun i => capOf (H i))) = 1 := by simp [hit,bad]
      rw [e]; exact le_add_left le_rfl
  · have bad := Bool.eq_false_iff.mpr h
    change 1 ≤ _ + hit (final.clean=false) + _
    have e : hit (final.clean=false) = 1 := by simp [hit,bad]
    rw [e]; exact le_add_right (le_add_left le_rfl)

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.det_covered

import Integration.SlhDsaCompressionSingleTarget
import Mathlib.Combinatorics.Pigeonhole

namespace Reduction.Compression.MessageHash
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA SLHDSA.Security SLHDSA.DigestTransport OracleComp OracleSpec
open PQ.Interactive PQ.QROM Quantum ENNReal KeyedHash KeyedHash.Covering QItsr Classical

variable (S : Sha2Set)
abbrev Mask (d : ℕ) := { m : Finset (Fin S.vp.params.k) // m.card = d }
abbrev Masked (m : Finset (Fin S.vp.params.k)) :=
  Fin (2^S.vp.params.h) × (m → Fin (2^S.vp.params.a))
def masked (m : Finset (Fin S.vp.params.k)) (u : Chain512) : Masked S m :=
  let z := whole S u
  (z.1,fun i => z.2 i)

/-- Assign each covered coordinate to a matching target. A single distinct target
must match the candidate on a subset of at least `d+1` coordinates. -/
private theorem common_mask (g : CompressionTables) (xs : List Cell) (nd : xs.Nodup)
    (qs d : ℕ) (len : xs.length ≤ qs+1) (many : qs*d < S.vp.params.k)
    (cov : CovP (idxOf S.vp) (xs.map fun u => digest S (g.2 u))) :
    ∃ (m : Mask S (d+1)), ∃ u ∈ xs, ∃ v ∈ xs, u ≠ v ∧ masked S m.1 (g.2 u) = masked S m.1 (g.2 v) := by
  classical
  obtain ⟨u,hu,c⟩ := cover_cells S g xs nd cov
  choose f hmem hne heq using c
  let t := xs.toFinset.erase u
  have mapped : ∀ i ∈ Finset.univ, f i ∈ t := fun i _ =>
    Finset.mem_erase.mpr ⟨(hne i).symm,List.mem_toFinset.mpr (hmem i)⟩
  have cnt : t.card ≤ qs := by
    have e := Finset.card_erase_add_one (List.mem_toFinset.mpr hu)
    have small := List.toFinset_card_le xs
    dsimp [t]
    omega
  obtain ⟨v,hv,large⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to mapped
    (n := d) (by simpa using (Nat.mul_le_mul_right d cnt).trans_lt many)
  obtain ⟨m,sub,size⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt large)
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (size ▸ Nat.succ_pos d)
  have eq (i : Fin S.vp.params.k) (hi : i ∈ m) : coordinate S i (g.2 u) = coordinate S i (g.2 v) := by
    simpa only [(Finset.mem_filter.mp (sub hi)).2] using heq i
  exact ⟨⟨m,size⟩,u,hu,v,List.mem_toFinset.mp (Finset.mem_erase.mp hv).2,
    (Finset.mem_erase.mp hv).1.symm,Prod.ext (congrArg (Prod.fst (β := Fin (2^S.vp.params.a))) (eq j hj))
    (funext fun i => congrArg Prod.snd (eq i i.2))⟩

theorem masked_fraction (m : Finset (Fin S.vp.params.k)) (B : Finset (Masked S m)) :
    ((Finset.univ.filter fun y => masked S m y ∈ B).card : ℝ) / Fintype.card Chain512 =
      (B.card:ℝ)/2^(S.vp.params.h + S.vp.params.a*m.card) := by
  classical
  let leaf := Fin (2^S.vp.params.h)
  let digit := Fin (2^S.vp.params.a)
  let rest := {i : Fin S.vp.params.k // i ∉ m} → digit
  let e : Decoded S ≃ Masked S m × rest := (Equiv.prodCongr (Equiv.refl leaf)
    (Equiv.piEquivPiSubtypeProd (fun i => i ∈ m) (fun _ => digit))).trans (Equiv.prodAssoc ..).symm
  have hc := covering_uniform S (fun z => (z.1,fun i : m => z.2 i) ∈ B)
  have h := hc.trans ((SampleableType.prEvent_uniformSample_comp_of_bijective e.bijective
    (fun z => z.1 ∈ B)).trans (SampleableType.prEvent_uniformSample_fst _))
  simp only [SampleableType.prEvent_uniformSample] at h
  have card : Fintype.card (Masked S m) = 2^(S.vp.params.h + S.vp.params.a*m.card) := by
    rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,Fintype.card_coe,← pow_mul,← pow_add]
  have eq := congrArg ENNReal.toReal h
  simp only [masked,whole, ENNReal.toReal_div,ENNReal.toReal_natCast,Finset.filter_mem_eq_inter,Finset.univ_inter,card,
    Nat.cast_pow,Nat.cast_ofNat,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at eq ⊢
  convert eq using 2
  congr 1

noncomputable local instance (g : CompressionTables) : SampleableType (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (SampleableType S.Node)

theorem mask_hit (hw : S.vp.params.n ≠ 16) (g : CompressionTables) (cand : Query S) (ts : List (Query S))
    (qs d : ℕ) (len : ts.length ≤ qs) (dk : d < S.vp.params.k) (many : qs*d < S.vp.params.k)
    (win : (itsrProblem S.vp (tablePrimitives g S.vp.params)).Wins ts cand) :
    ∃ m : Mask S (d+1), acceptsBy (masked S m.1) g (selectBy (masked S m.1) (trace S g cand ts)) := by
  classical
  have k := Finset.exists_subset_card_eq (s := Finset.univ (α := Fin S.vp.params.k)) (n := d+1)
    (by simpa using dk)
  obtain ⟨m,_,size⟩ := k
  let defmask : Mask S (d+1) := ⟨m,size⟩
  rcases win_witness S hw g cand ts win with cov | iv | ⟨u,mu,v,mv,ne,eq⟩
  · have length : (finalCells S g cand ts).length ≤ qs+1 := by
      apply (List.dedup_sublist _).length_le.trans
      simpa only [List.length_map,List.length_cons] using Nat.succ_le_succ len
    obtain ⟨z,u,mu,v,mv,ne,eq⟩ := common_mask S g _ (List.nodup_dedup _) qs d length many cov
    exact ⟨z,selects_witness S _ g cand ts (Or.inl ⟨u,final_subset S hw g cand ts _ mu,
      v,final_subset S hw g cand ts _ mv,ne,eq⟩)⟩
  · exact ⟨defmask,selects_witness S _ g cand ts (Or.inr iv)⟩
  · exact ⟨defmask,selects_witness S _ g cand ts (Or.inl ⟨u,mu,v,mv,ne,congrArg _ eq⟩)⟩

theorem union_weight {W A I : Type} [Fintype W] [DecidableEq W] [DecidableEq I]
    (X : Closed W A) (ρ : Matrix W W ℂ) (t : Finset I) (P : I → A → Prop) :
    qWeight (fun z => ∃ i ∈ t, P i z) X ρ ≤ ∑ i ∈ t, qWeight (P i) X ρ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [qWeight_false_fors]
  | @insert i t hi ih =>
    let B := fun z => ∃ j ∈ t, P j z
    have eq := qWeight_congr_ev (p := fun z => ∃ j ∈ insert i t, P j z)
      (p' := fun z => P i z ∨ (B z ∧ ¬P i z)) (by intro z; simp only [Finset.mem_insert,exists_eq_or_imp,B]; tauto) X ρ
    rw [eq,qWeight_or (fun _ h k => k.2 h),Finset.sum_insert hi]
    exact add_le_add le_rfl ((qWeight_mono (fun _ h => h.1) X ρ).trans ih)

variable (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
variable (F : PortForger Input Output E)

theorem mask_success (hw : S.vp.params.n ≠ 16) (c : Caps) (qs d : ℕ) (dk : d < S.vp.params.k)
    (many : qs*d < S.vp.params.k) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (g : CompressionTables) :
    qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S r seeds F g)) F.ρ₀ ≤
      ∑ m : Mask S (d+1), qWeight (acceptsBy (masked S m.1) g)
        (projectedMachine S r seeds F (masked S m.1) c.ml qs (oracle g)) F.ρ₀ := by
  classical
  let X := close (ITSROracles (itsrProblem S.vp (randPrims (functions S g)))) (qbItsrL (reduced S r seeds F g)) []
  let P := fun (m : Mask S (d+1)) (z : Query S × List (Query S)) =>
    acceptsBy (masked S m.1) g (selectBy (masked S m.1) (trace S g z.1 z.2))
  apply le_trans _ ((union_weight X F.ρ₀ Finset.univ P).trans _)
  · apply qWeight_mono_allQ (transcript_support S r seeds F c qs hs hc g)
    intro z cap win
    obtain ⟨m,h⟩ := mask_hit S hw g z.1 z.2 qs d cap.2.1 dk many
      (by constructor; exact win.1; kexact win.2)
    exact ⟨m,Finset.mem_univ _,h⟩
  · exact Finset.sum_le_sum fun m _ => projected_event S r seeds F (masked S m.1) c qs hs hc g (P m)
      (fun _ _ _ h => h)

/-- Union over the subsets of FORS coordinates where one target can witness the cover. -/
noncomputable def maskLoss (d q : ℕ) : ℝ≥0∞ :=
  (S.vp.params.k.choose (d+1) : ℝ≥0∞) *
    ((2*(q:ℝ≥0∞)+1)^2/2^512 + ENNReal.ofReal (16*((q:ℝ)+1)^3/2^(S.vp.params.h+S.vp.params.a*(d+1))))

theorem mask_itsr (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs d : ℕ) (dk : d < S.vp.params.k)
    (many : qs*d < S.vp.params.k) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g)))
      (qbItsrL (reduced S r seeds F g)) F.ρ₀) ≤ maskLoss S d (queries S c.ml q qs) := by
  classical
  let A := fun (m : Mask S (d+1)) => projectedMachine S r seeds F (masked S m.1) c.ml qs
  let p := fun (m : Mask S (d+1)) (g : CompressionTables) =>
    qWeight (acceptsBy (masked S m.1) g) (A m (oracle g)) F.ρ₀
  have one (m : Mask S (d+1)) := projected_search (masked S m.1) _
    (fun B => (masked_fraction S m.1 B).le) (A m) _
    (projected_cost S r seeds F hw (masked S m.1) c q qs hq hs hc) F.ρ₀ F.posSemidef F.trace_eq_one
  apply le_trans (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (mask_success S r seeds F hw c qs d dk many hs hc g))
  change (∑ g, unifW _ g * ∑ m, p m g) ≤ _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold maskLoss
  have card : Fintype.card (Mask S (d+1)) = S.vp.params.k.choose (d+1) := by simp [Mask]
  rw [← card,← nsmul_eq_mul,← Finset.card_univ,← Finset.sum_const]
  apply Finset.sum_le_sum
  intro m _
  simpa only [p,SetOracle.uniformMean,queries,m.2] using one m

end Reduction.Compression.MessageHash

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
variable (S : Sha2Set) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

noncomputable def wideMaskBound (L q qs d : ℕ) :=
  wideLossWithClasses S L q qs (fun ar => ClassCollision.twoPhaseLoss S ar L q qs) +
    MessageHash.maskLoss S d (MessageHash.queries S L q qs)

/-- A shared-compression signature bound using simultaneous FORS-coordinate matches
at a common address. The caller may use any number of coordinates satisfying the
pigeonhole inequality for its signing-query budget. -/
theorem wide_suf_mask (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs d : ℕ) (dk : d < S.vp.params.k)
    (many : qs*d < S.vp.params.k) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S r seeds F g)) ≤ wideMaskBound S c.ml q qs d :=
  (wide_suf_with_classes S r seeds F hw c q qs hq hs hc _ (fun ar ha =>
    ClassCollision.two_phase_class_tcr S r seeds F ar hw ha c q qs hq hs hc)).trans
    (add_le_add le_rfl (MessageHash.mask_itsr S r seeds F hw c q qs d dk many hq hs hc))

theorem wide_euf_mask (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs d : ℕ) (dk : d < S.vp.params.k)
    (many : qs*d < S.vp.params.k) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qUnforgeableAdvantage (experimentForger S r seeds F g)) ≤ wideMaskBound S c.ml q qs d :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S r seeds F g))).trans
    (wide_suf_mask S r seeds F hw c q qs d dk many hq hs hc)
end Reduction.Compression

#print axioms Reduction.Compression.MessageHash.mask_itsr
#print axioms Reduction.Compression.wide_suf_mask
#print axioms Reduction.Compression.wide_euf_mask

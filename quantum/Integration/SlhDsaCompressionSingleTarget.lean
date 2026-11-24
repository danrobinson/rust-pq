import Integration.SlhDsaCompressionWideMixed

namespace Reduction.Compression.MessageHash
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA SLHDSA.Security SLHDSA.DigestTransport OracleComp OracleSpec
open PQ.Interactive PQ.QROM Quantum ENNReal KeyedHash KeyedHash.Covering QItsr Classical

private theorem other_unique {A : Type} (xs : List A) (n : xs.length ≤ 2) (u v w : A)
    (hu : u ∈ xs) (hv : v ∈ xs) (hw : w ∈ xs) (ne : u ≠ v) (nd : u ≠ w) : v = w := by
  rcases xs with _ | ⟨a,bs⟩
  · simp at hu
  rcases bs with _ | ⟨b,cs⟩
  · simp_all
  rcases cs with _ | ⟨c,ds⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hu hv hw
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> simp_all
  · simp at n

variable (S : Sha2Set)
abbrev Decoded := Digest S.vp.params.h S.vp.params.a S.vp.params.k
def whole (u : Chain512) : Decoded S := coveringDigest S.vp (digest S u)

private theorem whole_collision (g : CompressionTables) (xs : List Cell) (nd : xs.Nodup) (len : xs.length ≤ 2)
    (cov : CovP (idxOf S.vp) (xs.map fun u => digest S (g.2 u))) :
    ∃ u ∈ xs, ∃ v ∈ xs, u ≠ v ∧ whole S (g.2 u) = whole S (g.2 v) := by
  obtain ⟨u,hu,c⟩ := cover_cells S g xs nd cov
  let j : Fin S.vp.params.k := ⟨0,by cases S <;> decide⟩
  obtain ⟨v,hv,hd,e⟩ := c j
  refine ⟨u,hu,v,hv,hd,Prod.ext (congrArg (Prod.fst (β := Fin (2^S.vp.params.a))) e) ?_⟩
  funext i
  obtain ⟨w,hw,ne,ew⟩ := c i
  have ev := other_unique xs len u v w hu hv hw hd ne
  subst w
  exact congrArg Prod.snd ew

noncomputable local instance (g : CompressionTables) : SampleableType (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (SampleableType S.Node)

theorem single_hit (hw : S.vp.params.n ≠ 16) (g : CompressionTables) (cand : Query S) (ts : List (Query S))
    (len : ts.length ≤ 1) (win : (itsrProblem S.vp (tablePrimitives g S.vp.params)).Wins ts cand) :
    acceptsBy (whole S) g (selectBy (whole S) (trace S g cand ts)) := by
  apply selects_witness
  rcases win_witness S hw g cand ts win with cov | iv | ⟨u,mu,v,mv,ne,eq⟩
  · have length : (finalCells S g cand ts).length ≤ 2 := by
      apply (List.dedup_sublist _).length_le.trans
      simp only [List.length_map,List.length_cons]
      omega
    obtain ⟨u,mu,v,mv,ne,eq⟩ := whole_collision S g _ (List.nodup_dedup _) length cov
    exact Or.inl ⟨u,final_subset S hw g cand ts _ mu,v,final_subset S hw g cand ts _ mv,ne,eq⟩
  · exact Or.inr iv
  · exact Or.inl ⟨u,mu,v,mv,ne,congrArg (whole S) eq⟩

theorem whole_fraction (B : Finset (Decoded S)) :
    ((Finset.univ.filter fun y => whole S y ∈ B).card : ℝ)/Fintype.card Chain512 =
      (B.card:ℝ)/2^(S.vp.params.h + S.vp.params.a*S.vp.params.k) := by
  have h := covering_uniform S (fun z => z ∈ B)
  simp only [SampleableType.prEvent_uniformSample] at h
  have card : Fintype.card (Decoded S) = 2^(S.vp.params.h + S.vp.params.a*S.vp.params.k) := by
    change Fintype.card (Fin (2^S.vp.params.h) × (Fin S.vp.params.k → Fin (2^S.vp.params.a))) = _
    rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,Fintype.card_fin,← pow_mul,← pow_add]
  have e := congrArg ENNReal.toReal h
  simp only [whole, ENNReal.toReal_div,ENNReal.toReal_natCast,Finset.filter_mem_eq_inter,Finset.univ_inter,card,
    Nat.cast_pow,Nat.cast_ofNat,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at e ⊢
  convert e using 2
  congr 1

noncomputable def singleLoss (q : ℕ) : ℝ≥0∞ :=
  (2*(q:ℝ≥0∞)+1)^2/2^512 + ENNReal.ofReal (16*((q:ℝ)+1)^3/2^(S.vp.params.h + S.vp.params.a*S.vp.params.k))

variable (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
variable (F : PortForger Input Output E)
theorem single_itsr (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ) (single : qs ≤ 1)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g)))
      (qbItsrL (reduced S r seeds F g)) F.ρ₀) ≤ singleLoss S (queries S c.ml q qs) := by
  let M := projectedMachine S r seeds F (whole S) c.ml qs
  have h := projected_search (whole S) _ (fun B => (whole_fraction S B).le) M _
    (projected_cost S r seeds F hw (whole S) c q qs hq hs hc) F.ρ₀ F.posSemidef F.trace_eq_one
  apply le_trans _ h
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul' le_rfl
  apply projected_success S r seeds F (whole S) c qs hs hc g
  intro cand ts len win
  exact single_hit S hw g cand ts (len.trans single) (by constructor; exact win.1; kexact win.2)

/-- With no signed target there is no covering index, even for a fixed table. -/
theorem zero_itsr (c : Caps) (hs : ∀ pk, CountBound isSign (F.main pk) 0)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (g : CompressionTables) :
    qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g))) (qbItsrL (reduced S r seeds F g)) F.ρ₀ = 0 := by
  classical
  apply le_antisymm _ bot_le
  unfold qItsrAdvantage
  apply le_trans _ (qWeight_false_fors (close (ITSROracles (itsrProblem S.vp (randPrims (functions S g))))
    (qbItsrL (reduced S r seeds F g)) []) F.ρ₀).le
  apply qWeight_mono_allQ (transcript_support S r seeds F c 0 hs hc g)
  intro z cap win
  have ht : z.2 = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp cap.2.1)
  let d := (tablePrimitives g S.vp.params).Hmsg z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2
  let index := ((splitDigest S.vp.params d).forsAdrs,0 * 2^S.vp.params.a +
    forsIdx S.vp.params (splitDigest S.vp.params d).md.toList 0)
  have hit : index ∈ idxOf S.vp d := by
    simp only [Ideal.idxOf,Reduction.forsIndices,List.mem_map,List.mem_range]
    exact ⟨0,by cases S <;> decide,rfl⟩
  have bad := win.2 index hit
  simp only [KeyedHash.ITSRProblem.targetIndexSet,ht,List.flatMap_nil,List.not_mem_nil] at bad

end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.single_itsr

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
variable (S : Sha2Set) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)
noncomputable def wideSingleBound (L q qs : ℕ) :=
  wideLossWithClasses S L q qs (fun ar => ClassCollision.twoPhaseLoss S ar L q qs) +
    MessageHash.singleLoss S (MessageHash.queries S L q qs)

theorem wide_suf_single (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ) (single : qs ≤ 1)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S r seeds F g)) ≤ wideSingleBound S c.ml q qs :=
  (wide_suf_with_classes S r seeds F hw c q qs hq hs hc _ (fun ar ha =>
    ClassCollision.two_phase_class_tcr S r seeds F ar hw ha c q qs hq hs hc)).trans
    (add_le_add le_rfl (MessageHash.single_itsr S r seeds F hw c q qs single hq hs hc))

theorem wide_euf_single (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ) (single : qs ≤ 1)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qUnforgeableAdvantage (experimentForger S r seeds F g)) ≤ wideSingleBound S c.ml q qs :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S r seeds F g))).trans
    (wide_suf_single S r seeds F hw c q qs single hq hs hc)
end Reduction.Compression
#print axioms Reduction.Compression.wide_suf_single
#print axioms Reduction.Compression.wide_euf_single

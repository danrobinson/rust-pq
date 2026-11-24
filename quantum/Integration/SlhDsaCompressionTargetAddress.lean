import Integration.SlhDsaCompressionSingleTarget
namespace Reduction.Compression.MessageHash
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA SLHDSA.Security SLHDSA.DigestTransport OracleComp OracleSpec
open PQ.Interactive PQ.QROM Quantum ENNReal KeyedHash KeyedHash.Covering QItsr Classical
variable (S : Sha2Set)

/-- Two physically distinct final compression cells of signing targets decode to
the same hypertree address. The candidate is excluded from this event. -/
def targetAddressCollision (g : CompressionTables) (ts : List (Query S)) : Prop :=
  ∃ u ∈ ts.map (lastCell S g), ∃ v ∈ ts.map (lastCell S g),
    u ≠ v ∧ (whole S (g.2 u)).1 = (whole S (g.2 v)).1

private theorem covered_without_address_collision (hw : S.vp.params.n ≠ 16) (g : CompressionTables) (cand : Query S) (ts : List (Query S))
    (good : ¬targetAddressCollision S g ts)
    (cover : CovP (idxOf S.vp) ((finalCells S g cand ts).map fun u => digest S (g.2 u))) :
    ∃ u ∈ cells S g cand ts, ∃ v ∈ cells S g cand ts, u ≠ v ∧ whole S (g.2 u) = whole S (g.2 v) := by
  classical
  obtain ⟨u,hu,c⟩ := cover_cells S g _ (List.nodup_dedup _) cover
  let targets := ts.map (lastCell S g)
  have split (z) (hz : z ∈ finalCells S g cand ts) : z = lastCell S g cand ∨ z ∈ targets :=
    List.mem_cons.mp (List.mem_dedup.mp hz)
  have uniq (x y) (hx : x ∈ targets) (hy : y ∈ targets)
      (eq : (whole S (g.2 x)).1 = (whole S (g.2 y)).1) : x = y :=
    by by_contra ne; exact good ⟨x,hx,y,hy,ne,eq⟩
  let j : Fin S.vp.params.k := ⟨0,by cases S <;> decide⟩
  obtain ⟨v,hv,uv,eq⟩ := c j
  have addr : (whole S (g.2 u)).1 = (whole S (g.2 v)).1 :=
    congrArg (Prod.fst (β := Fin (2^S.vp.params.a))) eq
  refine ⟨u,final_subset S (by assumption) g cand ts u hu,v,?_,uv,Prod.ext addr ?_⟩
  · exact final_subset S (by assumption) g cand ts v hv
  funext i
  obtain ⟨w,hw,uw,ew⟩ := c i
  have aw : (whole S (g.2 u)).1 = (whole S (g.2 w)).1 :=
    congrArg (Prod.fst (β := Fin (2^S.vp.params.a))) ew
  have same : v = w := by
    rcases split u hu with uc | ut
    · exact uniq _ _ ((split v hv).resolve_left (fun h => uv (uc.trans h.symm)))
        ((split w hw).resolve_left (fun h => uw (uc.trans h.symm))) (addr.symm.trans aw)
    · exact ((split v hv).resolve_right (fun vt => uv (uniq _ _ ut vt addr))).trans
        ((split w hw).resolve_right (fun wt => uw (uniq _ _ ut wt aw))).symm
  subst w
  exact congrArg Prod.snd ew

noncomputable local instance (g : CompressionTables) : SampleableType (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (SampleableType S.Node)

theorem target_hit (hw : S.vp.params.n ≠ 16) (g : CompressionTables) (cand : Query S) (ts : List (Query S))
    (good : ¬targetAddressCollision S g ts) (win : (itsrProblem S.vp (tablePrimitives g S.vp.params)).Wins ts cand) :
    acceptsBy (whole S) g (selectBy (whole S) (trace S g cand ts)) := by
  apply selects_witness
  rcases win_witness S hw g cand ts win with cov | iv | ⟨u,mu,v,mv,ne,eq⟩
  · exact Or.inl (covered_without_address_collision S hw g cand ts good cov)
  · exact Or.inr iv
  · exact Or.inl ⟨u,mu,v,mv,ne,congrArg _ eq⟩

variable (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
variable (F : PortForger Input Output E)

/-- Probability of an address collision among the actual random-salt signing
targets, averaged over the same two public compression tables as the forger. -/
noncomputable def targetAddressLoss :=
  SetOracle.uniformMean fun g =>
    qWeight (fun z => targetAddressCollision S g z.2)
      (close (ITSROracles (itsrProblem S.vp (randPrims (functions S g)))) (qbItsrL (reduced S r seeds F g)) []) F.ρ₀

theorem fresh_target_itsr (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g)))
      (qbItsrL (reduced S r seeds F g)) F.ρ₀) ≤ targetAddressLoss S r seeds F + singleLoss S (queries S c.ml q qs) := by
  classical
  let M := projectedMachine S r seeds F (whole S) c.ml qs
  have h := projected_search (whole S) _ (fun B => (whole_fraction S B).le) M _
    (projected_cost S r seeds F hw (whole S) c q qs hq hs hc) F.ρ₀ F.posSemidef F.trace_eq_one
  apply le_trans _ (add_le_add le_rfl h)
  unfold targetAddressLoss SetOracle.uniformMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  rw [← mul_add]
  let prob := itsrProblem S.vp (randPrims (functions S g))
  let X := close (ITSROracles prob) (qbItsrL (reduced S r seeds F g)) []
  let B := fun z : Query S × List (Query S) => targetAddressCollision S g z.2
  let G := fun z : Query S × List (Query S) => ¬B z ∧ prob.Wins z.2 z.1
  have incl : qWeight (fun z => prob.Wins z.2 z.1) X F.ρ₀ ≤ qWeight (fun z => B z ∨ G z) X F.ρ₀ :=
    qWeight_mono (fun z win => by by_cases b : B z; exact Or.inl b; exact Or.inr ⟨b,win⟩) X F.ρ₀
  apply mul_le_mul' le_rfl
  apply incl.trans
  rw [qWeight_or (fun _ b g => g.1 b)]
  apply add_le_add le_rfl
  apply projected_event S r seeds F (whole S) c qs hs hc g G
  intro cand ts _ h
  exact target_hit S hw g cand ts h.1 (by constructor; exact h.2.1; kexact h.2.2)

end Reduction.Compression.MessageHash
#print axioms Reduction.Compression.MessageHash.fresh_target_itsr

import Integration.SlhDsaCompressionClassCollision
import Integration.SlhDsaCompressionClassReduction

namespace Reduction.Compression.ClassCollision
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal TweakableHash Resources2
attribute [local irreducible] arityTargets tcrTargets
variable (S : Sha2Set)
local notation "P₀" => randPrims (carrier S)
abbrev CallLog := List (Bytes 22 × List S.Node)
def walkMax := max (keygenMax S) (thashCalls S S.vp.params.k)

def record (pk : S.Node) (H : Input → Output) :
    QueryImpl (thSpec P₀) (StateM (CallLog S)) := fun t log =>
  ((tablePrimitives (tablesOf H) S.vp.params).Thash pk t.1 t.2, log ++ [t])

private theorem record_cost {α : Type} (pk : S.Node) (P : OracleComp (thSpec P₀) α)
    (q : ℕ) (hq : WCount (fun t => thashCalls S t.2.length) P q) (log : CallLog S) :
    EvalCost (fun H => (pure (((simulateQ (record S pk H) P).run log).2) : ProbComp (CallLog S))) q := by
  induction P using OracleComp.inductionOn generalizing q log with
  | pure a => exact (EvalCost.const (pure log)).mono (Nat.zero_le _)
  | query_bind t k ih =>
    rw [wCount_query_bind] at hq
    have h := EvalCost.bind (thash_cost S pk t.1 t.2) (fun r => ih r _ (hq.2 r) (log ++ [t]))
    have he (H : Input → Output) :
        ((simulateQ (record S pk H) (liftM ((thSpec P₀).query t) >>= k)).run log).2 =
          ((simulateQ (record S pk H) (k ((tablePrimitives (tablesOf H) S.vp.params).Thash pk t.1 t.2))).run (log ++ [t])).2 := by
      rw [simulateQ_bind, simulateQ_spec_query]
      rfl
    simp only [he]
    exact h.mono (by have := hq.1; omega)

noncomputable def walk (tbl : SecretTable S.vp P₀) (pk : S.Node) (H : Input → Output) :=
  ((simulateQ (record S pk H) (structureFree tbl)).run []).2

theorem walk_cost (tbl : SecretTable S.vp P₀) (pk : S.Node) :
    EvalCost (fun H => (pure (walk S tbl pk H) : ProbComp (CallLog S))) (tcrTargets S.vp * walkMax S) := by
  apply record_cost
  apply cappedCount (fun t : (thSpec P₀).Domain => thashCalls S t.2.length) (fun _ => True)
    (walkMax S) (fun _ h => (h trivial).elim) _ _ (tcr_structureFree_bound tbl)
  unfold structureFree
  refine Realize.np_structureVia _ (fun key xs hx => ?_) (fun a => isQueryBoundP_pure _ _ _)
  apply (isQueryBoundP_query_iff _ _ _).2
  intro h
  change walkMax S < thashCalls S xs.length at h
  rcases hx with h'|h'|h'|h' <;> rw [h'] at h <;> unfold walkMax keygenMax at h <;> omega

set_option maxHeartbeats 1500000 in
theorem walk_oracle (g : CompressionTables) (tbl : SecretTable S.vp P₀) (pk : S.Node) :
    walk S tbl pk (oracle g) = honestCalls (vp := S.vp) (prims := randPrims (functions S g)) tbl pk := by
  rw [honestCalls_eq_free]
  unfold walk
  have h : record S pk (oracle g) = logImpl (vp := S.vp) (prims := randPrims (functions S g)) pk := by
    funext t s
    change ((tablePrimitives (tablesOf (oracle g)) S.vp.params).Thash pk t.1 t.2, s ++ [t]) = _
    rw [tablesOf_oracle]
    qm_kernel_rfl
  have hf : structureFree (vp := S.vp) (prims := P₀) tbl = structureFree (vp := S.vp) (prims := randPrims (functions S g)) tbl := by qm_kernel_rfl
  rw [hf,h]


variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E) (arity : ℕ)

def attemptAt (pk : S.Node) (log : CallLog S) (jm : ℕ × {xs : List S.Node // xs.length = arity}) :
    Attempt S arity :=
  match (TcrSplit.gState (fun xs : List S.Node => xs.length = arity) log).1[jm.1]? with
  | none => ⟨pk,default,jm.2,jm.2⟩
  | some tm => ⟨pk,tm.1,jm.2,tm.2⟩

noncomputable def signatureCandidates (H : Input → Output) : Closed (WS Input Output E) (Attempt S arity) := do
  let pk ← liftU seeds
  let tbl ← liftU (Lazy.sparseTable S.vp P₀)
  let log ← liftU (pure (walk S tbl pk H) : ProbComp (CallLog S))
  let jm ← ClassOne.machine S (carrier S) rand F arity (tbl,Realize.clampL S.vp.params.len log) pk H
  pure (attemptAt S arity pk log jm)

theorem signatureCandidates_cost (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (spec := unifSpec) cnt0 (signatureCandidates S rand seeds F arity)
      (ClassOne.budget S c.ml q qs + tcrTargets S.vp * walkMax S) := by
  unfold signatureCandidates
  apply PUE.liftU_bind (EvalCost.const seeds) (q := ClassOne.budget S c.ml q qs + tcrTargets S.vp * walkMax S)
  intro pk
  apply PUE.liftU_bind (EvalCost.const (Lazy.sparseTable S.vp P₀))
    (q := ClassOne.budget S c.ml q qs + tcrTargets S.vp * walkMax S)
  intro tbl
  apply PUE.liftU_bind (walk_cost S tbl pk)
  intro log
  change PUE (spec := unifSpec) cnt0
    (fun H => ClassOne.machine S (carrier S) rand F arity (tbl,Realize.clampL S.vp.params.len log) pk H >>= fun jm =>
      pure (attemptAt S arity pk log jm)) _
  simp only [bind_pure_comp]
  exact PUE.map _ (ClassOne.machine_pue S (carrier S) rand F c arity _ pk q qs (Realize.clampL_mem _ _) hq hs hc)

private theorem honest_len (g : CompressionTables)
    (tbl : SecretTable S.vp P₀) (pk : S.Node) :
    ∀ t ∈ honestCalls (vp := S.vp) (prims := randPrims (functions S g)) tbl pk,
      t.2.length ≤ S.vp.params.len := by
  intro t ht
  obtain ⟨a,_,_,hlen⟩ := honestCalls_arity _ _ t ht
  rw [hlen]
  have h : 2 ≤ S.vp.params.len ∧ S.vp.params.k ≤ S.vp.params.len := by cases S <;> decide
  unfold arityOf
  split_ifs <;> omega

set_option maxHeartbeats 1000000 in
theorem signatureCandidates_oracle (g : CompressionTables) :
    signatureCandidates S rand seeds F arity (oracle g) =
      candidates (arity := arity) (E := E) S seeds g (qbTcrArM arity (reduced S rand seeds F g)) := by
  let Q := reduced S rand seeds F g
  unfold signatureCandidates candidates
  apply bind_congr
  intro pk
  have h := bTcrArM_choose_run (structural_randPrims S.vp (fipsApprovedAddressBounds S.fips) (functions S g))
    arity Q.toClassical pk
  simp only [qbTcrArM, qTcrOfClassical]
  dsimp only [Q] at h
  rw [h]
  let sparse := Lazy.sparseTable S.vp (randPrims (functions S g))
  let L := fun tbl => honestCalls (vp := S.vp) (prims := randPrims (functions S g)) tbl pk
  let pack := fun tbl : SecretTable S.vp P₀ => ((tbl,L tbl),TcrSplit.gState (fun xs : List S.Node => xs.length = arity) (L tbl))
  let out := fun (r : (SecretTable S.vp P₀ × CallLog S) × SM_DT_TCR_State (Bytes 22) {xs : List S.Node // xs.length = arity}) => do
    let jm ← qMemoForge arity Q r.1 pk
    match r.2.1[jm.1]? with
    | none => pure (⟨pk,default,jm.2,jm.2⟩ : Attempt S arity)
    | some tm => pure ⟨pk,tm.1,jm.2,tm.2⟩
  have hr : liftU (pack <$> sparse) >>= out = (liftU sparse >>= fun t => out (pack t)) := by
    rw [liftU_map,bind_map_left]
  trans (liftU sparse >>= fun t => out (pack t))
  swap
  · kexact hr.symm
  apply bind_congr
  intro tbl
  dsimp only [out,pack,L,Q]
  simp only [liftU_pure, pure_bind, walk_oracle, Realize.clampL_eq_self _ _ (honest_len S g tbl pk)]
  refine Ideal.Transport.bind_congr_k (ClassOne.atOracle S rand seeds F g arity (tbl,L tbl) pk) ?_
  intro jm
  unfold attemptAt
  split <;> rename_i he <;> rw [he]

/-- The actual byte-level signature reduction's nonsingleton class-TCR contribution
on each wide SHA-2 set reduces to quantum prefix collision finding. Both phases
and the final extraction are charged to the same public compression port. -/
theorem signature_class_collision (hw : S.vp.params.n ≠ 16) (hn : arity ≠ 1)
    (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    ∃ M : (Input → Output) → Closed (WS Input Output E) (Option (Cell × Cell)),
      PUE (X := Input) (Y := Output) (E := E) (spec := unifSpec) cnt0 M
        (ClassOne.budget S c.ml q qs + tcrTargets S.vp * walkMax S +
          (1 + 2 * ((38 + S.vp.params.n * arity) / 128 + 1))) ∧
      (∑ g : CompressionTables, unifW _ g * qSM_DT_TCR_Advantage (qbTcrArM arity (reduced S rand seeds F g))) ≤
        ∑ g : CompressionTables, unifW _ g *
          @qWeight _ _ _ (collision S g) (Classical.decPred _) (M (oracle g)) F.ρ₀ :=
  class_reduction (arity := arity) S (signatureCandidates S rand seeds F arity) seeds hw hn
    (fun g => qbTcrArM arity (reduced S rand seeds F g)) F.ρ₀ (fun _ => rfl) _
    (signatureCandidates_cost S rand seeds F arity c q qs hq hs hc)
    (signatureCandidates_oracle S rand seeds F arity)

end Reduction.Compression.ClassCollision
#print axioms Reduction.Compression.ClassCollision.walk_cost
#print axioms Reduction.Compression.ClassCollision.walk_oracle
#print axioms Reduction.Compression.ClassCollision.signatureCandidates_cost
#print axioms Reduction.Compression.ClassCollision.signatureCandidates_oracle
#print axioms Reduction.Compression.ClassCollision.signature_class_collision

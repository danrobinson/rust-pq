import PQ.QROM.FidelityPrf
import PQ.QROM.FidelityLazy
import PQ.QROM.ExactItsr
import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR

/-!
# Fidelity of the exact adaptive ITSR game to VCVio's `KeyedHash.ITSRAdvantage`

`itsrAdaptiveExp` (`PQ/QROM/ExactItsr.lean`), restricted to classical adversaries with one
uniform coin, classical queries to `H : K × Xm → D` and at most `s` target queries, is VCVio's
`ITSRAdvantage` for the keyed hash `hash k x = H (k, x)` with uniform keys, averaged over the
uniformly random `H`; the cover relation is VCVio's subset relation `fidItsrCov indices`
(every index of the candidate's digest is an index of a target's digest).

* `fidMapOut`: changing the final output of an interactive adversary (the exact ITSR game has
  output family `fun _ ↦ K × Xm`).
* `fid_itsr_exact`: the exact game on embedded adversaries: the average of the winning indicator
  of the classical run against `rndCh Rs`.
* `fid_itsr_capped`: with at most `s` target queries, VCVio's target oracle (a fresh key per
  query, no cap) is the oracle capped at `s` fresh keys.
* `fid_itsr_presample`: pre-sampling of the randomizers `Rs : Fin s → K` (`fidLazy_eq_eager`;
  the `i`-th key is read once, at the `i`-th target query).
* `fid_itsr_wins_iff`: VCVio's `Wins` on the transcript is `itsrAWin (fidItsrCov indices)`.
* `fid_itsr_eq`: `itsrAdaptiveExp (embedding) = avg_H ITSRAdvantage (honest H)`.
* `fid_itsr_classical_le`: `itsr_adaptive_le` as a bound on VCVio's advantage.

* `fidItsrCov_fors_iff`, `fid_itsr_fors_classical_le`: the FORS relation `forsCov` is the
  instance `indices = fidForsIndices`; the bound with the closed form of the covering
  probability.

Deviation that remains: the cap `s` on target queries is a hypothesis on the adversary here
(VCVio's game has none).
-/

open OracleComp OracleSpec ENNReal Quantum Matrix KeyedHash
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

universe u v u₁ v₁ w

namespace PQ.QROM

/-! ## Changing the output of an interactive adversary -/

section MapOut

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {Req Resp St : Type}
  {Out Out' : QReg → Type w} {W₂ : QReg → Type w}

/-- Apply `f` to the final output of an interactive adversary. -/
def fidMapOut (f : ∀ u, Out u → Out' u) :
    (n : ℕ) → {A : QReg} → IAdv L spec Req Resp Out n A → IAdv L spec Req Resp Out' n A
  | 0, _, x => QuantumComp.bind (X := Out) x fun u o ↦ QuantumComp.pure (f u o)
  | n + 1, _, x =>
    QuantumComp.bind (X := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) x
      fun u r ↦ QuantumComp.pure (X := fun u ↦ Out' u ⊕
          (Req × (Resp → IAdv L spec Req Resp Out' n u))) (match r with
        | .inl o => .inl (f u o)
        | .inr rc => .inr (rc.1, fun resp ↦ fidMapOut f n (rc.2 resp)))

theorem fidMapOut_flat (f : ∀ u, Out u → Out' u) (ch : Req → St → Resp × St)
    (K : ∀ u, Out' u → St → QuantumComp L spec W₂ u) (n : ℕ) {A : QReg} (s : St)
    (x : IAdv L spec Req Resp Out n A) :
    IAdv.flat ch K n s (fidMapOut f n x) = IAdv.flat ch (fun u o s ↦ K u (f u o) s) n s x := by
  induction n generalizing A s with
  | zero =>
    have key : ∀ x : QuantumComp L spec Out A,
        QuantumComp.bind (QuantumComp.bind x fun u o ↦ QuantumComp.pure (X := Out') (f u o))
          (fun u o ↦ K u o s) = QuantumComp.bind x fun u o ↦ K u (f u o) s := fun x ↦ by
      rw [QuantumComp.bind_assoc]
      rfl
    exact key x
  | succ n ih =>
    have key : ∀ x : QuantumComp L spec
        (fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) A,
        QuantumComp.bind (QuantumComp.bind x fun u r ↦ QuantumComp.pure (X := fun u ↦ Out' u ⊕
          (Req × (Resp → IAdv L spec Req Resp Out' n u))) (match r with
            | .inl o => .inl (f u o)
            | .inr rc => .inr (rc.1, fun resp ↦ fidMapOut f n (rc.2 resp))))
          (fun u r ↦ match r with
            | .inl o => K u o s
            | .inr rc => IAdv.flat ch K n (ch rc.1 s).2 (rc.2 (ch rc.1 s).1)) =
        QuantumComp.bind x fun u r ↦ match r with
          | .inl o => K u (f u o) s
          | .inr rc => IAdv.flat ch (fun u o s ↦ K u (f u o) s) n (ch rc.1 s).2
              (rc.2 (ch rc.1 s).1) := fun x ↦ by
      rw [QuantumComp.bind_assoc]
      congr 1
      funext u r
      cases r with
      | inl o => rfl
      | inr rc => exact ih _ _
    exact key x

theorem fidMapOut_isQueryBound (f : ∀ u, Out u → Out' u) (n : ℕ) {A : QReg}
    (x : IAdv L spec Req Resp Out n A) {b : spec.Port → ℕ} (hx : IAdv.IsQueryBound n x b) :
    IAdv.IsQueryBound n (fidMapOut f n x) b := by
  intro St ch s
  rw [fidMapOut_flat, IAdv.flat_eq_bind]
  exact ((hx St ch s).bind (b₂ := 0) fun u os ↦
    QuantumComp.isQueryBound_pure _ _).mono (add_zero b).le

end MapOut

/-! ## One-port games with an arbitrary continuation -/

section Leaf

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {ρ : Type} {rspec : OracleSpec.{0, 0} ρ} {Req Resp St State Ω : Type} [Fintype Ω] [Nonempty Ω]

/-- The embedded algorithm with a uniform coin, followed by any continuation: the average over
the coin of the continuation at the classical run. -/
theorem fidS_leafProb_coin (cd : FidCodec rspec Req Resp) (H : X → Y) (ch : Req → St → Resp × St)
    (n : ℕ) (choose : Ω → OracleComp ((X →ₒ Y) + rspec) State) (s : St)
    (hb : ∀ ω, IsQueryBoundP (choose ω) fidIsReq n) {W₂ : QReg → Type}
    (K : ∀ u, FidOut State u → St → QuantumComp LocalSig.instruments.{0} (qromSpec X Y) W₂ u)
    (E : (Σ u, W₂ u) → Prop) :
    leafProb (additiveOracleRuntime H) .instruments
        (IAdv.flat ch K n s (fidSCoinEmb cd choose n)) fidσ E =
      avg fun ω ↦ leafProb (additiveOracleRuntime H) .instruments
        (K (QReg.of Unit) ⟨rfl, (fidGRun cd H ch (choose ω) s).1⟩
          (fidGRun cd H ch (choose ω) s).2) fidσ E := by
  rw [fidSCoin_flat]
  refine (fidGCoin_leafProb (additiveOracleRuntime H) _ fidσ_posSemidef _).trans ?_
  refine avg_congr fun ω ↦ ?_
  unfold leafProb
  simp only [fidS_sim cd H ch n (choose ω) s (hb ω)]

end Leaf

/-! ## ITSR -/

section Itsr

variable {K Xm D Index Ω : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm]
  [DecidableEq Xm] [Fintype D] [DecidableEq D] [AddCommGroup D] [DecidableEq Index]
  [SampleableType K] [Fintype Ω] [Nonempty Ω] [SampleableType Ω] {s : ℕ}

/-- VCVio's subset relation as a cover relation: every index of `u` is an index of a digest
in `S`. -/
def fidItsrCov (indices : D → List Index) (S : Finset D) (u : D) : Prop :=
  ∀ i ∈ indices u, ∃ d ∈ S, i ∈ indices d

instance (indices : D → List Index) (S : Finset D) : DecidablePred (fidItsrCov indices S) :=
  fun u ↦ by unfold fidItsrCov; infer_instance

theorem fidItsrCov_mono (indices : D → List Index) (S S' : Finset D) (u : D) (h : S ⊆ S')
    (hc : fidItsrCov indices S u) : fidItsrCov indices S' u :=
  fun i hi ↦ let ⟨d, hd, hid⟩ := hc i hi; ⟨d, h hd, hid⟩

/-- VCVio's ITSR problem for the function `H`: uniform keys, `hash k x = H (k, x)`. -/
noncomputable def fidItsrProblem (indices : D → List Index) (H : K × Xm → D) :
    ITSRProblem K Xm D Index :=
  ⟨⟨$ᵗ K, fun k x ↦ H (k, x)⟩, indices⟩

/-- Requests of the exact game for the queries of the target oracle. -/
noncomputable def fidItsrCodec (K Xm : Type) [Nonempty K] : FidCodec (Xm →ₒ K) Xm K where
  enc x := x
  dec _ k := k
  dflt _ := Classical.arbitrary K

/-- A classical ITSR adversary with a uniform coin and classical queries to `H`. -/
abbrev FidItsrAdv (Ω K Xm D : Type) := Ω → OracleComp ((K × Xm →ₒ D) + (Xm →ₒ K)) (K × Xm)

/-- Answer the queries to `H`; pass the target queries on. -/
def fidItsrInst (H : K × Xm → D) :
    QueryImpl ((K × Xm →ₒ D) + (Xm →ₒ K)) (OracleComp (unifSpec + ITSRTargetSpec Xm K)) :=
  fun t ↦ match t with
    | .inl q => pure (H q)
    | .inr x => liftM (OracleSpec.query (spec := unifSpec + ITSRTargetSpec Xm K) (.inr x))

/-- VCVio's adversary at the function `H`. -/
noncomputable def fidItsrHonest (indices : D → List Index) (A : FidItsrAdv Ω K Xm D)
    (H : K × Xm → D) : ITSRAdversary (fidItsrProblem indices H) where
  main := (liftM ($ᵗ Ω : ProbComp Ω) : OracleComp (unifSpec + ITSRTargetSpec Xm K) Ω) >>=
    fun ω ↦ simulateQ (fidItsrInst H) (A ω)

/-- The embedding into the exact adaptive ITSR game. -/
noncomputable def fidItsrEmb (A : FidItsrAdv Ω K Xm D) (s : ℕ) :
    IAdv LocalSig.instruments.{0} (qromSpec (K × Xm) D) Xm K (fun _ ↦ K × Xm) s (QReg.of Unit) :=
  fidMapOut (fun _ p ↦ p.2) s (fidSCoinEmb (fidItsrCodec K Xm) A s)

/-- **The exact adaptive ITSR game on embedded classical adversaries.** -/
theorem fid_itsr_exact (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]
    (A : FidItsrAdv Ω K Xm D) (hb : ∀ ω, IsQueryBoundP (A ω) fidIsReq s) :
    itsrAdaptiveExp .instruments (A := QReg.of Unit) (SubState.basis ()) s (fidItsrEmb A s) Cov =
      avg fun Rs : Fin s → K ↦ avg fun H : K × Xm → D ↦ avg fun ω : Ω ↦
        ind (itsrAWin Cov Rs H ⟨QReg.of Unit,
          fidGRun (fidItsrCodec K Xm) H (rndCh Rs) (A ω) []⟩) := by
  unfold itsrAdaptiveExp mpExp
  refine avg_congr fun Rs ↦ avg_congr fun H ↦ ?_
  unfold qprob fidItsrEmb
  rw [evalDistMap_eq_leafProb, fidMapOut_flat]
  have hσ : (SubState.basis (() : (QReg.of Unit))).matrix ⊗ₖ
      (additiveOracleRuntime H).init.matrix = fidσ := fid_joint_basis
  rw [hσ, fidS_leafProb_coin _ _ _ _ _ _ hb]
  refine avg_congr fun ω ↦ ?_
  have hp := leafProb_pure (R := additiveOracleRuntime H) (I := LocalSig.Interp.instruments.{0})
    (W := fun _ ↦ (K × Xm) × List Xm) (A := QReg.of Unit)
    (fidGRun (fidItsrCodec K Xm) H (rndCh Rs) (A ω) []) fidσ (itsrAWin Cov Rs H)
  exact hp.trans ((congrArg (· * _) fidσ_trace).trans (one_mul _))

/-! ### VCVio's side: the target oracle, capped and pre-sampled -/

/-- VCVio's target oracle with queries to `H` answered, as one implementation. -/
noncomputable def fidItsrImpl (indices : D → List Index) (H : K × Xm → D) :
    QueryImpl ((K × Xm →ₒ D) + (Xm →ₒ K)) (StateT (ITSRTranscript K Xm) ProbComp) :=
  fun t ↦ match t with
    | .inl q => pure (H q)
    | .inr x => ITSRTargetOracle (fidItsrProblem indices H) x

theorem fid_itsr_compose (indices : D → List Index) (H : K × Xm → D) {α : Type}
    (oa : OracleComp ((K × Xm →ₒ D) + (Xm →ₒ K)) α) :
    simulateQ (ITSROracles (fidItsrProblem indices H)) (simulateQ (fidItsrInst H) oa) =
      simulateQ (fidItsrImpl indices H) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [simulateQ_bind (fidItsrInst H), simulateQ_spec_query,
      simulateQ_bind (fidItsrImpl indices H), simulateQ_spec_query, simulateQ_bind]
    rcases t with q | x
    · simp only [fidItsrInst, fidItsrImpl]
      rw [simulateQ_pure, pure_bind, pure_bind]
      exact ih (H q)
    · simp only [fidItsrInst, fidItsrImpl]
      refine Eq.trans (congrArg (· >>= _) (simulateQ_spec_query
        (ITSROracles (fidItsrProblem indices H)) (.inr x))) ?_
      exact bind_congr fun u ↦ ih u

/-- The target oracle capped at `s` draws: after `s` targets it answers a fixed key. -/
noncomputable def fidItsrCapped (s : ℕ) (H : K × Xm → D) :
    QueryImpl ((K × Xm →ₒ D) + (Xm →ₒ K)) (StateT (ITSRTranscript K Xm) ProbComp) :=
  fun t ↦ match t with
    | .inl q => pure (H q)
    | .inr x => StateT.mk fun targets ↦
        if targets.length < s then
          (($ᵗ K : ProbComp K) >>= fun k ↦ pure (k, targets ++ [(k, x)]))
        else pure (Classical.arbitrary K, targets ++ [(Classical.arbitrary K, x)])

/-- With at most `n` target queries and room for `n` more targets below the cap, VCVio's
target oracle is the capped one. -/
theorem fid_itsr_capped (indices : D → List Index) (H : K × Xm → D) {α : Type}
    (oa : OracleComp ((K × Xm →ₒ D) + (Xm →ₒ K)) α) (n : ℕ) (targets : ITSRTranscript K Xm)
    (hb : IsQueryBoundP oa fidIsReq n) (hn : targets.length + n ≤ s) :
    (simulateQ (fidItsrImpl indices H) oa).run targets =
      (simulateQ (fidItsrCapped s H) oa).run targets := by
  induction oa using OracleComp.inductionOn generalizing n targets with
  | pure a => rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, StateT.run_bind]
    rcases t with q | x
    · simp only [fidItsrImpl, fidItsrCapped]
      rw [StateT.run_pure, pure_bind, pure_bind]
      exact ih (H q) n targets (by simpa [fidIsReq] using hb.2 (H q)) hn
    · have hn0 : 0 < n := by simpa [fidIsReq] using hb.1
      have hlt : targets.length < s := by omega
      have e1 : (fidItsrImpl indices H (.inr x)).run targets =
          (($ᵗ K : ProbComp K) >>= fun k ↦ pure (k, targets ++ [(k, x)])) :=
        ITSRTargetOracle_run _ x targets
      have e2 : (fidItsrCapped s H (.inr x)).run targets =
          (($ᵗ K : ProbComp K) >>= fun k ↦ pure (k, targets ++ [(k, x)])) := by
        simp [fidItsrCapped, hlt]
      rw [e1, e2, bind_assoc, bind_assoc]
      simp only [pure_bind]
      refine bind_congr fun k' ↦ ?_
      exact ih k' (n - 1) (targets ++ [(k', x)]) (by simpa [fidIsReq] using hb.2 k')
        (by rw [List.length_append, List.length_singleton]; omega)

/-- VCVio's target oracle with the `i`-th key read from the table `Rs`, as deterministic steps
on VCVio's transcript. -/
noncomputable def fidItsrEag (H : K × Xm → D) (Rs : Fin s → K) :
    (t : ((K × Xm →ₒ D) + (Xm →ₒ K)).Domain) → ITSRTranscript K Xm →
      ((K × Xm →ₒ D) + (Xm →ₒ K)).Range t × ITSRTranscript K Xm
  | .inl q, targets => (H q, targets)
  | .inr x, targets =>
    ((rndAt Rs targets.length : K), targets ++ [((rndAt Rs targets.length : K), x)])

/-- **Pre-sampling of the randomizers** (for the capped oracle). -/
theorem fid_itsr_presample (H : K × Xm → D) {α : Type}
    (oa : OracleComp ((K × Xm →ₒ D) + (Xm →ₒ K)) α) (targets : ITSRTranscript K Xm)
    (cont : α × ITSRTranscript K Xm → ProbComp Bool) :
    fidPr ((simulateQ (fidItsrCapped s H) oa).run targets >>= cont) =
      avg fun Rs : Fin s → K ↦ fidPr (cont (fidEagRun (fidItsrEag H Rs) oa targets)) := by
  refine fidLazy_eq_eager (dead := fun targets (i : Fin s) ↦ i.1 < targets.length) ?_ ?_ ?_
    oa targets cont
  · intro t targets
    rcases t with q | x
    · exact Or.inl fun Rs ↦ rfl
    · by_cases h : targets.length < s
      · right
        refine ⟨⟨targets.length, h⟩, fun k ↦ (k, targets ++ [(k, x)]), ?_, ?_, ?_⟩
        · simp [fidItsrCapped, h]
        · intro Rs
          simp [fidItsrEag, rndAt, h]
        · intro k
          simp
      · left
        intro Rs
        simp [fidItsrCapped, fidItsrEag, rndAt, h]
  · intro Rs t targets i hi
    rcases t with q | x
    · exact hi
    · simp only [fidItsrEag, List.length_append, List.length_singleton]
      omega
  · intro Rs t targets i k hi
    rcases t with q | x
    · rfl
    · simp only [fidItsrEag]
      rw [rndAt_update Rs i k (Nat.ne_of_gt hi)]

/-- VCVio's transcript for the requests `t` of the exact game and the table `Rs`. -/
noncomputable def fidItsrSt (Rs : Fin s → K) (t : List Xm) : ITSRTranscript K Xm :=
  t.mapIdx fun j x ↦ (rndAt Rs j, x)

/-- The table-run of VCVio's adversary is the classical run against the challenger `rndCh`
of the exact game. -/
theorem fid_itsr_eag_run (H : K × Xm → D) (Rs : Fin s → K) {α : Type}
    (oa : OracleComp ((K × Xm →ₒ D) + (Xm →ₒ K)) α) (t : List Xm) :
    fidEagRun (fidItsrEag H Rs) oa (fidItsrSt Rs t) =
      ((fidGRun (fidItsrCodec K Xm) H (rndCh Rs) oa t).1,
        fidItsrSt Rs (fidGRun (fidItsrCodec K Xm) H (rndCh Rs) oa t).2) := by
  induction oa using OracleComp.inductionOn generalizing t with
  | pure a => rfl
  | query_bind q k ih =>
    rcases q with q | x
    · exact ih (H q) t
    · have e : fidItsrEag H Rs (.inr x) (fidItsrSt Rs t) =
          (rndAt Rs t.length, fidItsrSt Rs (t ++ [x])) := by
        simp [fidItsrEag, fidItsrSt, List.mapIdx_concat]
      change fidEagRun _ (k (fidItsrEag H Rs (.inr x) (fidItsrSt Rs t)).1)
        (fidItsrEag H Rs (.inr x) (fidItsrSt Rs t)).2 = _
      rw [e]
      exact ih _ _

theorem fid_itsr_run_length (H : K × Xm → D) (Rs : Fin s → K) {α : Type}
    (oa : OracleComp ((K × Xm →ₒ D) + (Xm →ₒ K)) α) (n : ℕ) (t : List Xm)
    (hb : IsQueryBoundP oa fidIsReq n) :
    (fidGRun (fidItsrCodec K Xm) H (rndCh Rs) oa t).2.length ≤ t.length + n := by
  induction oa using OracleComp.inductionOn generalizing n t with
  | pure a => exact Nat.le_add_right _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    rcases q with q | x
    · exact ih (H q) n t (by simpa [fidIsReq] using hb.2 (H q))
    · have hn0 : 0 < n := by simpa [fidIsReq] using hb.1
      have h := ih (rndAt Rs t.length : K) (n - 1) (t ++ [x])
        (by simpa [fidIsReq] using hb.2 (rndAt Rs t.length : K))
      rw [List.length_append, List.length_singleton] at h
      exact h.trans (by omega)

/-- VCVio's winning relation on the transcript of a table-run is the winning condition of the
exact game, for transcripts within the cap. -/
theorem fid_itsr_wins_iff (indices : D → List Index) (H : K × Xm → D) (Rs : Fin s → K)
    (t : List Xm) (ht : t.length ≤ s) (cand : K × Xm) (u : QReg) :
    (fidItsrProblem indices H).Wins (fidItsrSt Rs t) cand ↔
      itsrAWin (fidItsrCov indices) Rs H ⟨u, (cand, t)⟩ := by
  have hmem : ∀ z : K × Xm, z ∈ fidItsrSt Rs t ↔ isTgt Rs t z := by
    intro z
    unfold fidItsrSt isTgt
    rw [List.mem_mapIdx]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjs : j < s := lt_of_lt_of_le hj ht
      exact ⟨⟨j, hjs⟩, by simp [rndAt, hjs], by simp [hj]⟩
    · rintro ⟨j, hR, hx⟩
      have hj : j.1 < t.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hx
        exact absurd hx (by simp)
      refine ⟨j.1, hj, ?_⟩
      rw [List.getElem?_eq_getElem hj] at hx
      refine Prod.ext ?_ (Option.some.inj hx)
      simp [rndAt, j.2, hR]
  unfold ITSRProblem.Wins itsrAWin itsrATargets fidItsrCov
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [hmem]
  refine and_congr Iff.rfl (forall_congr' fun i ↦ forall_congr' fun _ ↦ ?_)
  unfold ITSRProblem.targetIndexSet
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨z, hz, hi⟩
    exact ⟨H z, ⟨z, (hmem z).1 hz, rfl⟩, hi⟩
  · rintro ⟨d, ⟨z, hz, rfl⟩, hi⟩
    exact ⟨z, (hmem z).2 hz, hi⟩

theorem fid_itsr_run_lift (indices : D → List Index) (H : K × Xm → D) {α : Type}
    (oa : ProbComp α) (targets : ITSRTranscript K Xm) :
    (simulateQ (ITSROracles (fidItsrProblem indices H))
      (liftM oa : OracleComp (unifSpec + ITSRTargetSpec Xm K) α)).run targets =
      oa >>= fun a ↦ pure (a, targets) := by
  unfold ITSROracles
  rw [QueryImpl.simulateQ_add_liftM_left]
  simp

/-- **Pre-sampling for VCVio's ITSR experiment**: on the honest adversary with at most `s`
target queries, VCVio's advantage (fresh key per target query) is the average over the coin
and a uniform table `Rs : Fin s → K` of the winning indicator of the classical run in which
the `i`-th target query is answered `Rs i`. -/
theorem fid_itsr_advantage (indices : D → List Index) (A : FidItsrAdv Ω K Xm D)
    (hb : ∀ ω, IsQueryBoundP (A ω) fidIsReq s) (H : K × Xm → D) :
    ITSRAdvantage (fidItsrHonest indices A H) =
      avg fun ω : Ω ↦ avg fun Rs : Fin s → K ↦
        ind (itsrAWin (fidItsrCov indices) Rs H ⟨QReg.of Unit,
          fidGRun (fidItsrCodec K Xm) H (rndCh Rs) (A ω) []⟩) := by
  rw [ITSRAdvantage_eq_evalDist_experiment]
  have hexp : ITSRExperiment (fidItsrHonest indices A H) =
      (($ᵗ Ω : ProbComp Ω) >>= fun ω ↦
        (simulateQ (ITSROracles (fidItsrProblem indices H))
          (simulateQ (fidItsrInst H) (A ω))).run [] >>= fun z ↦
            pure (decide ((fidItsrProblem indices H).Wins z.2 z.1))) := by
    unfold ITSRExperiment ITSRAdversary.run fidItsrHonest
    rw [simulateQ_bind, StateT.run_bind, fid_itsr_run_lift]
    simp only [bind_assoc, pure_bind]
  rw [hexp]
  refine (fidPr_uniform_bind _).trans (avg_congr fun ω ↦ ?_)
  rw [fid_itsr_compose, fid_itsr_capped (s := s) indices H (A ω) s [] (hb ω) (by simp),
    fid_itsr_presample]
  refine avg_congr fun Rs ↦ ?_
  have h := fid_itsr_eag_run H Rs (A ω) []
  rw [show ([] : ITSRTranscript K Xm) = fidItsrSt Rs [] from rfl, h, fidPr_pure]
  have hlen := fid_itsr_run_length H Rs (A ω) s [] (hb ω)
  have hw := fid_itsr_wins_iff indices H Rs
    (fidGRun (fidItsrCodec K Xm) H (rndCh Rs) (A ω) []).2 (by simpa using hlen)
    (fidGRun (fidItsrCodec K Xm) H (rndCh Rs) (A ω) []).1 (QReg.of Unit)
  by_cases hc : itsrAWin (fidItsrCov indices) Rs H ⟨QReg.of Unit,
      fidGRun (fidItsrCodec K Xm) H (rndCh Rs) (A ω) []⟩
  · exact (ind_of_true (decide_eq_true_iff.2 (hw.2 hc))).trans (ind_of_true hc).symm
  · exact (ind_of_false fun h' ↦ hc (hw.1 (decide_eq_true_iff.1 h'))).trans
      (ind_of_false hc).symm

/-- **Fidelity of the exact adaptive ITSR game.** -/
theorem fid_itsr_eq (indices : D → List Index) (A : FidItsrAdv Ω K Xm D)
    (hb : ∀ ω, IsQueryBoundP (A ω) fidIsReq s) :
    itsrAdaptiveExp .instruments (A := QReg.of Unit) (SubState.basis ()) s (fidItsrEmb A s)
        (fidItsrCov indices) =
      avg fun H : K × Xm → D ↦ ITSRAdvantage (fidItsrHonest indices A H) := by
  rw [fid_itsr_exact _ A hb, avg_comm]
  refine avg_congr fun H ↦ ?_
  rw [avg_comm]
  exact (fid_itsr_advantage indices A hb H).symm

/-- **`itsr_adaptive_le` as a bound on VCVio's ITSR advantage**, averaged over the uniformly
random keyed hash: classical adversaries with a uniform coin, at most `q` classical queries to
`H` and at most `s` target queries. -/
theorem fid_itsr_classical_le (indices : D → List Index) (A : FidItsrAdv Ω K Xm D) (q : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A ω) fidIsReq s) (hq : ∀ ω, IsQueryBoundP (A ω) fidIsHash q) :
    (avg fun H : K × Xm → D ↦ ITSRAdvantage (fidItsrHonest indices A H)) ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) (fidItsrCov indices) +
          (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  rw [← fid_itsr_eq indices A hb]
  exact itsr_adaptive_le (fidItsrCov_mono indices)
    (fidMapOut_isQueryBound _ s _ (fidSCoin_emb_isQueryBound _ A s q hq))

end Itsr

end PQ.QROM

namespace PQ.QROM

/-! ## The FORS index structure -/

section Fors

variable {K Xm Ix Lx Ω : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm]
  [DecidableEq Xm] [Fintype Ix] [DecidableEq Ix] [AddCommGroup Ix] [Fintype Lx] [DecidableEq Lx]
  [AddCommGroup Lx] [SampleableType K] [Fintype Ω] [Nonempty Ω] [SampleableType Ω] {k s : ℕ}

/-- The semantic indices of a FORS digest `(instance, k leaf indices)`: one index
`(instance, tree, leaf)` per tree. -/
def fidForsIndices (u : Ix × (Fin k → Lx)) : List (Ix × Fin k × Lx) :=
  (List.finRange k).map fun j ↦ (u.1, j, u.2 j)

/-- VCVio's subset relation for the FORS indices is the FORS cover relation `forsCov`. -/
theorem fidItsrCov_fors_iff (S : Finset (Ix × (Fin k → Lx))) (u : Ix × (Fin k → Lx)) :
    fidItsrCov (fidForsIndices (k := k)) S u ↔ forsCov S u := by
  unfold fidItsrCov forsCov fidForsIndices
  constructor
  · intro h j
    obtain ⟨d, hd, hi⟩ := h (u.1, j, u.2 j) (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩)
    obtain ⟨j', -, hj'⟩ := List.mem_map.1 hi
    simp only [Prod.mk.injEq] at hj'
    obtain ⟨h1, rfl, h3⟩ := hj'
    exact ⟨d, hd, h1, h3⟩
  · intro h i hi
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
    obtain ⟨d, hd, h1, h2⟩ := h j
    exact ⟨d, hd, List.mem_map.2 ⟨j, List.mem_finRange j, by rw [h1, h2]⟩⟩

theorem fid_coverProb_congr {D ι : Type} [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]
    (Cov Cov' : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)] [∀ S, DecidablePred (Cov' S)]
    (h : ∀ S u, Cov S u ↔ Cov' S u) : coverProb ι Cov = coverProb ι Cov' := by
  unfold coverProb covered
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Finset.filter_congr fun u _ ↦ h _ u]

/-- **Adaptive ITSR with the FORS index structure, for VCVio's advantage**, averaged over the
uniformly random `H_msg`, with the closed form of the covering probability. -/
theorem fid_itsr_fors_classical_le [Nonempty Ix] [Nonempty Lx]
    (A : FidItsrAdv Ω K Xm (Ix × (Fin k → Lx))) (q : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A ω) fidIsReq s) (hq : ∀ ω, IsQueryBoundP (A ω) fidIsHash q) :
    (avg fun H : K × Xm → Ix × (Fin k → Lx) ↦
        ITSRAdvantage (fidItsrHonest (fidForsIndices (k := k)) A H)) ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 *
          (∑ γ ∈ Finset.range (s + 1),
            (s.choose γ : ℝ≥0∞) * ((Fintype.card Ix : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card Ix : ℝ≥0∞)⁻¹) ^ (s - γ) *
              (1 - (1 - (Fintype.card Lx : ℝ≥0∞)⁻¹) ^ γ) ^ k) +
          (s : ℝ≥0∞) ^ 2 / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := fid_itsr_classical_le (fidForsIndices (k := k)) A q hb hq
  rw [fid_coverProb_congr _ (forsCov (I := Ix) (L := Lx) (k := k)) fidItsrCov_fors_iff,
    coverProb_fors, Fintype.card_fin] at h
  exact h

end Fors

end PQ.QROM

#print axioms PQ.QROM.fid_itsr_fors_classical_le
#print axioms PQ.QROM.fidMapOut_flat
#print axioms PQ.QROM.fid_itsr_presample
#print axioms PQ.QROM.fid_itsr_advantage
#print axioms PQ.QROM.fid_itsr_eq
#print axioms PQ.QROM.fid_itsr_classical_le

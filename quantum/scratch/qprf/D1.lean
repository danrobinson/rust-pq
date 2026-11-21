import Integration.SlhDsaBridgeItsr
import PQ.QROM.ItsrPullback

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped Kronecker ComplexOrder
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Reduction.QItsr
open Reduction.QMsg

section Presample
open KeyedHash

variable {W : Type} [Fintype W] {K X Y Index : Type} [Fintype K] [DecidableEq K]
  [SampleableType K] [Nonempty K] {s : ℕ}

/-- The ITSR target oracle answered by presampled randomizers. -/
noncomputable def rndImpl (Rs : Fin s → K) :
    QueryImpl (unifSpec + ITSRTargetSpec X K) (StateT (List X) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List X) ProbComp) +
    fun x ↦ (StateT.mk fun t ↦ pure (rndAt Rs t.length, t ++ [x]) : StateT (List X) ProbComp _)

theorem forwardsUnif_rndImpl (Rs : Fin s → K) : ForwardsUnif (rndImpl (X := X) Rs) :=
  forwardsUnif_ofLift_add _

/-- Target queries of an ITSR machine. -/
def isT : InstrIdx W ⊕ (ℕ ⊕ X) → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred (isT (W := W) (X := X)) := fun t ↦ by
  rcases t with _ | _ | _ <;> unfold isT <;> infer_instance

/-- The transcript of requests `l` issued from index `i` on. -/
noncomputable def pairs (Rs : Fin s → K) (i : ℕ) (l : List X) : ITSRTranscript K X :=
  l.mapIdx fun j x ↦ (rndAt Rs (i + j), x)

theorem pairs_cons (Rs : Fin s → K) (i : ℕ) (x : X) (l : List X) :
    pairs Rs i (x :: l) = (rndAt Rs i, x) :: pairs Rs (i + 1) l := by
  unfold pairs
  rw [List.mapIdx_cons]
  simp only [Nat.add_zero]
  congr 1
  congr 1
  funext j y
  rw [Nat.add_assoc, Nat.add_comm 1 j]

theorem close_rndImpl_prefix {α : Type} (Rs : Fin s → K)
    (Q : QOC W (unifSpec + ITSRTargetSpec X K) α) :
    ∀ t : List X, AllQueries (fun _ ↦ True) (fun z : α × List X ↦ t <+: z.2)
      (close (rndImpl Rs) Q t) := by
  induction Q using OracleComp.inductionOn with
  | pure a => intro t; exact List.prefix_refl _
  | query_bind q k ih =>
    intro t
    rcases q with j | n | x
    · rw [close_instr_bind]
      exact ⟨trivial, fun i ↦ ih i t⟩
    · rw [close_unif_bind _ (forwardsUnif_rndImpl Rs)]
      exact ⟨trivial, fun i ↦ ih i t⟩
    · rw [close_query_bind]
      change AllQueries _ _ (liftU (pure (rndAt Rs t.length, t ++ [x])) >>= _)
      rw [liftU_pure, pure_bind]
      exact allQ_mono (fun _ h ↦ h) (fun z h ↦ (List.prefix_append t [x]).trans h) (ih _ _)

theorem rndImpl_run_tgt (Rs : Fin s → K) (x : X) (t : List X) :
    (rndImpl Rs (Sum.inr x)).run t = pure (rndAt Rs t.length, t ++ [x]) := rfl

theorem close_rndImpl_congr {α : Type} (Rs Rs' : Fin s → K)
    (Q : QOC W (unifSpec + ITSRTargetSpec X K) α) :
    ∀ t : List X, (∀ j : ℕ, t.length ≤ j → rndAt Rs j = rndAt Rs' j) →
      close (rndImpl Rs) Q t = close (rndImpl Rs') Q t := by
  induction Q using OracleComp.inductionOn with
  | pure a => intro t _; rfl
  | query_bind q k ih =>
    intro t h
    rcases q with j | n | x
    · rw [close_instr_bind, close_instr_bind]
      simp only [fun i ↦ ih i t h]
    · rw [close_unif_bind _ (forwardsUnif_rndImpl Rs), close_unif_bind _ (forwardsUnif_rndImpl Rs')]
      simp only [fun i ↦ ih i t h]
    · rw [close_query_bind, close_query_bind, rndImpl_run_tgt, rndImpl_run_tgt, h _ le_rfl]
      simp only [liftU_pure, pure_bind]
      refine ih _ _ fun j hj ↦ h j ?_
      simp at hj
      omega

theorem qWeight_congr_allQ {α : Type} {g : InstrIdx W ⊕ ℕ → Prop} {P : α → Prop}
    {E E' : α → Prop} [DecidablePred E] [DecidablePred E'] {X' : Closed W α}
    (hX : AllQueries g P X') (h : ∀ a, P a → (E a ↔ E' a)) :
    ∀ ρ, qWeight E X' ρ = qWeight E' X' ρ := by
  induction X' using OracleComp.inductionOn with
  | pure a =>
    intro ρ
    simp only [qWeight_pure]
    by_cases hE : E a
    · rw [ite_eq_left hE, ite_eq_left ((h a hX).1 hE)]
    · rw [ite_eq_right hE, ite_eq_right fun h' ↦ hE ((h a hX).2 h')]
  | query_bind q k ih =>
    intro ρ
    rcases q with j | n
    · rw [qWeight_instr_bind, qWeight_instr_bind]
      exact Finset.sum_congr rfl fun i _ ↦ ih i (hX.2 i) _
    · rw [qWeight_unif_bind, qWeight_unif_bind]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ ih i (hX.2 i) _

theorem avg_coord_sum (j : Fin s) (f : (Fin s → K) → K → ℝ≥0∞)
    (hf : ∀ Rs r R, f (Function.update Rs j r) R = f Rs R) :
    avg (fun Rs : Fin s → K ↦ f Rs (Rs j)) =
      (Fintype.card K : ℝ≥0∞)⁻¹ * ∑ R, avg fun Rs : Fin s → K ↦ f Rs R := by
  classical
  have e : ∀ Rs : Fin s → K, f Rs (Rs j) = ∑ R, if Rs j = R then f Rs R else 0 := fun Rs ↦ by
    rw [Finset.sum_ite_eq]; simp
  simp only [e]
  rw [avg_finset_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun R _ ↦ avg_coord_eq j R (fun Rs ↦ f Rs R) fun Rs r ↦ hf Rs r R

theorem pairs_update (Rs : Fin s → K) (j : Fin s) (r : K) (i : ℕ) (hij : j.1 < i) (l : List X) :
    pairs (Function.update Rs j r) i l = pairs Rs i l := by
  unfold pairs
  refine List.mapIdx_eq_mapIdx_iff.2 fun m _ ↦ ?_
  rw [rndAt_update Rs j r (by omega)]

theorem rndAt_lt (Rs : Fin s → K) (i : ℕ) (hi : i < s) : rndAt Rs i = Rs ⟨i, hi⟩ := by
  unfold rndAt; simp [hi]

/-- **Presampling of the ITSR randomizers.**  Against a machine with at most `n` target queries
left, `|t| + n ≤ s`, the fresh-key target oracle is the average over presampled randomizers
`Rs : Fin s → K` of the deterministic challenger `rndImpl Rs`; the transcript is rebuilt from the
recorded requests. -/
theorem presample (prob : ITSRProblem K X Y Index) (hkey : prob.khf.keygen = $ᵗ K)
    (E : (K × X) × ITSRTranscript K X → Prop) [DecidablePred E]
    (Q : QOC W (unifSpec + ITSRTargetSpec X K) (K × X)) :
    ∀ (n : ℕ) (t : List X) (tr : ITSRTranscript K X), CountBound isT Q n → t.length + n ≤ s →
      ∀ ρ, qWeight E (close (ITSROracles prob) Q tr) ρ =
        avg fun Rs : Fin s → K ↦ qWeight (fun z ↦ E (z.1, tr ++ pairs Rs t.length
          (z.2.drop t.length))) (close (rndImpl Rs) Q t) ρ := by
  have hfI : ForwardsUnif (ITSROracles prob) := forwardsUnif_ofLift_add _
  induction Q using OracleComp.inductionOn with
  | pure a =>
    intro n t tr _ _ ρ
    simp only [close_pure, qWeight_pure, List.drop_length, pairs, List.mapIdx_nil,
      List.append_nil]
    rw [avg_const]
  | query_bind q k ih =>
    intro n t tr hQ hlen ρ
    rcases q with j | m | x
    · rw [close_instr_bind, qWeight_instr_bind]
      conv_rhs => arg 1; ext Rs; rw [close_instr_bind, qWeight_instr_bind]
      rw [avg_finset_sum]
      exact Finset.sum_congr rfl fun i _ ↦ ih i n t tr (hQ i) hlen _
    · rw [close_unif_bind _ hfI, qWeight_unif_bind]
      conv_rhs => arg 1; ext Rs; rw [close_unif_bind _ (forwardsUnif_rndImpl _), qWeight_unif_bind]
      rw [avg_mul_left, avg_finset_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ ih i n t tr (hQ i) hlen _
    · obtain ⟨hn, hk⟩ := hQ
      have hi : t.length < s := by omega
      have hlen' : (t ++ [x]).length + (n - 1) ≤ s := by simp; omega
      rw [close_query_bind]
      have hrun : ((ITSROracles prob) (Sum.inr x)).run tr =
          ($ᵗ K) >>= fun R ↦ pure (R, tr ++ [(R, x)]) := by
        change (ITSRTargetOracle prob x).run tr = _
        rw [ITSRTargetOracle_run, hkey]
      rw [hrun, liftU_bind, bind_assoc]
      simp only [liftU_pure, pure_bind]
      rw [qWeight_liftU_uniform_bind]
      simp only [fun (R : K) ↦ ih R (n - 1) (t ++ [x]) (tr ++ [(R, x)]) (hk R) hlen' ρ]
      simp only [close_query_bind, rndImpl_run_tgt, liftU_pure, pure_bind]
      set f : (Fin s → K) → K → ℝ≥0∞ := fun Rs R ↦
        qWeight (fun z ↦ E (z.1, (tr ++ [(R, x)]) ++ pairs Rs (t ++ [x]).length
          (z.2.drop (t ++ [x]).length))) (close (rndImpl Rs) (k R) (t ++ [x])) ρ with hf
      have hint : ∀ Rs : Fin s → K,
          qWeight (fun z ↦ E (z.1, tr ++ pairs Rs t.length (z.2.drop t.length)))
            (close (rndImpl Rs) (k (rndAt Rs t.length)) (t ++ [x])) ρ =
          f Rs (Rs ⟨t.length, hi⟩) := by
        intro Rs
        rw [hf, ← rndAt_lt Rs _ hi]
        refine qWeight_congr_allQ (close_rndImpl_prefix Rs _ _) (fun z hz ↦ ?_) ρ
        obtain ⟨r, hr⟩ := hz
        rw [← hr]
        simp only [List.append_assoc, List.singleton_append, List.length_append,
          List.length_singleton, List.drop_left' rfl]
        rw [show (t ++ x :: r).drop (t.length + 1) = r by simp, pairs_cons]
      simp only [hint]
      rw [avg_coord_sum ⟨t.length, hi⟩ f fun Rs r R ↦ ?_]
      rw [hf]
      simp only
      rw [close_rndImpl_congr (Function.update Rs ⟨t.length, hi⟩ r) Rs _ _ (fun j hj ↦ by
          refine rndAt_update Rs _ r ?_
          simp at hj
          show j ≠ t.length
          omega),
        ]
      have hlt : (⟨t.length, hi⟩ : Fin s).1 < (t ++ [x]).length := by simp
      simp only [pairs_update Rs ⟨t.length, hi⟩ r _ hlt]

end Presample

section CB
variable {α β : Type} {ι₁ ι₂ : Type} {sp₁ : OracleSpec ι₁} {sp₂ : OracleSpec ι₂}

lemma cb_mono {c : ι₁ → Prop} [DecidablePred c] {P : OracleComp sp₁ α} :
    ∀ {n n' : ℕ}, n ≤ n' → CountBound c P n → CountBound c P n' := by
  induction P using OracleComp.inductionOn with
  | pure a => intro _ _ _ _; trivial
  | query_bind t k ih =>
    intro n n' hn h
    change (if c t then 0 < n' ∧ ∀ r, CountBound c (k r) (n' - 1) else ∀ r, CountBound c (k r) n')
    change (if c t then 0 < n ∧ ∀ r, CountBound c (k r) (n - 1) else ∀ r, CountBound c (k r) n) at h
    split_ifs at h ⊢
    · exact ⟨by omega, fun r ↦ ih r (by omega) (h.2 r)⟩
    · exact fun r ↦ ih r hn (h r)

lemma cb_bind {c : ι₁ → Prop} [DecidablePred c] {P : OracleComp sp₁ α} {f : α → OracleComp sp₁ β}
    {n₂ : ℕ} (hf : ∀ a, CountBound c (f a) n₂) :
    ∀ {n₁ : ℕ}, CountBound c P n₁ → CountBound c (P >>= f) (n₁ + n₂) := by
  induction P using OracleComp.inductionOn with
  | pure a => intro n₁ _; rw [pure_bind]; exact cb_mono (by omega) (hf a)
  | query_bind t k ih =>
    intro n₁ h
    rw [bind_assoc]
    change (if c t then 0 < n₁ ∧ ∀ r, CountBound c (k r) (n₁ - 1) else
      ∀ r, CountBound c (k r) n₁) at h
    change (if c t then 0 < n₁ + n₂ ∧ ∀ r, CountBound c (k r >>= f) (n₁ + n₂ - 1) else
      ∀ r, CountBound c (k r >>= f) (n₁ + n₂))
    split_ifs at h ⊢
    · refine ⟨by omega, fun r ↦ ?_⟩
      have := ih r (h.2 r)
      rwa [show n₁ - 1 + n₂ = n₁ + n₂ - 1 by omega] at this
    · exact fun r ↦ ih r (h r)

lemma cb_of_allQ {c : ι₁ → Prop} [DecidablePred c] {g : α → Prop} {P : OracleComp sp₁ α}
    (h : AllQueries (fun t ↦ ¬ c t) g P) (n : ℕ) : CountBound c P n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    change (if c t then 0 < n ∧ ∀ r, CountBound c (k r) (n - 1) else ∀ r, CountBound c (k r) n)
    split_ifs with hc
    · exact absurd hc h.1
    · exact fun r ↦ ih r (h.2 r) n

lemma cb_query {c : ι₁ → Prop} [DecidablePred c] (t : ι₁) :
    CountBound c (liftM (sp₁.query t) : OracleComp sp₁ _) (if c t then 1 else 0) := by
  rw [← bind_pure (liftM (sp₁.query t) : OracleComp sp₁ _)]
  by_cases ht : c t
  · rw [if_pos ht]
    show (if c t then 0 < 1 ∧ ∀ r, CountBound c (pure r : OracleComp sp₁ (sp₁.Range t)) (1 - 1)
      else ∀ r, CountBound c (pure r : OracleComp sp₁ (sp₁.Range t)) 1)
    rw [if_pos ht]
    exact ⟨Nat.one_pos, fun _ ↦ trivial⟩
  · rw [if_neg ht]
    show (if c t then 0 < 0 ∧ ∀ r, CountBound c (pure r : OracleComp sp₁ (sp₁.Range t)) (0 - 1)
      else ∀ r, CountBound c (pure r : OracleComp sp₁ (sp₁.Range t)) 0)
    rw [if_neg ht]
    exact fun _ ↦ trivial

lemma cb_map {c : ι₁ → Prop} [DecidablePred c] (f : α → β) {P : OracleComp sp₁ α} {n : ℕ}
    (h : CountBound c P n) : CountBound c (f <$> P) n := by
  rw [map_eq_bind_pure_comp]
  have := cb_bind (f := pure ∘ f) (n₂ := 0) (fun _ ↦ trivial) h
  simpa using this

lemma cb_bind_pure {c : ι₁ → Prop} [DecidablePred c] {P : OracleComp sp₁ α} {g : α → β}
    {n : ℕ} (h : CountBound c P n) : CountBound c (P >>= fun a ↦ pure (g a)) n := by
  rw [bind_pure_comp]; exact cb_map _ h

lemma cb_pure' {c : ι₁ → Prop} [DecidablePred c] (a : α) (n : ℕ) :
    CountBound c (pure a : OracleComp sp₁ α) n := trivial

lemma cb_simulateQ {c₁ : ι₁ → Prop} [DecidablePred c₁] {c₂ : ι₂ → Prop} [DecidablePred c₂]
    (h : QueryImpl sp₁ (OracleComp sp₂))
    (hh : ∀ t, CountBound c₂ (h t) (if c₁ t then 1 else 0)) {P : OracleComp sp₁ α} :
    ∀ {n : ℕ}, CountBound c₁ P n → CountBound c₂ (simulateQ h P) n := by
  induction P using OracleComp.inductionOn with
  | pure a => intro n _; rw [simulateQ_pure]; trivial
  | query_bind t k ih =>
    intro n hP
    rw [simulateQ_bind, simulateQ_spec_query]
    change (if c₁ t then 0 < n ∧ ∀ r, CountBound c₁ (k r) (n - 1) else
      ∀ r, CountBound c₁ (k r) n) at hP
    by_cases ht : c₁ t
    · rw [if_pos ht] at hP
      have := cb_bind (fun r ↦ ih r (hP.2 r)) (hh t)
      rw [if_pos ht] at this
      rwa [show 1 + (n - 1) = n by omega] at this
    · rw [if_neg ht] at hP
      have := cb_bind (fun r ↦ ih r (hP r)) (hh t)
      rwa [if_neg ht, Nat.zero_add] at this

lemma cb_simulateQ_state {σ : Type} {c₁ : ι₁ → Prop} [DecidablePred c₁] {c₂ : ι₂ → Prop}
    [DecidablePred c₂] (h : QueryImpl sp₁ (StateT σ (OracleComp sp₂)))
    (hh : ∀ t s, CountBound c₂ ((h t).run s) (if c₁ t then 1 else 0)) {P : OracleComp sp₁ α} :
    ∀ {n : ℕ}, CountBound c₁ P n → ∀ s, CountBound c₂ ((simulateQ h P).run s) n := by
  induction P using OracleComp.inductionOn with
  | pure a => intro n _ s; rw [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind t k ih =>
    intro n hP s
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change (if c₁ t then 0 < n ∧ ∀ r, CountBound c₁ (k r) (n - 1) else
      ∀ r, CountBound c₁ (k r) n) at hP
    by_cases ht : c₁ t
    · rw [if_pos ht] at hP
      have := cb_bind (fun r ↦ ih r.1 (hP.2 r.1) r.2) (hh t s)
      rw [if_pos ht] at this
      rwa [show 1 + (n - 1) = n by omega] at this
    · rw [if_neg ht] at hP
      have := cb_bind (fun r ↦ ih r.1 (hP r.1) r.2) (hh t s)
      rwa [if_neg ht, Nat.zero_add] at this

end CB

section QCB
variable {W : Type} [Fintype W] {α : Type} {ι ι' : Type} {spec : OracleSpec ι}
  {spec' : OracleSpec ι'} {τ : Type}

/-- Counted classical indices of a quantum machine (instruments never counted). -/
def QC (W : Type) [Fintype W] (c : ι → Prop) : InstrIdx W ⊕ ι → Prop
  | .inl _ => False
  | .inr t => c t

instance (c : ι → Prop) [DecidablePred c] : DecidablePred (QC W c) := fun t ↦ by
  rcases t with _ | _ <;> unfold QC <;> infer_instance

lemma cb_liftQ {c : ι → Prop} [DecidablePred c] {ob : OracleComp spec α} {n : ℕ}
    (h : CountBound c ob n) : CountBound (QC W c) (liftQ ob : QOC W spec α) n :=
  cb_simulateQ _ (fun t ↦ cb_query (c := QC W c) (Sum.inr t)) h

lemma cb_wrap0 {c : ι → Prop} [DecidablePred c] {c' : (unifSpec + spec').Domain → Prop}
    [DecidablePred c'] (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    (hh : ∀ t, CountBound c' (h t) (if c t then 1 else 0)) {Q : QOC W spec α} {n : ℕ}
    (hQ : CountBound (QC W c) Q n) : CountBound (QC W c') (wrap0 h Q) n := by
  refine cb_simulateQ _ ?_ hQ
  rintro (j | t)
  · exact cb_query (c := QC W c') (Sum.inl j)
  · exact cb_liftQ (hh t)

lemma cb_wrap {c : ι → Prop} [DecidablePred c] {c' : (unifSpec + spec').Domain → Prop}
    [DecidablePred c'] (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    (hh : ∀ t s, CountBound c' ((implB t).run s) (if c t then 1 else 0)) {Q : QOC W spec α}
    {n : ℕ} (hQ : CountBound (QC W c) Q n) (s : τ) : CountBound (QC W c') (wrap implB Q s) n := by
  refine cb_simulateQ_state _ ?_ hQ s
  rintro (j | t) s
  · exact cb_map _ (cb_query (c := QC W c') (Sum.inl j))
  · exact cb_liftQ (hh t s)

end QCB

section Chain1
variable {W : Type} [Fintype W] {α : Type}

/-- The counted index: the second summand. -/
def isR {A B : Type} : A ⊕ B → Prop
  | .inr _ => True
  | .inl _ => False

instance {A B : Type} : DecidablePred (isR (A := A) (B := B)) := fun t ↦ by
  rcases t with _ | _ <;> unfold isR <;> infer_instance

lemma allQ_and {ι : Type} {sp : OracleSpec ι} {G : ι → Prop} {g : α → Prop}
    {P : OracleComp sp α} (h1 : AllQueries G (fun _ ↦ True) P)
    (h2 : AllQueries (fun _ ↦ True) g P) : AllQueries G g P := by
  induction P using OracleComp.inductionOn with
  | pure a => exact h2
  | query_bind t k ih => exact ⟨h1.1, fun r ↦ ih r (h1.2 r) (h2.2 r)⟩

lemma allQ_out_simulateQ {ι₁ ι₂ : Type} {sp₁ : OracleSpec ι₁} {sp₂ : OracleSpec ι₂}
    {g : α → Prop} (h : QueryImpl sp₁ (OracleComp sp₂)) {G : ι₁ → Prop} {P : OracleComp sp₁ α}
    (hP : AllQueries G g P) : AllQueries (fun _ ↦ True) g (simulateQ h P) :=
  allQ_simulateQ h (fun t _ ↦ allQ_true_of (fun _ ↦ trivial) _)
    (allQ_mono (good' := fun _ ↦ True) (fun _ _ ↦ trivial) (fun _ h ↦ h) hP)

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E]

theorem cb_compileQ (H : X → Y)
    (P : QOC ((X × Y) × E) (portSpec + (unifSpec + ((List Byte × List Byte) →ₒ Option (List Byte))))
      ((List Byte × List Byte) × Option (List Byte))) {n : ℕ}
    (hP : CountBound isSign P n) :
    CountBound (QC (WS X Y E) isR) (compileQ H P) n := by
  refine cb_simulateQ _ ?_ hP
  rintro (j | ⟨⟩ | m | mc)
  · exact cb_query (c := QC (WS X Y E) isR) (Sum.inl _)
  · exact cb_map _ (cb_query (c := QC (WS X Y E) isR) (Sum.inl _))
  · exact cb_query (c := QC (WS X Y E) isR) (Sum.inr (Sum.inl m))
  · exact cb_query (c := QC (WS X Y E) isR) (Sum.inr (Sum.inr mc))

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
  [Inhabited prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
  {optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}

theorem cb_qPureBytesToInternal (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    {n : ℕ} (hB : ∀ pk, CountBound (QC W isR) (B.main pk) n) (pk : PublicKeyCore prims.core) :
    CountBound (QC W isR) ((qPureBytesToInternal B).main pk) n := by
  unfold qPureBytesToInternal qToInternal qPureBytesToTyped QForger.wrapForger
  dsimp only
  refine cb_map _ (cb_wrap0 (c := isR) _ ?_ (cb_map _ (cb_wrap0 (c := isR) _ ?_ (hB _))))
  · rintro (m | mc)
    · exact cb_query (c := isR) (Sum.inl m)
    · simp only [Guarded.signingImpl]
      rcases pureEncode mc with x | m
      · exact cb_mono (n := 0) (by simp [isR]) trivial
      · exact cb_map _ (cb_query (c := isR) (Sum.inr m))
  · rintro (m | mc)
    · exact cb_query (c := isR) (Sum.inl m)
    · exact cb_map _ (cb_query (c := isR) (Sum.inr mc))

theorem out_qPureBytesToInternal (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (L : ℕ) (hB : ∀ pk, AllQueries (fun _ ↦ True)
      (fun z : (List Byte × List Byte) × Option (List Byte) ↦
        z.1.1.length + z.1.2.length + 2 ≤ L) (B.main pk)) (pk : PublicKeyCore prims.core) :
    AllQueries (fun _ ↦ True) (fun z : List Byte × _ ↦ z.1.length ≤ L)
      ((qPureBytesToInternal B).main pk) := by
  unfold qPureBytesToInternal qToInternal qPureBytesToTyped QForger.wrapForger
  dsimp only
  refine allQ_map (goodOut := fun o : (List Byte × List Byte) × _ ↦
      o.1.1.length + o.1.2.length + 2 ≤ L) _ ?_
    (allQ_out_simulateQ _ (allQ_map (goodOut := fun z : (List Byte × List Byte) × Option (List Byte) ↦
        z.1.1.length + z.1.2.length + 2 ≤ L) _ (fun z hz ↦ hz) (allQ_out_simulateQ _ (hB _))))
  rintro ⟨mc, o⟩ hz
  simp only [Guarded.readForgery]
  rcases he : pureEncode mc with x | m
  · simp
  · rcases o with y | σ
    · simp
    · have h := (encodePureMessage_ok_iff mc.2 mc.1 m).1 he
      simp only [h.2, List.length_append, List.length_cons, List.length_nil]
      simp only at hz
      omega

end Chain1

section Chain2
open Lazy
variable {W : Type} [Fintype W]
variable {vp : ValidatedParams} (prims : Primitives vp.params)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.Y] [DecidableEq prims.Y] [DecidableEq prims.PkSeed]
    [DecidableEq prims.AdrsKey] [Inhabited prims.Y] (L : ℕ)
  {optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}

/-- Game queries of an open program. -/
def isG {A B : Type} : ℕ ⊕ (A ⊕ B) → Prop
  | .inr (.inl _) => True
  | _ => False

instance {A B : Type} : DecidablePred (isG (A := A) (B := B)) := fun t ↦ by
  rcases t with _ | _ | _ <;> unfold isG <;> infer_instance

theorem allQ_noGame_of {α : Type} {P : OracleComp (OSpec prims (itsrG prims)) α}
    (h : AllQueries (GameG fun _ : ItsrIn prims ↦ False) (fun _ ↦ True) P) (n : ℕ) :
    CountBound isG P n :=
  cb_of_allQ (allQ_mono (fun t ht ↦ by rcases t with _ | _ | _ <;> simp_all [GameG, isG])
    (fun _ h ↦ h) h) n

theorem allQ_logSign (pk : PublicKeyCore prims.core) (P : ItsrIn prims → Prop)
    (m : List Byte) (hm : P (pk.pkSeed, pk.pkRoot, m)) (s : G2Log prims) :
    AllQueries (GameG P) (fun _ ↦ True)
      ((logSignOracle optRand pk (itsrRandomizerO pk.pkSeed pk.pkRoot)
        (fun m R ↦ Lazy.openSign prims (itsrG prims) m pk.pkSeed pk.pkRoot R) m).run s) := by
  simp only [logSignOracle, StateT.run_bind, StateT.run_monadLift, StateT.run_get, StateT.run_set,
    StateT.run_pure, bind_assoc, pure_bind, monadLift_self]
  refine allQ_bind (allQ_liftProb (fun _ ↦ trivial) _) fun addrnd _ ↦ ?_
  refine allQ_bind (mid := fun _ ↦ True) ?_ fun R _ ↦ ?_
  · unfold itsrRandomizerO
    split
    · trivial
    · exact allQ_bind (allQ_query (GameG P) (Sum.inr (Sum.inl _)) hm) fun _ _ ↦ trivial
  · exact allQ_bind (allQ_openSign prims (itsrG prims) P m pk.pkSeed pk.pkRoot R)
      fun _ _ ↦ trivial

theorem cb_logSign (pk : PublicKeyCore prims.core) (m : List Byte) (s : G2Log prims) :
    CountBound isG
      ((logSignOracle optRand pk (itsrRandomizerO pk.pkSeed pk.pkRoot)
        (fun m R ↦ Lazy.openSign prims (itsrG prims) m pk.pkSeed pk.pkRoot R) m).run s) 1 := by
  simp only [logSignOracle, StateT.run_bind, StateT.run_monadLift, StateT.run_get, StateT.run_set,
    StateT.run_pure, bind_assoc, pure_bind, monadLift_self]
  have h0 := cb_of_allQ (c := isG) (allQ_liftProb (G := fun t ↦ ¬ isG t)
    (sp := itsrG prims + ((ofFn fun _ : SecIdx ↦ prims.Y) + publicHashSpec prims.core))
    (fun n ↦ by simp [isG]) (optRand pk)) 0
  refine cb_mono (by omega) (cb_bind (n₂ := 1) (fun addrnd ↦ ?_) h0)
  refine cb_mono (by omega) (cb_bind (n₁ := 1) (n₂ := 0) (fun R ↦ ?_) ?_)
  · exact cb_bind_pure
      (allQ_noGame_of prims (allQ_openSign prims (itsrG prims) _ m pk.pkSeed pk.pkRoot R) 0)
  · unfold itsrRandomizerO
    split
    · exact cb_mono (n := 0) (by omega) trivial
    · unfold gameQ
      have := cb_query (c := isG) (sp₁ := OSpec prims (itsrG prims))
        (Sum.inr (Sum.inl (pk.pkSeed, pk.pkRoot, m)))
      simpa [isG] using this

/-- Target inputs within the cap. -/
def Ptgt (x : ItsrIn prims) : Prop := x.2.2.length ≤ L

theorem allQ_qItsrOpen (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, AllQueries (QG W (Gint L)) (fun z : List Byte × _ ↦ z.1.length ≤ L) (Q.main pk)) :
    AllQueries (QG W (GameG (Ptgt prims L))) (fun r : prims.Y × ItsrIn prims ↦ r.2.2.2.length ≤ L)
      (qItsrOpen Q) := by
  unfold qItsrOpen qRunForgerLog
  refine allQ_bind (allQ_liftQ (allQ_liftProb (fun _ ↦ trivial) _)) fun pkSeed _ ↦ ?_
  refine allQ_bind (allQ_liftQ (allQ_openKeygen prims _ _ pkSeed)) fun root _ ↦ ?_
  refine allQ_bind (allQ_wrap (G := Gint L) _ ?_ (hQ _) []) fun z hz ↦ allQ_liftQ hz
  rintro (n | m) s ht
  · simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
    exact allQ_bind (allQ_query _ (Sum.inl n) trivial) fun _ _ ↦ trivial
  · simp only [QueryImpl.add_apply_inr]
    exact allQ_logSign prims ⟨pkSeed, root⟩ _ m ht s

theorem cb_qItsrOpen (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) {n : ℕ}
    (hQ : ∀ pk, CountBound (QC W isR) (Q.main pk) n) :
    CountBound (QC W isG) (qItsrOpen Q) n := by
  unfold qItsrOpen qRunForgerLog
  have hp := cb_liftQ (W := W) (cb_of_allQ (c := isG) (allQ_liftProb (G := fun t ↦ ¬ isG t)
    (sp := itsrG prims + ((ofFn fun _ : SecIdx ↦ prims.Y) + publicHashSpec prims.core))
    (fun n ↦ by simp [isG]) pkSeedDist) 0)
  refine cb_mono (by omega) (cb_bind (n₂ := n) (fun pkSeed ↦ ?_) hp)
  have hk := fun pkSeed ↦ cb_liftQ (W := W) (allQ_noGame_of prims
    (allQ_openKeygen prims (itsrG prims) _ pkSeed) 0)
  refine cb_mono (by omega) (cb_bind (n₂ := n) (fun root ↦ ?_) (hk pkSeed))
  refine cb_mono (by omega) (cb_bind (n₂ := 0) (fun z ↦ by rw [liftQ_pure]; exact trivial)
    (cb_wrap (c := isR) _ ?_ (hQ _) []))
  rintro (m | msg) s
  · simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
    exact cb_mono (by simp [isR, isG]) (cb_bind_pure (cb_query (c := isG) (Sum.inl m)))
  · simp only [QueryImpl.add_apply_inr]
    exact cb_mono (by simp [isR]) (cb_logSign prims ⟨pkSeed, root⟩ msg s)

end Chain2

section Chain3
open Lazy
variable {W : Type} [Fintype W] {α ι κ : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κ}
  {D V : Type} [DecidableEq D] [SampleableType V]

theorem out_qLazyRun (hI : QueryImpl hspec Id) {g : α → Prop}
    (X : QOC W (RSpec gspec D V hspec) α) {G : _ → Prop} (hX : AllQueries G g X) :
    AllQueries (fun _ ↦ True) g (qLazyRun hI X) := by
  unfold qLazyRun
  refine allQ_out_simulateQ (G := fun _ ↦ True) _ (allQ_map (goodOut := fun z : α × _ ↦ g z.1) _ (fun z h ↦ h) ?_)
  exact allQ_mono (good' := fun _ ↦ True) (fun _ _ ↦ trivial) (fun _ h ↦ h)
    (allQ_simulateQ_state _ (fun t s _ ↦ allQ_true_of (fun _ ↦ trivial) _) hX [])

theorem cb_qLazyRun (hI : QueryImpl hspec Id) (X : QOC W (RSpec gspec D V hspec) α) {n : ℕ}
    (hX : CountBound (QC W isG) X n) : CountBound (QC W isR) (qLazyRun hI X) n := by
  unfold qLazyRun
  refine cb_wrap0 (c := isG) _ ?_ (cb_map _ (cb_wrap (c := isG) _ ?_ hX []))
  · rintro (m | t | d | q)
    · exact cb_query (c := isR) (Sum.inl m)
    · exact cb_query (c := isR) (Sum.inr t)
    · exact cb_of_allQ (allQ_liftProb (G := fun t ↦ ¬ isR t) (fun n ↦ by simp [isR]) _) _
    · exact cb_mono (n := 0) (by simp [isG]) trivial
  · rintro (m | t | d | q) s
    · exact cb_bind_pure (cb_query (c := isG) (Sum.inl m))
    · exact cb_bind_pure (cb_query (c := isG) (Sum.inr (Sum.inl t)))
    · simp only [lazyImplR, StateT.run_bind, StateT.run_get, pure_bind]
      cases List.lookup d s with
      | some v => exact cb_mono (n := 0) (by simp [isG]) trivial
      | none =>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        refine cb_mono (n := 0) (by simp [isG])
          (cb_bind_pure (g := fun p : V × List (D × V) ↦ (p.1, (d, p.1) :: s)) ?_)
        exact cb_bind_pure (cb_query (c := isG) (Sum.inr (Sum.inr (Sum.inl ()))))
    · exact cb_bind_pure (cb_query (c := isG) (Sum.inr (Sum.inr (Sum.inr q))))

end Chain3

section Supp
open KeyedHash
variable {W : Type} [Fintype W] {K X : Type} [Fintype K] [DecidableEq K] [SampleableType K]
  [Nonempty K] {s : ℕ} {α : Type}

lemma cb_congr {ι : Type} {sp : OracleSpec ι} {c c' : ι → Prop} [DecidablePred c]
    [DecidablePred c'] (h : ∀ t, c t ↔ c' t) {P : OracleComp sp α} :
    ∀ {n : ℕ}, CountBound c P n → CountBound c' P n := by
  induction P using OracleComp.inductionOn with
  | pure a => intro _ _; trivial
  | query_bind t k ih =>
    intro n hP
    change (if c t then 0 < n ∧ ∀ r, CountBound c (k r) (n - 1) else
      ∀ r, CountBound c (k r) n) at hP
    change (if c' t then 0 < n ∧ ∀ r, CountBound c' (k r) (n - 1) else
      ∀ r, CountBound c' (k r) n)
    by_cases ht : c t
    · rw [if_pos ht] at hP; rw [if_pos ((h t).1 ht)]
      exact ⟨hP.1, fun r ↦ ih r (hP.2 r)⟩
    · rw [if_neg ht] at hP; rw [if_neg fun h' ↦ ht ((h t).2 h')]
      exact fun r ↦ ih r (hP r)

theorem cb_isT {Q : QOC W (unifSpec + ITSRTargetSpec X K) α} {n : ℕ}
    (h : CountBound (QC W isR) Q n) : CountBound (isT (W := W) (X := X)) Q n :=
  cb_congr (fun t ↦ by rcases t with _ | _ | _ <;> simp [QC, isR, isT]) h

theorem close_rndImpl_supp (Rs : Fin s → K) (P : X → Prop) (goodC : α → Prop)
    (Q : QOC W (unifSpec + ITSRTargetSpec X K) α) :
    ∀ (n : ℕ) (t : List X), AllQueries (QG W (Gfin P)) goodC Q →
      CountBound (QC W isR) Q n →
      AllQueries (fun _ ↦ True)
        (fun z : α × List X ↦ goodC z.1 ∧ z.2.length ≤ t.length + n ∧ ∀ y ∈ z.2, y ∈ t ∨ P y)
        (close (rndImpl Rs) Q t) := by
  induction Q using OracleComp.inductionOn with
  | pure a =>
    intro n t hA _
    exact ⟨hA, by simp, fun y hy ↦ Or.inl hy⟩
  | query_bind q k ih =>
    intro n t hA hc
    rcases q with j | m | x
    · have hc' : ∀ r, CountBound (QC W isR) (k r) n := hc
      rw [close_instr_bind]
      exact ⟨trivial, fun i ↦ ih i n t (hA.2 i) (hc' i)⟩
    · have hc' : ∀ r, CountBound (QC W isR) (k r) n := hc
      rw [close_unif_bind _ (forwardsUnif_rndImpl Rs)]
      exact ⟨trivial, fun i ↦ ih i n t (hA.2 i) (hc' i)⟩
    · have hc' : 0 < n ∧ ∀ r, CountBound (QC W isR) (k r) (n - 1) := hc
      have hx : P x := hA.1
      rw [close_query_bind, rndImpl_run_tgt]
      simp only [liftU_pure, pure_bind]
      refine allQ_mono (fun _ h ↦ h) (fun z hz ↦ ⟨hz.1, ?_, fun y hy ↦ ?_⟩)
        (ih _ (n - 1) (t ++ [x]) (hA.2 _) (hc'.2 _))
      · have := hz.2.1
        simp at this
        omega
      · rcases hz.2.2 y hy with h | h
        · rcases List.mem_append.1 h with h | h
          · exact Or.inl h
          · rw [List.mem_singleton.1 h]; exact Or.inr hx
        · exact Or.inr h

theorem qWeight_mono_allQ {g : InstrIdx W ⊕ ℕ → Prop} {P : α → Prop}
    {E E' : α → Prop} [DecidablePred E] [DecidablePred E'] {X' : Closed W α}
    (hX : AllQueries g P X') (h : ∀ a, P a → E a → E' a) :
    ∀ ρ, qWeight E X' ρ ≤ qWeight E' X' ρ := by
  induction X' using OracleComp.inductionOn with
  | pure a =>
    intro ρ
    simp only [qWeight_pure]
    by_cases hE : E a
    · rw [ite_eq_left hE, ite_eq_left (h a hX hE)]
    · rw [ite_eq_right hE]; exact zero_le
  | query_bind q k ih =>
    intro ρ
    rcases q with j | n
    · rw [qWeight_instr_bind, qWeight_instr_bind]
      exact Finset.sum_le_sum fun i _ ↦ ih i (hX.2 i) _
    · rw [qWeight_unif_bind, qWeight_unif_bind]
      exact mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ ↦ ih i (hX.2 i) _)

end Supp

section Win
open KeyedHash
variable (c : Caps)

/-- A message truncated to the cap. -/
def cutB (m : List Byte) : BList Byte c.ml := BList.ofList (m.take c.ml) (by simp)

/-- An ITSR input read within the cap. -/
def tg (x : BN × BN × List Byte) : ItsrXm c := (x.1, x.2.1, cutB c x.2.2)

theorem cutB_of (m : List Byte) (h : m.length ≤ c.ml) : cutB c m = BList.ofList m h := by
  unfold cutB
  have : m.take c.ml = m := List.take_of_length_le h
  simp only [this]

theorem tg_inj (x y : BN × BN × List Byte) (hx : x.2.2.length ≤ c.ml) (hy : y.2.2.length ≤ c.ml)
    (h : tg c x = tg c y) : x = y := by
  obtain ⟨a, b, m⟩ := x
  obtain ⟨a', b', m'⟩ := y
  simp only [tg, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  rw [cutB_of c m hx, cutB_of c m' hy] at h
  have := congrArg (fun z : BList Byte c.ml ↦ List.ofFn z.2) h
  simp only [BList.ofFn_ofList] at this
  rw [this]

theorem hash_withHmsg (ω₀ : Ω128 c) (Hf : BN × ItsrXm c → BM) (R : BN) (x : BN × BN × List Byte)
    (hx : x.2.2.length ≤ c.ml) :
    (itsrProblem Link.vp (primsΩ (ω₀.withHmsg (hmsgTable c Hf)))).khf.hash R x = Hf (R, tg c x) := by
  obtain ⟨pk, root, m⟩ := x
  simp only at hx
  show (if h : m.length ≤ c.ml then _ else _) = _
  rw [dif_pos hx]
  simp only [tg, cutB_of c m hx]
  rfl

theorem mem_pairs {s : ℕ} (Rs : Fin s → BN) (t : List (BN × BN × List Byte)) (e : BN × (BN × BN × List Byte)) :
    e ∈ pairs Rs 0 t ↔ ∃ (j : ℕ) (h : j < t.length), (rndAt Rs j, t[j]) = e := by
  unfold pairs
  rw [List.mem_mapIdx]
  simp

set_option maxRecDepth 100000 in
theorem win_conv (ω₀ : Ω128 c) (Hf : BN × ItsrXm c → BM) {s : ℕ} (Rs : Fin s → BN)
    (cand : BN × (BN × BN × List Byte)) (t : List (BN × BN × List Byte))
    (hcand : cand.2.2.2.length ≤ c.ml) (ht : ∀ y ∈ t, y.2.2.length ≤ c.ml) (hlen : t.length ≤ s)
    (hw : (itsrProblem Link.vp (primsΩ (ω₀.withHmsg (hmsgTable c Hf)))).Wins (pairs Rs 0 t) cand) :
    itsrAWin idxCov Rs Hf (⟨QReg.of Unit, ((cand.1, tg c cand.2), t.map (tg c))⟩ :
      Σ _ : QReg, (BN × ItsrXm c) × List (ItsrXm c)) := by
  classical
  set prob := itsrProblem Link.vp (primsΩ (ω₀.withHmsg (hmsgTable c Hf))) with hprob
  obtain ⟨hnot, hcov⟩ := hw
  have hidx : ∀ (R : BN) (x : BN × BN × List Byte), x.2.2.length ≤ c.ml →
      prob.indexSet (R, x) = idxOf (Hf (R, tg c x)) := fun R x hx ↦ by
    show prob.indices (prob.khf.hash R x) = _
    rw [hash_withHmsg c ω₀ Hf R x hx]
    rfl
  refine ⟨fun hmem ↦ hnot ?_, fun i hi ↦ ?_⟩
  · have hmem' : isTgt Rs (t.map (tg c)) (cand.1, tg c cand.2) := by
      unfold itsrATargets at hmem
      exact (Finset.mem_filter.1 hmem).2
    obtain ⟨j, hj, hj'⟩ := hmem'
    simp only [List.getElem?_map] at hj'
    obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hj'
    have hjl : j.1 < t.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hy
      cases hy
    have hyt : t[j.1] = y := by
      rw [List.getElem?_eq_getElem hjl] at hy
      exact Option.some.inj hy
    have hyc : y = cand.2 := tg_inj c y cand.2 (ht y (hyt ▸ List.getElem_mem hjl)) hcand hyx
    refine (mem_pairs Rs t cand).2 ⟨j.1, hjl, ?_⟩
    rw [rndAt_lt Rs j.1 j.2, hyt, hyc]
    exact Prod.ext hj rfl
  · have hi' : i ∈ prob.indexSet cand := by rw [hidx cand.1 cand.2 hcand]; exact hi
    obtain ⟨e, he, hie⟩ := List.mem_flatMap.1 (hcov i hi')
    obtain ⟨j, hj, rfl⟩ := (mem_pairs Rs t e).1 he
    have hjs : j < s := lt_of_lt_of_le hj hlen
    have htg : (Rs ⟨j, hjs⟩, tg c t[j]) ∈ itsrATargets Rs (t.map (tg c)) := by
      unfold itsrATargets
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨⟨j, hjs⟩, rfl, ?_⟩⟩
      simp [List.getElem?_map, List.getElem?_eq_getElem hj]
    refine ⟨Hf (Rs ⟨j, hjs⟩, tg c t[j]), Finset.mem_image.2 ⟨_, htg, rfl⟩, ?_⟩
    · rw [hidx _ _ (ht _ (List.getElem_mem hj)), rndAt_lt Rs j hjs] at hie
      exact hie

end Win

section Final
open KeyedHash

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- The embedding of the `H_msg` table domain into the port domain. -/
def ιH : BN × ItsrXm c → EncX c := fun z ↦ .inr (.inl (z.1, z.2.1, z.2.2.1, z.2.2.2))

theorem ιH_injective : Function.Injective (ιH c) := by
  rintro ⟨a, b, d, e⟩ ⟨a', b', d', e'⟩ h
  simp only [ιH, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- The candidate read within the cap. -/
noncomputable def ocO : Option (BN × (BN × BN × List Byte)) → BN × ItsrXm c
  | some z => (z.1, tg c z.2)
  | none => Classical.arbitrary _

theorem encΩ_withHmsg_local (ω₀ : Ω128 c) (H G : BN × ItsrXm c → BM) (z : EncX c)
    (h : encΩ (ω₀.withHmsg (hmsgTable c H)) z ≠ encΩ (ω₀.withHmsg (hmsgTable c G)) z) :
    ∃ w, ιH c w = z ∧ H w ≠ G w := by
  rcases z with x | x | x | x
  · exact absurd rfl h
  · refine ⟨(x.1, x.2.1, x.2.2.1, x.2.2.2), rfl, fun he ↦ h ?_⟩
    change (0, H (x.1, x.2.1, x.2.2.1, x.2.2.2)) = (0, G (x.1, x.2.1, x.2.2.1, x.2.2.2))
    rw [he]
  · exact absurd rfl h
  · exact absurd rfl h

theorem supp_qbItsrL (qs : ℕ) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (ω : Ω128 c) :
    AllQueries (QG (WS (EncX c) EncY E) (Gfin (Ptgt (primsΩ ω) c.ml)))
        (fun r : BN × ItsrIn (primsΩ ω) ↦ r.2.2.2.length ≤ c.ml)
        (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) ∧
      CountBound (QC (WS (EncX c) EncY E) isR)
        (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) qs := by
  have hQ : ∀ pk, AllQueries (QG (WS (EncX c) EncY E) (Gint c.ml))
      (fun z : List Byte × _ ↦ z.1.length ≤ c.ml)
      ((internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).main pk) := fun pk ↦
    allQ_and (allQ_qPureBytesToInternal c.ml _
        (fun pkb ↦ allQ_compileQ c (encΩ ω) (F.main pkb) (hcap pkb)) pk)
      (out_qPureBytesToInternal _ c.ml
        (fun pkb ↦ allQ_out_simulateQ (compileImplQ (encΩ ω)) (hcap pkb)) pk)
  have hO := allQ_qItsrOpen (primsΩ ω) c.ml _ hQ
  refine ⟨allQ_and (allQ_qLazyRun _ (Ptgt (primsΩ ω) c.ml) _
      (allQ_mono (fun _ h ↦ h) (fun _ _ ↦ trivial) hO)) (out_qLazyRun _ _ hO), ?_⟩
  exact cb_qLazyRun _ _ (cb_qItsrOpen (primsΩ ω) _ fun pk ↦
    cb_qPureBytesToInternal _ (fun pkb ↦ cb_compileQ (encΩ ω) (F.main pkb) (hqs pkb)) pk)

/-- ITSR inputs `(PK.seed, PK.root, M)` of SLH-DSA-SHA2-128s. -/
abbrev ItsrInB : Type := BN × BN × List Byte

/-- **The ITSR term**, from an interactive adversary over the PORT oracle (machine side,
`hPort`) and the forger hypotheses `hqs`, `hcap`. -/
theorem itsr_term_port (q' qs : ℕ)
    (hPort : ∀ ω₀ : Ω128 c, ∃ (L : LocalSig.{1, 0}) (A : QReg) (I : L.Interp) (ρ : SubState A)
      (x : IAdv L (qromSpec (EncX c) EncY) ItsrInB BN (fun _ ↦ Option (BN × ItsrInB)) qs A),
      IAdv.IsQueryBound qs x (fun _ ↦ q') ∧
      ∀ (Hm : BN → BN → BN → BList Byte c.ml → BM) (Rs : Fin qs → BN)
        (Ev : Option (BN × ItsrInB) × List ItsrInB → Prop) [DecidablePred Ev],
        qprob I (encΩ (ω₀.withHmsg Hm))
            (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (EncX c) EncY)) qs [] x)
            ρ (fun p ↦ Ev p.2) =
          qWeight (fun z ↦ Ev (some z.1, z.2))
            (close (rndImpl (X := ItsrInB) Rs) (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              (ω₀.withHmsg Hm))) []) F.ρ₀)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    avΩ c (fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω))
      (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) ≤ epsItsr Link.vp.params q' qs := by
  classical
  rw [avΩ_resample_hmsg c]
  refine (avΩ_mono c fun ω₀ ↦ ?_).trans (le_of_eq (avΩ_const c _))
  obtain ⟨L, A, I, ρ, x, hx, hEq⟩ := hPort ω₀
  let Ev : (Fin qs → BN) → (BN × ItsrXm c → BM) →
      Option (BN × (BN × BN × List Byte)) × List (BN × BN × List Byte) → Prop :=
    fun Rs Hf ot ↦ itsrAWin idxCov Rs Hf (⟨QReg.of Unit, (ocO c ot.1, ot.2.map (tg c))⟩ :
      Σ _ : QReg, (BN × ItsrXm c) × List (ItsrXm c))
  have key : ∀ Hf : BN × ItsrXm c → BM,
      qItsrAdvantage (itsrProblem Link.vp (primsΩ (ω₀.withHmsg (hmsgTable c Hf))))
        (qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F (ω₀.withHmsg (hmsgTable c Hf))))
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F (ω₀.withHmsg (hmsgTable c Hf))).ρ₀ ≤
      avg fun Rs : Fin qs → BN ↦ qprob I (encΩ (ω₀.withHmsg (hmsgTable c Hf)))
        (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (EncX c) EncY)) qs [] x) ρ
        (fun p ↦ Ev Rs Hf p.2) := by
    intro Hf
    obtain ⟨hA, hC⟩ := supp_qbItsrL c optRand₀ pkSeedDist₀ F qs hqs hcap
      (ω₀.withHmsg (hmsgTable c Hf))
    unfold qItsrAdvantage
    rw [presample (s := qs) (itsrProblem Link.vp (primsΩ (ω₀.withHmsg (hmsgTable c Hf)))) rfl _ _ qs [] []
      (cb_isT hC) (by simp) _]
    refine avg_mono fun Rs ↦ ?_
    rw [hEq (hmsgTable c Hf) Rs (Ev Rs Hf)]
    refine qWeight_mono_allQ (close_rndImpl_supp Rs _ _ _ qs [] hA hC) (fun z hz hw ↦ ?_) _
    simp only [List.length_nil, List.drop_zero, List.nil_append, Nat.zero_add] at hw hz
    exact win_conv c ω₀ Hf Rs z.1 z.2 hz.1
      (fun y hy ↦ (hz.2.2 y hy).resolve_left (List.not_mem_nil)) hz.2.1 hw
  calc _ ≤ ∑ Hf : BN × ItsrXm c → BM, (Fintype.card (BN × ItsrXm c → BM) : ℝ≥0∞)⁻¹ *
          avg (fun Rs : Fin qs → BN ↦ qprob I (encΩ (ω₀.withHmsg (hmsgTable c Hf)))
            (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (EncX c) EncY)) qs [] x)
            ρ (fun p ↦ Ev Rs Hf p.2)) :=
        Finset.sum_le_sum fun Hf _ ↦ mul_le_mul' le_rfl (key Hf)
    _ = Pull.itsrPExp (fun H ↦ encΩ (ω₀.withHmsg (hmsgTable c H))) (tg c) (fun _ ↦ ocO c)
          I ρ qs x idxCov := by
        unfold Pull.itsrPExp avg
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun Rs _ ↦ Finset.sum_congr rfl fun Hf _ ↦ ?_
        rw [show (fun p ↦ Ev Rs Hf p.2) = (fun p ↦ itsrAWin idxCov Rs Hf
          (Pull.lv (tg c) (fun _ ↦ ocO c) p)) from rfl]
        ring
    _ ≤ _ := Pull.itsrP_adaptive_le (ιH_injective c) (encΩ_withHmsg_local c ω₀) idxCov_mono hx
    _ ≤ _ := itsr_bound_le q' qs

end Final
end Reduction.QItsr

#print axioms Reduction.QItsr.itsr_term_port

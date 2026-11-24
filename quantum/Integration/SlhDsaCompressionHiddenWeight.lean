import Integration.SlhDsaCompressionWotsReduction
import Ideal.Core.HiddenPrefix

namespace Reduction.Compression.HiddenWeight
open Ideal Ideal.HP OracleComp OracleSpec PQ.Interactive ENNReal

noncomputable def mean {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, prob p (· = x) * f x

theorem mean_pure {α : Type} (x : α) (f : α → ℝ≥0∞) : mean (pure x) f = f x := by
  classical
  simp only [mean,prob_pure,ite_mul,one_mul,zero_mul,@eq_comm _ x,tsum_ite_eq]

theorem mean_bind {α β : Type} (p : ProbComp α) (k : α → ProbComp β) (f : β → ℝ≥0∞) :
    mean (p >>= k) f = mean p (fun x => mean (k x) f) := by
  unfold mean
  simp only [wq_prob_bind_tsum,← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_right,mul_assoc]
  exact tsum_comm

theorem mean_add {α : Type} (p : ProbComp α) (f g : α → ℝ≥0∞) :
    mean p (fun x => f x + g x) = mean p f + mean p g := by simp only [mean,mul_add,tsum_add]

theorem mean_mono {α : Type} (p : ProbComp α) {f g : α → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    mean p f ≤ mean p g := tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)

theorem mean_one {α : Type} (p : ProbComp α) {f : α → ℝ≥0∞} (h : ∀ x, f x ≤ 1) : mean p f ≤ 1 := by
  have hh := mean_mono p h
  exact hh.trans (by simpa only [mean,mul_one] using tsum_prob_eq_le_one p)

theorem flag {α : Type} (p : ProbComp α) (f : α → Bool) :
    prT (p >>= fun x => pure (f x)) = mean p (fun x => if f x then 1 else 0) := by
  change prob _ (· = true) = _
  rw [wq_prob_bind_tsum]
  simp only [mean,prob_pure]

/-- Before the continuation starts, it is enough to couple the classical
transcript. The continuation may be any quantum Born weight bounded by one. -/
theorem trace_le {α ι : Type} {sp : OracleSpec ι} (a₁ a₂ : (i : ι) → sp.Range i)
    (bad : ι → Bool) (hag : ∀ i, bad i = false → a₁ i = a₂ i)
    (P : OracleComp (unifSpec + sp) α) (w : α → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) (l : List ι) :
    mean (simulateQ (ansImpl a₁) P) w ≤ mean (simulateQ (ansImpl a₂) P) w +
      prT ((simulateQ (trImpl a₂) P).run l >>= fun z => pure (z.2.any bad)) := by
  induction P using OracleComp.inductionOn generalizing l with
  | pure x =>
    simp only [simulateQ_pure,mean_pure]
    exact le_self_add
  | query_bind t k ih =>
    rcases t with n|i
    · rw [simulateQ_ansImpl_inl_bind,simulateQ_ansImpl_inl_bind,run_stImpl_inl_bind,bind_assoc,mean_bind,mean_bind]
      change _ ≤ _ + prob _ (· = true)
      rw [wq_prob_bind_tsum]
      exact (mean_mono _ (fun x => ih x l)).trans_eq (mean_add ..)
    · rw [simulateQ_ansImpl_inr_bind,simulateQ_ansImpl_inr_bind,run_stImpl_inr_bind]
      cases hb : bad i with
      | false => rw [hag i hb]; exact ih _ _
      | true =>
        have hit : prT ((simulateQ (trImpl a₂) (k (a₂ i))).run (l ++ [i]) >>= fun z => pure (z.2.any bad)) = 1 := by
          apply prT_eq_one_of_support
          intro b hb'
          rw [mem_support_bind_iff] at hb'
          obtain ⟨z,hz,hb'⟩ := hb'
          simp only [support_pure,Set.mem_singleton_iff] at hb'
          have inv := run_stImpl_inv a₂ (fun t l => l ++ [t]) (fun l => l.any bad = true)
            (fun t s hs => by simp [hs]) (k (a₂ i)) (l ++ [i]) (by simp [hb]) z hz
          rw [hb',inv]
        rw [hit]
        exact (mean_one _ hw).trans le_add_self

theorem mean_switch {α β : Type} (p : ProbComp α) (q : ProbComp β) (f : α → β → ℝ≥0∞) :
    mean p (fun a => mean q (f a)) = mean q (fun b => mean p (fun a => f a b)) := by
  simp only [mean,← ENNReal.tsum_mul_left]
  rw [tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => mul_left_comm ..

theorem mean_gstar {St Blk : Type} [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype Blk]
    [SampleableType (CF St Blk)] (IV : St) (b : Blk) (f : CF St Blk → ℝ≥0∞) :
    mean ($ᵗ (CF St Blk)) f = mean ($ᵗ St) (fun cv =>
      mean ($ᵗ (CF St Blk)) (fun g => mean ($ᵗ (Blk → St)) (fun T => f (gstar IV b cv g T)))) := by
  classical
  let : MeasurableSpace (CF St Blk) := ⊤
  let q : ProbComp (CF St Blk) := do
    let cv ← $ᵗ St
    let g ← $ᵗ (CF St Blk)
    let T ← $ᵗ (Blk → St)
    pure (gstar IV b cv g T)
  have he : 𝒟[($ᵗ (CF St Blk) : ProbComp _)] = 𝒟[q] := by
    simpa only [bind_pure] using evalDist_gstar IV b (fun g : CF St Blk => pure g)
  have h : mean ($ᵗ (CF St Blk)) f = mean q f := by
    apply tsum_congr
    intro g
    apply congrArg (· * f g)
    unfold prob
    rw [prEvent_eq_evalDist_of_discrete,prEvent_eq_evalDist_of_discrete,he]
  simpa only [q,mean_bind,mean_pure] using h

variable {St Blk PkSeed σ : Type} [DecidableEq St] [DecidableEq Blk]
variable (IV : St) (sb : PkSeed → Blk)
variable (P : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)

private theorem paired (seed : PkSeed) (cv : St) (g : CF St Blk) (T : Blk → St)
    (w : σ → ℝ≥0∞) (hw : ∀ x, w x ≤ 1) :
    mean (simulateQ (ans₁ (gstar IV (sb seed) cv g T)
      (keyedChain IV sb (gstar IV (sb seed) cv g T) seed)) P) w ≤
    mean (simulateQ (ans₁ g (chainI g T)) P) w +
      prT ((simulateQ (trImpl (pairAns g (chainI g T))) P).run [] >>= fun z =>
        pure (decide (cv = IV) || z.2.any (badQ IV (sb seed) cv g T))) := by
  by_cases hcv : cv = IV
  · have hit : prT ((simulateQ (trImpl (pairAns g (chainI g T))) P).run [] >>= fun z =>
        pure (decide (cv = IV) || z.2.any (badQ IV (sb seed) cv g T))) = 1 := by
      apply prT_eq_one_of_support
      intro b hb
      rw [mem_support_bind_iff] at hb
      obtain ⟨_,_,hb⟩ := hb
      simpa [hcv] using hb
    rw [hit]
    exact (mean_one _ hw).trans le_add_self
  · simpa only [ans₁_eq,hcv,decide_false,Bool.false_or] using trace_le
      (pairAns (gstar IV (sb seed) cv g T) (keyedChain IV sb (gstar IV (sb seed) cv g T) seed))
      (pairAns g (chainI g T)) _ (fun t ht => pairAns_gstar_eq IV sb seed cv hcv g T t ht) P w hw []

theorem prT_mean {α : Type} (p : ProbComp α) (k : α → ProbComp Bool) :
    prT (p >>= k) = mean p (fun x => prT (k x)) := wq_prob_bind_tsum p k _

variable [Fintype St] [SampleableType St] [Fintype Blk] [SampleableType (CF St Blk)]

set_option maxHeartbeats 800000 in
/-- Open the chaining state's first row for the choosing phase while keeping
the actual table in every measured continuation. The error charges classical
queries made in the choosing phase. -/
theorem hiddenPrefix (seeds : ProbComp PkSeed) (hsb : Function.Injective sb)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← seeds}[s' = s] ≤ γ)
    (q C L : ℕ) (hq : IsQueryBoundP P (fun i => isPub i = true) q)
    (hC : IsQueryBoundP P (fun i => isChain i = true) C) (hL : AllQueriesSatisfy P (chainLenLe L))
    (w : PkSeed → CF St Blk → σ → ℝ≥0∞) (hw : ∀ s g x, w s g x ≤ 1) :
    mean seeds (fun s => mean ($ᵗ (CF St Blk)) fun g =>
      mean (simulateQ (ans₁ g (keyedChain IV sb g s)) P) (w s g)) ≤
    mean seeds (fun s => mean ($ᵗ St) fun cv => mean ($ᵗ (CF St Blk)) fun g => mean ($ᵗ (Blk → St)) fun T =>
      mean (simulateQ (ans₁ g (chainI g T)) P) (w s (gstar IV (sb s) cv g T))) +
        (q*γ + (2*q+C*(1+2*L)+1:ℕ)*(Fintype.card St:ℝ≥0∞)⁻¹) := by
  classical
  let draws : ProbComp (PkSeed × St × CF St Blk × (Blk → St)) := do
    let s ← seeds
    let cv ← $ᵗ St
    let g ← $ᵗ (CF St Blk)
    let T ← $ᵗ (Blk → St)
    pure (s,cv,g,T)
  let good := fun (z : PkSeed × St × CF St Blk × (Blk → St)) =>
    mean (simulateQ (ans₁ z.2.2.1 (chainI z.2.2.1 z.2.2.2)) P)
      (w z.1 (gstar IV (sb z.1) z.2.1 z.2.2.1 z.2.2.2))
  let fail := fun (z : PkSeed × St × CF St Blk × (Blk → St)) =>
    prT ((simulateQ (trImpl (pairAns z.2.2.1 (chainI z.2.2.1 z.2.2.2))) P).run [] >>= fun r =>
      pure (decide (z.2.1 = IV) || r.2.any (badQ IV (sb z.1) z.2.1 z.2.2.1 z.2.2.2)))
  let random := fun (z : PkSeed × St × CF St Blk × (Blk → St)) =>
    let h := gstar IV (sb z.1) z.2.1 z.2.2.1 z.2.2.2
    mean (simulateQ (ans₁ h (keyedChain IV sb h z.1)) P) (w z.1 h)
  have comp : mean draws random ≤ mean draws good + mean draws fail :=
    (mean_mono (f := random) (g := fun z => good z + fail z) draws (fun z => paired IV sb P z.1 z.2.1 z.2.2.1 z.2.2.2 _ (fun x => hw _ _ x))).trans_eq (mean_add ..)
  have start : (mean seeds fun s => mean ($ᵗ (CF St Blk)) fun g =>
      mean (simulateQ (ans₁ g (keyedChain IV sb g s)) P) (w s g)) = mean draws random := by
    simp only [draws,random,mean_bind,mean_pure]
    exact congrArg (mean seeds) (funext (fun s => mean_gstar IV (sb s) _))
  have badEq : mean draws fail = prT (badGame IV sb seeds P) := by
    let initial : ProbComp (PkSeed × St) := do
      let s ← seeds
      let cv ← $ᵗ St
      pure (s,cv)
    let traces := do
      let g ← $ᵗ (CF St Blk)
      let T ← $ᵗ (Blk → St)
      let r ← (simulateQ (trImpl (pairAns g (chainI g T))) P).run []
      pure (g,T,r)
    let mark := fun (a : PkSeed × St) (b : CF St Blk × (Blk → St) × σ × List ((St × Blk) ⊕ (Blk × List Blk))) =>
      decide (a.2 = IV) || b.2.2.2.any (badQ IV (sb a.1) a.2 b.1 b.2.1)
    have e := mean_switch initial traces (fun a b => if mark a b then (1:ℝ≥0∞) else 0)
    simpa only [initial,traces,draws,fail,badGame,mark,mean_bind,mean_pure,prT_mean,prT_pure] using e
  rw [start]
  refine comp.trans (add_le_add ?_ (badEq.le.trans (prT_badGame_le IV sb hsb seeds γ hγ P q C L hq hC hL)))
  simp only [draws,good,mean_bind,mean_pure,le_rfl]

end Reduction.Compression.HiddenWeight
#print axioms Reduction.Compression.HiddenWeight.trace_le
#print axioms Reduction.Compression.HiddenWeight.hiddenPrefix

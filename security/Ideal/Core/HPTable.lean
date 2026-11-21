import Ideal.Core.HPBasic
import VCVio.EvalDist.Monad.UniformTable

/-!
# Tables for the hidden-prefix hop

* `gstar`: the public table with the cell `(IV, sb seed)` overridden by `cv` and the row `cv`
  overridden by the private row table; `evalDist_gstar`: it is uniform.
* `idealEager`: the ideal game with eagerly sampled tables; `evalDist_idealGame`.
-/

open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory

namespace Ideal.HP

variable {St Blk : Type}

/-- The joint table over the public table and the private row table. -/
def tbl (g : CF St Blk) (T : Blk → St) : (t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t
  | .inl q => g q
  | .inr B => T B

/-- Answer function of phase one from a public and a chain answer function. -/
def pairAns (pub : CF St Blk) (chain : Blk × List Blk → St) :
    (t : (St × Blk) ⊕ (Blk × List Blk)) → (hS St Blk + chainS St Blk).Range t
  | .inl q => pub q
  | .inr q => chain q

theorem ans₁_eq (pub : CF St Blk) (chain : Blk × List Blk → St) :
    ans₁ pub chain = ansImpl (pairAns pub chain) := by
  unfold ans₁ ansImpl pairAns
  rfl

/-- The ideal chain answer: private row at the first block, then the public table. -/
def chainI (g : CF St Blk) (T : Blk → St) (q : Blk × List Blk) : St := mdFold g (T q.1) q.2

/-- The table of phase two of the ideal game. -/
def gstar [DecidableEq St] [DecidableEq Blk] (IV : St) (sbs : Blk) (cv : St) (g : CF St Blk)
    (T : Blk → St) : CF St Blk :=
  fun q => if q = (IV, sbs) then cv else if q.1 = cv then T q.2 else g q

/-- Replace row `c₀` of `g` by `T`. -/
def rowRep [DecidableEq St] (g : CF St Blk) (c₀ : St) (T : Blk → St) : CF St Blk :=
  fun q => if q.1 = c₀ then T q.2 else g q

theorem gstar_eq_update [DecidableEq St] [DecidableEq Blk] (IV : St) (sbs : Blk) (cv : St)
    (g : CF St Blk) (T : Blk → St) :
    gstar IV sbs cv g T = Function.update (rowRep g cv T) (IV, sbs) cv := by
  funext q
  by_cases hq : q = (IV, sbs)
  · subst hq; simp [gstar]
  · simp [gstar, rowRep, hq]

/-! ## Uniformity -/

section Uniform

variable {T V α : Type} [MeasurableSpace α]

/-- Bijective re-randomisation of an independent uniform pair. -/
theorem evalDist_uniform_pair_bijective [Finite T] [Nonempty T] [Finite V] [Nonempty V]
    (value : ProbComp V) (table : ProbComp T)
    (hvalue : ∀ [MeasurableSpace V] [MeasurableSingletonClass V], 𝒟[value] = uniformOn Set.univ)
    (htable : ∀ [MeasurableSpace T] [MeasurableSingletonClass T], 𝒟[table] = uniformOn Set.univ)
    (σ : V × T → V × T) (hσ : Function.Bijective σ) (f : V × T → ProbComp α) :
    𝒟[value >>= fun u => table >>= fun g => f (σ (u, g))] =
      𝒟[value >>= fun u => table >>= fun g => f (u, g)] := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSpace T := ⊤
  set pair : ProbComp (V × T) := Prod.mk <$> value <*> table with hpair
  have hunif : 𝒟[pair] = uniformOn Set.univ :=
    evalDist_seq_map_eq_uniformOn _ _ Prod.mk hvalue htable
      Measurable.of_discrete ⟨fun x y h => h, fun x => ⟨x, rfl⟩⟩
  have h1 : ∀ F : V × T → ProbComp α,
      (value >>= fun u => table >>= fun g => F (u, g)) = pair >>= F := fun F => by
    simp [hpair, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  rw [h1 fun p => f (σ p), h1 f]
  exact evalDist_bind_bijective_of_uniform pair hunif σ hσ f

end Uniform

/-- **The overridden table is uniform.** -/
theorem evalDist_gstar [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype Blk]
    [SampleableType (CF St Blk)] {α : Type} [MeasurableSpace α] (IV : St) (sbs : Blk)
    (f : CF St Blk → ProbComp α) :
    𝒟[$ᵗ (CF St Blk) >>= f] =
      𝒟[$ᵗ St >>= fun cv => $ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun T =>
        f (gstar IV sbs cv g T)] := by
  let : MeasurableSpace St := ⊤
  have hb := evalDist_bind_bind_update ($ᵗ St) ($ᵗ (CF St Blk))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample (IV, sbs) f
  rw [← hb]
  refine evalDist_bind_congr_of_support _ _ _ fun cv _ => ?_
  set h : CF St Blk → ProbComp α := fun g => f (Function.update g (IV, sbs) cv) with hh
  have h1 : 𝒟[$ᵗ (CF St Blk) >>= h] =
      𝒟[$ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun T => h g] :=
    evalDist_bind_congr_of_support _ _ _ fun g _ => (OracleComp.evalDist_bind_const _ _).symm
  rw [h1]
  set σ : CF St Blk × (Blk → St) → CF St Blk × (Blk → St) :=
    fun p => (rowRep p.1 cv p.2, fun B => p.1 (cv, B)) with hσ
  have hσinv : Function.Involutive σ := by
    rintro ⟨g, T⟩
    refine Prod.ext ?_ ?_
    · funext q
      by_cases hq : q.1 = cv
      · simp only [hσ, rowRep, hq, ite_true]
        rw [← hq]
      · simp [hσ, rowRep, hq]
    · funext B
      simp [hσ, rowRep]
  have key := evalDist_uniform_pair_bijective ($ᵗ (CF St Blk)) ($ᵗ (Blk → St))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample σ
    hσinv.bijective (fun p => h p.1)
  rw [← key]
  simp only [hσ, hh, gstar_eq_update]

/-! ## Evaluating the ideal handlers at a table -/

theorem simulateQ_ansImpl_foldlM (g : CF St Blk) (T : Blk → St) (bs : List Blk) (c : St) :
    simulateQ (ansImpl (tbl g T))
        (bs.foldlM (fun c b => (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b)))) c) =
      pure (mdFold g c bs) := by
  induction bs generalizing c with
  | nil => simp [mdFold]
  | cons b bs ih =>
    simp only [List.foldlM_cons, simulateQ_bind, simulateQ_spec_query, mdFold, List.foldl_cons]
    exact (pure_bind _ _).trans (ih _)

/-- Phase one of the ideal game at a fixed table. -/
theorem simulateQ_chainToT {α : Type} (g : CF St Blk) (T : Blk → St)
    (oa : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) α) :
    simulateQ (ansImpl (tbl g T)) (simulateQ chainToT oa) =
      simulateQ (ans₁ g (chainI g T)) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with n | q | q
  · exact simulateQ_spec_query _ _
  · exact simulateQ_spec_query _ _
  · simp only [chainToT, simulateQ_bind, simulateQ_spec_query]
    exact (pure_bind _ _).trans (simulateQ_ansImpl_foldlM g T _ _)

/-- Phase two of the ideal game at a fixed table. -/
theorem simulateQ_route [DecidableEq St] [DecidableEq Blk] {α : Type} (IV : St) (sbs : Blk)
    (cv : St) (g : CF St Blk) (T : Blk → St) (oa : OracleComp (unifSpec + hS St Blk) α) :
    simulateQ (ansImpl (tbl g T)) (simulateQ (route IV sbs cv) oa) =
      simulateQ (instImpl₀ (gstar IV sbs cv g T)) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with n | q
  · exact simulateQ_spec_query _ _
  · simp only [route]
    by_cases h1 : q = (IV, sbs)
    · subst h1
      simp only [ite_true, simulateQ_pure]
      show pure cv = pure (gstar IV sbs cv g T (IV, sbs))
      simp [gstar]
    · by_cases h2 : q.1 = cv
      · simp only [h1, h2, ite_true, ite_false]
        refine (simulateQ_spec_query _ _).trans ?_
        simp [instImpl₀, unifFwdAnswerImpl, gstar, h1, h2, tbl]
      · simp only [h1, h2, ite_false]
        refine (simulateQ_spec_query _ _).trans ?_
        simp [instImpl₀, unifFwdAnswerImpl, gstar, h1, h2, tbl]

theorem simulateQ_ansImpl_liftM {ι : Type} {spec : OracleSpec ι} {α : Type}
    (a : (t : ι) → spec.Range t) (oa : ProbComp α) :
    simulateQ (ansImpl a) (liftM oa : OracleComp (unifSpec + spec) α) = oa := by
  simp [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_left]

/-! ## The eager ideal game -/

/-- The ideal game with eagerly sampled public table and private row table. -/
noncomputable def idealEager [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype Blk]
    [SampleableType (CF St Blk)] {PkSeed σ : Type}
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) : ProbComp Bool := do
  let g ← $ᵗ (CF St Blk)
  let T ← $ᵗ (Blk → St)
  let x ← simulateQ (ans₁ g (chainI g T)) prog₁
  let seed ← seedGen
  let cv ← $ᵗ St
  simulateQ (instImpl₀ (gstar IV (sb seed) cv g T)) (P₂ seed x)

/-- The pair of tables as one dependent table. -/
def tblEquiv : CF St Blk × (Blk → St) ≃ ((t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t)
    where
  toFun p := tbl p.1 p.2
  invFun F := (fun q => F (.inl q), fun B => F (.inr B))
  left_inv p := rfl
  right_inv F := by funext t; rcases t with q | B <;> rfl

theorem evalDist_idealGame [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype Blk]
    [SampleableType (CF St Blk)] {PkSeed σ : Type}
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) :
    𝒟[idealGame IV sb seedGen prog₁ P₂] = 𝒟[idealEager IV sb seedGen prog₁ P₂] := by
  let : SampleableType ((t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t) :=
    SampleableType.ofEquiv tblEquiv
  unfold idealGame
  rw [OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable]
  have hdraw : ∀ k : ((t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t) → ProbComp Bool,
      ($ᵗ ((t : (St × Blk) ⊕ Blk) → (hS St Blk + tS St Blk).Range t) >>= k) =
        $ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun T => k (tbl g T) := by
    intro k
    change (tblEquiv <$> ((·, ·) <$> ($ᵗ (CF St Blk)) <*> ($ᵗ (Blk → St)))) >>= k = _
    simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
    rfl
  rw [hdraw]
  unfold idealEager
  refine congrArg _ (bind_congr fun g => bind_congr fun T => ?_)
  rw [OracleComp.completeTable_empty]
  simp only [idealProg, simulateQ_bind, simulateQ_chainToT, simulateQ_ansImpl_liftM,
    simulateQ_route]

end Ideal.HP

#print axioms Ideal.HP.evalDist_gstar
#print axioms Ideal.HP.evalDist_idealGame

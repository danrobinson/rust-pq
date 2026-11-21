import Ideal.Core.HPTable

/-!
# The hidden-prefix hop: real game ≤ eager ideal game + bad event

`badGame` is the eager ideal phase one with its trace of queries, followed by the draw of the
seed and of `cv`; it returns whether `cv = IV` or some traced query touches a hidden cell.
`prT_realGame_le`: `Pr[real] ≤ Pr[idealEager] + Pr[badGame]`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.HP

variable {St Blk PkSeed σ : Type} [DecidableEq St] [DecidableEq Blk]

/-- Some cell visited by the ideal continuation from `c` through `bs` is hidden. -/
def cellBad (IV : St) (sbs : Blk) (cv : St) (g : CF St Blk) : St → List Blk → Bool
  | _, [] => false
  | c, b :: bs => (decide ((c, b) = (IV, sbs)) || decide (c = cv)) ||
      cellBad IV sbs cv g (g (c, b)) bs

/-- A phase-one query touches a hidden cell. -/
def badQ (IV : St) (sbs : Blk) (cv : St) (g : CF St Blk) (T : Blk → St) :
    (St × Blk) ⊕ (Blk × List Blk) → Bool
  | .inl q => decide (q = (IV, sbs)) || decide (q.1 = cv)
  | .inr q => cellBad IV sbs cv g (T q.1) q.2

theorem mdFold_gstar (IV : St) (sbs : Blk) (cv : St) (g : CF St Blk) (T : Blk → St) (c : St)
    (bs : List Blk) (h : cellBad IV sbs cv g c bs = false) :
    mdFold (gstar IV sbs cv g T) c bs = mdFold g c bs := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih =>
    simp only [cellBad, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    have h1 : gstar IV sbs cv g T (c, b) = g (c, b) := by
      simp [gstar, h.1.1, h.1.2]
    simp only [mdFold, List.foldl_cons] at ih ⊢
    rw [h1]
    exact ih _ h.2

theorem pairAns_gstar_eq (IV : St) (sb : PkSeed → Blk) (seed : PkSeed) (cv : St) (hcv : cv ≠ IV)
    (g : CF St Blk) (T : Blk → St) (t : (St × Blk) ⊕ (Blk × List Blk))
    (ht : badQ IV (sb seed) cv g T t = false) :
    pairAns (gstar IV (sb seed) cv g T)
        (keyedChain IV sb (gstar IV (sb seed) cv g T) seed) t =
      pairAns g (chainI g T) t := by
  rcases t with q | q
  · simp only [badQ, Bool.or_eq_false_iff, decide_eq_false_iff_not] at ht
    simp [pairAns, gstar, ht.1, ht.2]
  · simp only [badQ] at ht
    simp only [pairAns, keyedChain, chainI]
    have h1 : gstar IV (sb seed) cv g T (IV, sb seed) = cv := by simp [gstar]
    have h2 : gstar IV (sb seed) cv g T (cv, q.1) = T q.1 := by
      simp [gstar, hcv]
    rw [h1, h2]
    exact mdFold_gstar IV (sb seed) cv g T _ _ ht

/-- The bad-event game. -/
noncomputable def badGame [SampleableType St] [Fintype Blk] [SampleableType (CF St Blk)]
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ) : ProbComp Bool := do
  let g ← $ᵗ (CF St Blk)
  let T ← $ᵗ (Blk → St)
  let z ← (simulateQ (trImpl (pairAns g (chainI g T))) prog₁).run []
  let seed ← seedGen
  let cv ← $ᵗ St
  pure (decide (cv = IV) || z.2.any (badQ IV (sb seed) cv g T))

theorem prT_real_pointwise (IV : St) (sb : PkSeed → Blk)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool)
    (seed : PkSeed) (cv : St) (g : CF St Blk) (T : Blk → St) :
    prT (simulateQ (ans₁ (gstar IV (sb seed) cv g T)
          (keyedChain IV sb (gstar IV (sb seed) cv g T) seed)) prog₁ >>= fun x =>
        simulateQ (instImpl₀ (gstar IV (sb seed) cv g T)) (P₂ seed x)) ≤
      prT (simulateQ (ans₁ g (chainI g T)) prog₁ >>= fun x =>
        simulateQ (instImpl₀ (gstar IV (sb seed) cv g T)) (P₂ seed x)) +
      prT ((simulateQ (trImpl (pairAns g (chainI g T))) prog₁).run [] >>= fun z =>
        pure (decide (cv = IV) || z.2.any (badQ IV (sb seed) cv g T))) := by
  by_cases hcv : cv = IV
  · have h1 : prT ((simulateQ (trImpl (pairAns g (chainI g T))) prog₁).run [] >>= fun z =>
        pure (decide (cv = IV) || z.2.any (badQ IV (sb seed) cv g T))) = 1 := by
      refine prT_eq_one_of_support _ fun b hb => ?_
      rw [mem_support_bind_iff] at hb
      obtain ⟨z, -, hb⟩ := hb
      simpa [hcv] using hb
    rw [h1]
    exact (prT_le_one _).trans le_add_self
  · have h := prT_simulateQ_le_add_trace
      (pairAns (gstar IV (sb seed) cv g T) (keyedChain IV sb (gstar IV (sb seed) cv g T) seed))
      (pairAns g (chainI g T)) (badQ IV (sb seed) cv g T)
      (fun t ht => pairAns_gstar_eq IV sb seed cv hcv g T t ht) prog₁
      (fun x => simulateQ (instImpl₀ (gstar IV (sb seed) cv g T)) (P₂ seed x)) []
    simpa only [ans₁_eq, hcv, decide_false, Bool.false_or] using h

theorem prT_realGame_le [SampleableType St] [Fintype Blk] [SampleableType (CF St Blk)]
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) :
    prT (realGame IV sb seedGen prog₁ P₂) ≤
      prT (idealEager IV sb seedGen prog₁ P₂) + prT (badGame IV sb seedGen prog₁) := by
  -- the real game with the seed first and the table replaced by `gstar`
  have h1 : prT (realGame IV sb seedGen prog₁ P₂) =
      prT (seedGen >>= fun seed => $ᵗ St >>= fun cv => $ᵗ (CF St Blk) >>= fun g =>
        $ᵗ (Blk → St) >>= fun T =>
          simulateQ (ans₁ (gstar IV (sb seed) cv g T)
            (keyedChain IV sb (gstar IV (sb seed) cv g T) seed)) prog₁ >>= fun x =>
          simulateQ (instImpl₀ (gstar IV (sb seed) cv g T)) (P₂ seed x)) := by
    unfold realGame
    rw [prT_swap]
    refine prT_bind_congr _ _ _ fun seed _ => prT_congr ?_
    exact evalDist_gstar IV (sb seed) fun g =>
      simulateQ (ans₁ g (keyedChain IV sb g seed)) prog₁ >>= fun x =>
        simulateQ (instImpl₀ g) (P₂ seed x)
  rw [h1]
  refine (prT_bind_le_add _ _ _ _ fun seed => prT_bind_le_add _ _ _ _ fun cv =>
    prT_bind_le_add _ _ _ _ fun g => prT_bind_le_add _ _ _ _ fun T =>
      prT_real_pointwise IV sb prog₁ P₂ seed cv g T).trans (le_of_eq ?_)
  congr 1
  · -- move the seed and `cv` after phase one
    unfold idealEager
    have e1 : ∀ K : PkSeed → St → CF St Blk → (Blk → St) → σ → ProbComp Bool,
        prT (seedGen >>= fun seed => $ᵗ St >>= fun cv => $ᵗ (CF St Blk) >>= fun g =>
          $ᵗ (Blk → St) >>= fun T => simulateQ (ans₁ g (chainI g T)) prog₁ >>= fun x =>
            K seed cv g T x) =
        prT ($ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun T =>
          simulateQ (ans₁ g (chainI g T)) prog₁ >>= fun x => seedGen >>= fun seed =>
            $ᵗ St >>= fun cv => K seed cv g T x) := by
      intro K
      have := prT_swap (seedGen >>= fun seed => $ᵗ St >>= fun cv => pure (seed, cv))
        ($ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun T =>
          simulateQ (ans₁ g (chainI g T)) prog₁ >>= fun x => pure (g, T, x))
        (fun a b => K a.1 a.2 b.1 b.2.1 b.2.2)
      simpa only [bind_assoc, pure_bind] using this
    exact e1 fun seed cv g T x => simulateQ (instImpl₀ (gstar IV (sb seed) cv g T)) (P₂ seed x)
  · unfold badGame
    have := prT_swap (seedGen >>= fun seed => $ᵗ St >>= fun cv => pure (seed, cv))
      ($ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun T =>
        (simulateQ (trImpl (pairAns g (chainI g T))) prog₁).run [] >>= fun z => pure (g, T, z))
      (fun a b => pure (decide (a.2 = IV) || b.2.2.2.any (badQ IV (sb a.1) a.2 b.1 b.2.1)))
    simpa only [bind_assoc, pure_bind] using this

end Ideal.HP

#print axioms Ideal.HP.prT_realGame_le

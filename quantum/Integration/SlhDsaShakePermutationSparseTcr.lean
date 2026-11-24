import Integration.SlhDsaShakePermutationSparseSelect
import Integration.SlhDsaShakePermutationSparseAverage

/-! Native arity-class SM-TCR in the two-way ideal permutation model.
The first phase is charged separately for its classical absorption steps.
The quantum second-phase row model charges three cells per public query. -/
namespace Reduction.ShakePermutation.SparsePort.ArityGame
open Classical MLink OracleSpec OracleComp SLHDSA TweakableHash PQ.Interactive PQ.QROM Quantum SetOracle ENNReal
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
variable (S : Sha2Set) (ar : ℕ) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E]
abbrev Work (E : Type) [Fintype E] [DecidableEq E] := WS Port Words E
abbrev Msg := Arity.Msg S ar
abbrev Row := Arity.Row S ar
abbrev Base := ShakeXof.Arity.base S ar seeds
variable (A : QSM_DT_TCR_Adversary (Work E) (Base S ar seeds))
variable (forge : (Port → Words) → A.State → S.Node → Closed (Work E) (ℕ × Msg S ar))

def actualGame (π : Permutation) := thashArityProblemT S.vp (primitives (lanes π) S.vp.params) seeds ar

def adversary (π : Permutation) : QSM_DT_TCR_Adversary (Work E) (actualGame S ar seeds π) where
  State := A.State
  choose := A.choose
  forge := forge (oracle π)
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private theorem qrun {D L V : Type} [Fintype V] (f : Bytes 32 → Words → Words)
    (sel : Select.Prog D) (post : D → Closed V L) (ρ : Matrix V V ℂ) (E' : L → Prop) [DecidablePred E'] :
    qWeight E' (liftU (simulateQ (Select.close f) sel) >>= post) ρ =
      Phase.run f (fun x => qWeight E' (post x) ρ) sel := by
  induction sel using OracleComp.inductionOn with
  | pure x => simp only [simulateQ_pure,liftU_pure,pure_bind]; rfl
  | query_bind i k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query]
    rcases i with n|⟨d,w⟩
    · change qWeight E' (liftU (liftM (unifSpec.query n) >>= _) >>= post) ρ = _
      rw [liftU_query_bind,bind_assoc,qWeight_unif_bind]
      change _ = uniformMean (fun x : Fin (n+1) => Phase.run f _ (k x))
      simp only [← ih,uniformMean,unifW,Fintype.card_fin,Nat.cast_add,Nat.cast_one,← Finset.mul_sum]
    · change qWeight E' (liftU (pure (f d w) >>= _) >>= post) ρ = _
      rw [pure_bind]
      exact ih _

def test (pk : S.Node) (H : Port → Words) (F : Row S ar → S.Node)
    (r : A.State × Select.History S ar) : ℝ≥0∞ :=
  qWeight (PQ.Interactive.tcrWin r.2.1 F) (forge H r.1 pk) A.ρ₀

private theorem check_win {σ : Type} (F : Row S ar → S.Node) (r : σ × Select.History S ar)
    (jm : ℕ × Msg S ar) :
    (match r.2.1[jm.1]? with
     | none => false
     | some tm => decide (jm.2 ≠ tm.2 ∧ F (tm.1,jm.2) = F tm)) = decide (PQ.Interactive.tcrWin r.2.1 F jm) := by
  cases h : r.2.1[jm.1]? <;> simp [PQ.Interactive.tcrWin,h]

private theorem normalized (pk : S.Node) (f : Bytes 32 → Words → Words) (H : Port → Words)
    (F : Row S ar → S.Node)  :
    qWeight (· = true)
      (liftU ((simulateQ (SM_DT_TCR_oracles (Select.game S ar seeds f) pk) A.choose).run ([], [])) >>= fun r =>
        forge H r.1 pk >>= fun jm =>
          match r.2.1[jm.1]? with
          | none => pure false
          | some tm => pure (decide (jm.2 ≠ tm.2 ∧ F (tm.1,jm.2) = F tm))) A.ρ₀ =
      Phase.run f (test S ar seeds A forge pk H F) (Select.prog S ar pk A.choose ([],[])) := by
  rw [Select.close_prog S ar seeds pk f A.choose ([],[]),qrun]
  apply congrArg (fun ev => Phase.run f ev _)
  funext r
  unfold test
  rw [← qWeight_bind_pure_decide (PQ.Interactive.tcrWin r.2.1 F) (forge H r.1 pk) A.ρ₀]
  apply congrArg (fun z : Closed (Work E) Bool => qWeight (· = true) z A.ρ₀)
  apply congrArg (fun g => forge H r.1 pk >>= g)
  funext jm
  rw [← check_win S ar F r jm]
  cases r.2.1[jm.1]? <;> rfl

private theorem shadow_leaf (pk : S.Node) (h : ar ≤ 2) (π : Permutation)
    (s : Row S ar → SkFormat.Suffix S) (F : Row S ar → S.Node) (d : Bytes 32) (m : Msg S ar) :
    Select.value S (shadow (SkFormat.split S) (Arity.input S ar pk h) π s Prod.fst F) pk d m.val = F (d,m) := by
  unfold Select.value
  let j : Row S ar := (d,m)
  rw [show ShakeXof.thBytes S pk d m.val = Arity.data S ar pk j from rfl,Arity.single _ _ _ _ h]
  simp only [List.foldl_cons,List.foldl_nil]
  have eq : join (rateXor (rateBlock (padded (sp (Arity.data S ar pk j))) 0) (rateOf 0)) (capOf 0) =
      Arity.input S ar pk h j := by
    apply congrArg₂ join _ rfl
    funext i
    exact UInt64.xor_zero
  rw [eq,shadow,ShakeXof.locate_emb]
  simp only [j,ite_true,target,Equiv.apply_symm_apply]

private theorem shadow_locality (pk : S.Node) (h : ar ≤ 2) (π : Permutation)
    (s : Row S ar → SkFormat.Suffix S) (F G : Row S ar → S.Node) (d : Bytes 32) (xs : List S.Node)
    (eq : ∀ m, F (d,m) = G (d,m)) :
    Select.value S (shadow (SkFormat.split S) (Arity.input S ar pk h) π s Prod.fst F) pk d xs =
      Select.value S (shadow (SkFormat.split S) (Arity.input S ar pk h) π s Prod.fst G) pk d xs := by
  have hh (j : Row S ar) (same : j.1 = d) : F j = G j := by rcases j with ⟨w,m⟩; change w = d at same; subst w; exact eq m
  simp only [Select.value,shadow_local _ _ _ _ Prod.fst F G d _ hh]

private theorem model (q : ℕ) (pk : S.Node) (st : A.State)
    (cost : PUE (spec := unifSpec) cnt0 (fun H => forge H st pk) q) :
    ∃ N : HybridModel Port Words (ℕ × Msg S ar) q, ∀ H (ev : ℕ × Msg S ar → Prop) [DecidablePred ev],
      N.prob H ev = qWeight ev (forge H st pk) A.ρ₀ := by
  classical
  obtain ⟨ρ,he⟩ := exists_subState (A := (Port × Words) × E) A.ρ₀ A.posSemidef A.trace_eq_one
  obtain ⟨N,hN⟩ := cost.exists_model ρ
  exact ⟨N,fun H ev _ => (hN H ev).trans (by rw [he])⟩

private theorem ideal_bound (pk : S.Node) (h : ar ≤ 2) (π : Permutation) (s : Row S ar → SkFormat.Suffix S)
    (base : Row S ar) (q : ℕ) (hq : ∀ st, PUE (spec := unifSpec) cnt0 (fun H => forge H st pk) q) :
    uniformMean (fun F : Row S ar → S.Node => Phase.ideal (SkFormat.split S) (Arity.input S ar pk h)
      base Prod.fst (Select.prog S ar pk A.choose ([],[])) (test S ar seeds A forge pk) π (F,s)) ≤
      (2*((3*q : ℕ):ℝ≥0∞)+1)^2/(Fintype.card S.Node : ℝ≥0∞) := by
  let : Nonempty (Msg S ar) := ⟨⟨List.replicate ar default,by simp⟩⟩
  let a := Arity.input S ar pk h
  let f (R : Row S ar → S.Node) := shadow (SkFormat.split S) a π s Prod.fst R
  let H (R : Row S ar → S.Node) := simulatedPort (SkFormat.split S) a π s base R
  let th (R : Row S ar → S.Node) (p : S.Node) (d : Bytes 32) (m : Msg S ar) := Select.value S (f R) p d m.val
  let ce (R : Row S ar → S.Node) (_ : Unit) (p : S.Node) (d : Bytes 32) (xs : List S.Node) := Select.value S (f R) p d xs
  have leaf : ∀ R d m, th R pk d m = R (d,m) := shadow_leaf S ar pk h π s
  have b := tcr_row_avg_le (Base S ar seeds) pk th leaf ce
    (fun R G _ d xs he => shadow_locality S ar pk h π s R G d xs he) A.choose
    (fun R st => forge (H R) st pk) A.ρ₀ (3*q) (fun st => by
      obtain ⟨N,hN⟩ := model S ar seeds A forge q pk st (hq st)
      exact ⟨publicModel (SkFormat.split S) a π s base N,fun R ev _ => hN _ _⟩)
  apply le_trans (le_of_eq _) b
  apply Finset.sum_congr rfl
  intro R _
  apply congrArg (fun u => unifW _ R * u)
  simp_rw [leaf]
  kexact (normalized S ar seeds A forge pk (f R) (H R) R).symm


theorem run_actual (pk : S.Node) (π : Permutation) (F : Row S ar → S.Node)
    (row : ∀ d (m : Msg S ar), (primitives (lanes π) S.vp.params).Thash pk d m.val = F (d,m)) :
    tcrInner (adversary S ar seeds A forge π) pk = Phase.run (fun _ => π)
      (test S ar seeds A forge pk (oracle π) F) (Select.prog S ar pk A.choose ([],[])) := by
  have hnorm := normalized S ar seeds A forge pk (fun _ => π) (oracle π) F
  have vals : Select.value S (fun _ : Bytes 32 => (π : Words → Words)) = (primitives (lanes π) S.vp.params).Thash :=
    funext fun p => funext fun d => funext fun xs => Select.value_actual S π p d xs
  have native_eq : Select.game S ar seeds (fun _ => π) = actualGame S ar seeds π := by
    unfold Select.game; rw [vals]; rfl
  have sim_eq : (simulateQ (SM_DT_TCR_oracles (Select.game S ar seeds (fun _ => π)) pk) A.choose).run ([],[]) =
      (simulateQ (SM_DT_TCR_oracles (actualGame S ar seeds π) pk) A.choose).run ([],[]) := by
    let v (g : S.Node → Bytes 32 → List S.Node → S.Node) := (simulateQ (SM_DT_TCR_oracles
      (tcrWithEval (Base S ar seeds) (fun p d (m : Msg S ar) => g p d m.val) (fun _ p d xs => g p d xs)) pk) A.choose).run ([],[])
    kexact congrArg v vals
  rw [sim_eq] at hnorm
  apply Eq.trans _ hnorm
  unfold tcrInner
  change qWeight _ (liftU ((simulateQ (SM_DT_TCR_oracles (actualGame S ar seeds π) pk) A.choose).run ([],[])) >>= _) _ = _
  apply congrArg (fun z : Closed (Work E) Bool => qWeight (· = true) z A.ρ₀)
  apply congrArg (fun k => liftU ((simulateQ (SM_DT_TCR_oracles (actualGame S ar seeds π) pk) A.choose).run ([],[])) >>= k)
  funext r
  apply congrArg (fun g => forge (oracle π) r.1 pk >>= g)
  funext jm
  cases q : r.2.1[jm.1]? with
  | none => rfl
  | some tm =>
    change pure (decide (_ ∧ (primitives (lanes π) S.vp.params).Thash pk tm.1 jm.2.val =
      (primitives (lanes π) S.vp.params).Thash pk tm.1 tm.2.val)) = _
    let dec (u v : S.Node) : Closed (Work E) Bool := pure (decide (jm.2 ≠ tm.2 ∧ u=v))
    kexact congrArg₂ dec (row tm.1 jm.2) (row tm.1 tm.2)

private theorem actual_eq (pk : S.Node) (h : ar ≤ 2) (π : Permutation) :
    tcrInner (adversary S ar seeds A forge π) pk =
      Phase.actual (SkFormat.split S) (Arity.input S ar pk h) (Select.prog S ar pk A.choose ([],[]))
        (test S ar seeds A forge pk) π := by
  let F := exactTable (SkFormat.split S) (Arity.input S ar pk h) π
  have row (d : Bytes 32) (m : Msg S ar) : (primitives (lanes π) S.vp.params).Thash pk d m.val = F (d,m) :=
    Arity.hash_eq S ar pk h π (d,m)
  exact run_actual S ar seeds A forge pk π F row

def loss (q Q : ℕ) : ℝ≥0∞ :=
  (2*((3*q : ℕ):ℝ≥0∞)+1)^2 / Fintype.card S.Node +
    (Q * Classic.forestPenalty Rate Words Q + Q*((Fintype.card (Row S ar):ℝ≥0∞)/Fintype.card Words)) +
    (((2:ℝ≥0∞)^63)⁻¹ + ((2:ℝ≥0∞)^384)⁻¹)

private theorem swap {X Y : Type} [Fintype X] [Fintype Y] (g : X → Y → ℝ≥0∞) :
    uniformMean (fun x => uniformMean (g x)) = uniformMean (fun y => uniformMean (fun x => g x y)) := by
  unfold uniformMean
  simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]

theorem fixed (pk : S.Node) (h : ar ≤ 2) (q Q : ℕ)
    (hq : ∀ st, PUE (spec := unifSpec) cnt0 (fun H => forge H st pk) q)
    (count : CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (Select.prog S ar pk A.choose ([],[]))) Q) :
    uniformMean (fun π => tcrInner (adversary S ar seeds A forge π) pk) ≤ loss S ar q Q := by
  let base : Row S ar := (default,⟨List.replicate ar default,by simp⟩)
  have zcap : 2^1344 ≤ Fintype.card (SkFormat.Suffix S) := by rw [SkFormat.card_suffix]; cases S <;> decide +kernel
  have wf (H : Port → Words) (F : Row S ar → S.Node) (r : A.State × Select.History S ar) :
      test S ar seeds A forge pk H F r ≤ 1 := by
    obtain ⟨N,hn⟩ := model S ar seeds A forge q pk r.1 (hq r.1)
    rw [test,← hn]; apply HybridModel.prob_le_one
  simp_rw [actual_eq S ar seeds A forge pk h]
  apply (Phase.phase_transfer (SkFormat.split S) (Arity.input S ar pk h) base Prod.fst _ _
    (Arity.row_bits S ar h) zcap (Select.valid_prog S ar pk h _ _) wf Q count).trans
  apply add_le_add (add_le_add _ le_rfl) le_rfl
  apply ShakeXof.mean_le_const
  intro π
  rw [swap]
  exact ShakeXof.mean_le_const (fun s => ideal_bound S ar seeds A forge pk h π s base q hq)

theorem bound (h : ar ≤ 2) (q Q : ℕ)
    (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => forge H st pk) q)
    (count : ∀ pk, CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (Select.prog S ar pk A.choose ([],[]))) Q) :
    uniformMean (fun π => qSM_DT_TCR_Advantage (adversary S ar seeds A forge π)) ≤ loss S ar q Q := by
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  change uniformMean (fun π => ∑' pk, PQ.Interactive.prob seeds (· = pk) * tcrInner (adversary S ar seeds A forge π) pk) ≤ _
  rw [ShakeXof.mean_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * loss S ar q Q :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (fixed S ar seeds A forge pk h q Q (fun st => hq st pk) (count pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * loss S ar q Q := ENNReal.tsum_mul_right
       _ ≤ _ := (mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le

end
end Reduction.ShakePermutation.SparsePort.ArityGame
#print axioms Reduction.ShakePermutation.SparsePort.ArityGame.bound

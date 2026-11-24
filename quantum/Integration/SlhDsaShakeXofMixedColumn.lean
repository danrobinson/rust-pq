import Integration.SlhDsaShakeXofMixedRow
import Integration.SlhDsaShakeXofPrf
import Integration.SlhDsaShakePermutationClassicalPublicRisk

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Ideal.HP QItsr
open SetOracle (uniformMean)
open ShakePermutation.Classic (mean_comm mean_mono mean_add avg_const)
open scoped ComplexOrder Kronecker
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- Discarding the log of deterministic oracle reads recovers the same
closed quantum program as answering those reads without recording them. -/
theorem discard_read_log {X Y W α : Type} [Fintype W] (v : X → Y)
    (P : QOC W (unifSpec + (X →ₒ Y)) α) (log : List X) :
    Prod.fst <$> close (trImpl v) P log = ansRun v P := by
  induction P using OracleComp.inductionOn generalizing log with
  | pure a => simp [ansRun_pure]
  | query_bind t f ih =>
    rcases t with j|u|x
    · rw [ansRun_instr,close_instr_bind,map_bind]
      exact congrArg _ (funext fun i => ih i log)
    · rw [ansRun_unif,close_unif_bind _ (show ForwardsUnif (trImpl (spec := X →ₒ Y) v) from fun _ _ => rfl),map_bind]
      exact congrArg _ (funext fun i => ih i log)
    · rw [ansRun_oracle,close_query_bind]
      change Prod.fst <$> (liftU (pure (v x,log++[x])) >>= _) = _
      rw [liftU_pure,pure_bind]
      exact ih (v x) _

def keySlice {K Dm X : Type} (emb : K × Dm ↪ X) (k : K) : Dm ↪ X :=
  ⟨fun d => emb (k,d), fun _ _ e => congrArg Prod.snd (emb.injective e)⟩

/-- Replacing the output prefix of the embedded slice at one uniform hidden
key couples the real keyed function to an independent random answer table.
The two ports may be adaptively interleaved and use the same underlying table. -/
theorem mixed_column_prf {K Dm X : Type} [Fintype K] [DecidableEq K] [SampleableType K] [Nonempty K]
    [Fintype Dm] [DecidableEq Dm] [Nonempty Dm] [Fintype X] [DecidableEq X] [Nonempty X]
    {n m : ℕ} (hn : n ≤ m) (emb : K × Dm ↪ X)
    {D : Type} [DecidableEq D] (address : D → Dm) (inj : Function.Injective address)
    {E : Type} [Fintype E] [DecidableEq E]
    (A : (X → Bytes m) → QOC (WS X (Bytes m) E) (PRFScheme.PRFOracleSpec D (Bytes n)) Bool)
    (Q : (D → Bytes n) → (X → Bytes m) → QOC (WS X (Bytes m) E) (unifSpec + (X →ₒ Bytes m)) Bool)
    (q t : ℕ) (represented : ∀ a H, ansRun H (Q a H) = ansRun a (A H))
    (coherent : ∀ a, PU (Q a) q) (reads : ∀ a H, CountBound (QC _ isR) (Q a H) t)
    (ρ : SubState ((X × Bytes m) × E)) (unit : ρ.matrix.trace = 1) :
    let loss := ENNReal.ofReal (8*(q:ℝ)^2 / Fintype.card K) +
      ((t:ℝ≥0∞)^(2⁻¹:ℝ)+2*q)^2 / Fintype.card K
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    uniformMean (fun g => qPrfRealPr (keyedScheme address (read emb hn g)) (A g) M) ≤
      uniformMean (fun g => qPrfIdealPr (A g) M) + loss := by
  classical
  intro loss M
  let Φ := fun (g : X → Bytes m) (f : Dm → Bytes n) => qWeight (· = true) (ansRun (f ∘ address) (A g)) M
  let col := keySlice emb
  let change := fun k (g : X → Bytes m) (f : Dm → Bytes n) => write (col k) g f
  have real (g : X → Bytes m) : qPrfRealPr (keyedScheme address (read emb hn g)) (A g) M =
      uniformMean (fun k => Φ g (read (col k) hn g)) := by
    unfold qPrfRealPr qPrfRealExperiment
    rw [show (keyedScheme address (read emb hn g)).keygen = ($ᵗ K) from rfl,qWeight_liftU_uniform_bind]
    simp only [uniformMean,unifW,← Finset.mul_sum]
    rfl
  have ideal (g : X → Bytes m) : qPrfIdealPr (A g) M = uniformMean (Φ g) := by
    have e := lazy_eq_avg address inj (· = true) (A g) M
    refine e.trans ?_
    simp only [uniformMean,unifW,← Finset.mul_sum]
    rfl
  have res (k : K) : uniformMean (fun g => Φ g (read (col k) hn g)) =
      uniformMean (fun g => uniformMean (fun f => Φ (change k g f) f)) := by
    rw [resample (col k) hn (fun g => Φ g (read (col k) hn g))]
    simp only [read_write,change]
  have hop (g : X → Bytes m) (f : Dm → Bytes n) :
      uniformMean (fun k => Φ (change k g f) f) ≤ Φ g f + loss := by
    let row := fun x => ((locate emb x).map Prod.fst).getD (Classical.arbitrary K)
    have same k x (ne : row x ≠ k) : change k g f x = g x := by
      unfold change write
      cases h : locate (col k) x with
      | none => rfl
      | some d =>
        have hx : emb (k,d) = x := located (col k) h
        exact False.elim (ne (by simp only [row,←hx,locate_emb,Option.map_some,Option.getD_some]))
    have h := mixed_row_reprogram g (fun k => change k g f) row same (Q (f ∘ address)) q t (coherent _) (reads _) ρ unit
    have erase (v : X → Bytes m) :
        qWeight (fun z => z.1 = true) (close (trImpl v) (Q (f ∘ address) v) []) M = Φ v f := by
      rw [← qWeight_map Prod.fst (· = true),discard_read_log,represented]
    dsimp only at h
    change uniformMean (fun k => qWeight _ _ M) ≤ qWeight _ _ M + _ + _ at h
    simpa only [erase,loss,add_assoc] using h
  simp only [real,ideal]
  rw [mean_comm (fun g k => Φ g (read (col k) hn g))]
  simp_rw [res]
  rw [mean_comm (fun k g => uniformMean (fun f => Φ (change k g f) f))]
  calc _ ≤ uniformMean (fun g => uniformMean (fun f => Φ g f + loss)) := by
          apply mean_mono
          intro g
          rw [mean_comm (fun k f => Φ (change k g f) f)]
          exact mean_mono (hop g)
       _ = _ := by simp only [mean_add,ShakePermutation.Classic.avg_const]

variable (S : Sha2Set) {N L : ℕ} {E : Type} [Fintype E] [DecidableEq E]

/-- Cost of distinguishing the real keyed slice from a fresh random function
with q coherent reads and t classical reads of the public XOF. -/
noncomputable def mixedPrfLoss (q t : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (8*(q:ℝ)^2/2^(8*S.vp.params.n)) +
    ((t:ℝ≥0∞)^(2⁻¹:ℝ)+2*q)^2/2^(8*S.vp.params.n)

abbrev MixedMachine (N : ℕ) (E : Type) [Fintype E] [DecidableEq E] (D : Type) :=
  (D → S.Node) → ShakeApi.RawTable S N →
    QOC (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E)
      (unifSpec + (ShakeApi.Input N →ₒ Bytes S.vp.params.m)) Bool

private theorem node_card_enn : (Fintype.card S.Node : ℝ≥0∞) = 2^(8*S.vp.params.n) := by
  have hn : Fintype.card S.Node = 2^(8*S.vp.params.n) := by
    rw [card_bytes',pow_mul]; rfl
  exact_mod_cast hn

theorem mixed_sk_prf (cap : 2*S.vp.params.n+32 ≤ N)
    (A : ShakeApi.RawTable S N → QOC (Work S N E) (PRFScheme.PRFOracleSpec (S.Node × SkAdrs S.vp) S.Node) Bool)
    (Q : MixedMachine S N E (S.Node × SkAdrs S.vp)) (q t : ℕ)
    (represented : ∀ a H, ansRun H (Q a H) = ansRun a (A H))
    (coherent : ∀ a, PU (Q a) q) (reads : ∀ a H, CountBound (QC _ isR) (Q a H) t)
    (ρ : SubState ((ShakeApi.Input N × Bytes S.vp.params.m) × E)) (unit : ρ.matrix.trace = 1) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    uniformMean (fun g => qPrfRealPr (skPrfC S.vp (ShakeApi.primitives S (ShakeApi.extend g))) (A g) M) ≤
      uniformMean (fun g => qPrfIdealPr (A g) M) + mixedPrfLoss S q t := by
  simp only [skScheme S cap,mixedPrfLoss,← Compression.node_card_real S,← node_card_enn S]
  exact mixed_column_prf (node_le_digest S) (skEmb S cap) (skAddress S) (skAddress_injective S) A Q q t represented coherent reads ρ unit

theorem mixed_msg_prf (cap : 2*S.vp.params.n+L ≤ N)
    (A : ShakeApi.RawTable S N → QOC (Work S N E) (PRFScheme.PRFOracleSpec (MsgDomain S L) S.Node) Bool)
    (Q : MixedMachine S N E (MsgDomain S L)) (q t : ℕ)
    (represented : ∀ a H, ansRun H (Q a H) = ansRun a (A H))
    (coherent : ∀ a, PU (Q a) q) (reads : ∀ a H, CountBound (QC _ isR) (Q a H) t)
    (ρ : SubState ((ShakeApi.Input N × Bytes S.vp.params.m) × E)) (unit : ρ.matrix.trace = 1) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    uniformMean (fun g => qPrfRealPr (boundedMsgScheme S g) (A g) M) ≤
      uniformMean (fun g => qPrfIdealPr (A g) M) + mixedPrfLoss S q t := by
  simpa only [msgScheme S cap,mixedPrfLoss,Compression.node_card_real S,node_card_enn S] using
    mixed_column_prf (node_le_digest S) (msgEmb S cap) (id) (Function.injective_id) A Q q t represented coherent reads ρ unit

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.mixed_column_prf
#print axioms Reduction.ShakeXof.mixed_sk_prf
#print axioms Reduction.ShakeXof.mixed_msg_prf

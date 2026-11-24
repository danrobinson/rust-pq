import Integration.SlhDsaCompressionPrfCost
import Integration.SlhDsaCompressionBudget

namespace Reduction.Compression.SkGame
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Resources2 Open QMsg
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f
variable (rand : S.Node → S.Node → ProbComp S.Node) (answer : S.Node × Adrs → S.Node)

def signBudget (L : ℕ) := msgPrfCalls S L + Lazy.signHashes S.vp * signMax S L

theorem signBudget_mono {l L : ℕ} (h : l ≤ L) : signBudget S l ≤ signBudget S L := by
  apply Nat.add_le_add _ (Nat.mul_le_mul_left _ (signMax_mono S h))
  unfold msgPrfCalls
  split <;> omega

noncomputable def signer (pk root sk : S.Node) (H : Input → Output) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core))
      (StateT (SigLog S.vp P₀) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SigLog S.vp P₀) ProbComp) +
    sigSignOracle (vp := S.vp) (prims := P₀) (fun m => simulateQ (handler S f answer H)
      (openSignP (fun k => rand k.pkSeed k.pkRoot) ⟨pk,root⟩ sk m))

private noncomputable def clipped (L : ℕ) (pk root sk : S.Node) (H : Input → Output) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core))
      (StateT (SigLog S.vp P₀) ProbComp)
  | .inl n => signer S f rand answer pk root sk H (.inl n)
  | .inr m => signer S f rand answer pk root sk H (.inr (m.take L))

private theorem signer_cost (L : ℕ) (pk root sk : S.Node) (t) (log : SigLog S.vp P₀) :
    EvalCost (fun H => (clipped S f rand answer L pk root sk H t).run log)
      (sgnW (signBudget S L) t) := by
  rcases t with n|m
  · exact EvalCost.const _
  · simp only [clipped,signer,QueryImpl.add_apply_inr,sigSignOracle,run_appendLog_apply]
    exact ((sign_cost S f answer (fun k => rand k.pkSeed k.pkRoot) ⟨pk,root⟩ sk (m.take L)).bind
      fun sig => EvalCost.const (X := Input) (Y := Output) (pure (sig,log ++ [⟨m.take L,sig⟩]) : ProbComp _)
      ).mono (by simpa only [Nat.add_zero, signBudget] using signBudget_mono S (List.length_take_le L m))

variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

noncomputable def answered (pk : S.Node) (H : Input → Output) : Closed (WS Input Output E) Bool := do
  let sk ← liftU ($ᵗ S.Node)
  let root ← liftU (simulateQ (handler S f answer H) (openKeygenP (vp := S.vp) P₀ pk))
  let z ← close (signer S f rand answer pk root sk H) (mainAt S f F H ⟨pk,root⟩) []
  liftU (simulateQ (fun t => pure (hashPort S f H t) : QueryImpl _ ProbComp)
    (sufCheckOpen ⟨pk,root⟩ z.1 z.2))

def budget (L q qs : ℕ) := Lazy.keygenHashes S.vp * signMax S 0 + q + qs * signBudget S L +
  (1 + verifyHashes S.vp) * signMax S L

theorem answered_cost (c : Caps) (pk : S.Node) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (spec := unifSpec) cnt0 (answered S f rand answer F pk) (budget S c.ml q qs) := by
  let V := (1 + verifyHashes S.vp) * signMax S c.ml
  let K := signBudget S c.ml
  let work := fun (sk root : S.Node) (H : Input → Output) =>
    close (clipped S f rand answer c.ml pk root sk H)
      (mainAt S f F H ⟨pk,root⟩) [] >>= fun z =>
        (liftU (simulateQ (fun t => pure (hashPort S f H t) : QueryImpl _ ProbComp)
          (sufCheckOpen ⟨pk,root⟩ (z.1.1.take c.ml,z.1.2) z.2)) : Closed (WS Input Output E) Bool)
  have hwork (sk root) : PUE (spec := unifSpec) cnt0 (work sk root) (q + qs*K + V) := by
    refine PUE.bind (PUE.close _ (signer_cost S f rand answer c.ml pk root sk)
      (mainAt_pue S f F q qs K hq hs ⟨pk,root⟩) _) fun z => ?_
    have hv := (check_cost S f ⟨pk,root⟩ (z.1.1.take c.ml,z.1.2) z.2).mono
      (Nat.mul_le_mul_left _ (signMax_mono S (List.length_take_le c.ml z.1.1)))
    have h := PUE.liftU_bind (E := E) (q := 0) (B := fun b _ => (pure b : Closed (WS Input Output E) _))
      hv (fun b => PUE.pure b 0)
    simpa only [bind_pure,Nat.zero_add,V] using h
  have eq : answered S f rand answer F pk = fun H => liftU ($ᵗ S.Node) >>= fun sk =>
      liftU (simulateQ (handler S f answer H) (openKeygenP (vp := S.vp) P₀ pk)) >>= fun root => work sk root H := by
    funext H
    apply bind_congr
    intro sk
    apply bind_congr
    intro root
    apply close_congr_on (G := Gint c.ml) (ok := fun z => z.1.length ≤ c.ml)
    · rintro (j|m) ht
      · rfl
      · change m.length ≤ c.ml at ht
        exact congrArg (β := StateT (SigLog S.vp P₀) ProbComp (GeneralScheme.SignatureCore S.vp (P₀).core))
          (fun m : List Byte => signer S f rand answer pk root sk H (.inr m)) (List.take_of_length_le ht).symm
    · intro z hz
      simp only [List.take_of_length_le hz]
    · exact mainAt_cap S f F c hc H ⟨pk,root⟩
  rw [eq]
  have h := PUE.liftU_bind (EvalCost.const (X := Input) (Y := Output) ($ᵗ S.Node : ProbComp S.Node))
    fun sk => PUE.liftU_bind (simulate_cost S f answer _ _ (keygen_count S f pk)) (hwork sk)
  apply h.mono
  dsimp only [budget,V,K]
  omega

end Reduction.Compression.SkGame
#print axioms Reduction.Compression.SkGame.answered_cost

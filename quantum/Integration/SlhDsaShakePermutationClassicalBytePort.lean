import Integration.SlhDsaShakePermutationClassicalCrossing
import Integration.SlhDsaShakePermutationHonestGame
import Integration.SlhDsaCompressionClassicalGame

namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp MLink SLHDSA Classical PQ.Interactive PQ.QROM Quantum ENNReal
open SetOracle (uniformMean)
open Compression.ClassicalPort (Reads answers translate program_weight)
open Honest (ByteMessage ByteSig)
noncomputable section

abbrev SignSpec := unifSpec + (ByteMessage →ₒ ByteSig)
abbrev Claim := ByteMessage × ByteSig
abbrev Log := QueryLog (ByteMessage →ₒ ByteSig)
abbrev Fresh := Log → ByteMessage → ByteSig → Bool
abbrev CForger (X Y : Type) := List SLHDSA.Byte → OracleComp (Reads X Y SignSpec) Claim
abbrev Scheme (m : Type → Type) [Monad m] := SignatureAlg m ByteMessage (List SLHDSA.Byte) (List SLHDSA.Byte) ByteSig

def coinValue {Z : Type} (ev : Z → ℝ≥0∞) (P : ProbComp Z) : ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℝ≥0∞) ev (fun n _ k => uniformMean fun r : Fin (n+1) => k r) P

theorem coin_bind {Z V : Type} (ev : V → ℝ≥0∞) (P : ProbComp Z) (k : Z → ProbComp V) :
    coinValue ev (P >>= k) = coinValue (fun z => coinValue ev (k z)) P := by
  induction P using OracleComp.inductionOn with
  | pure => simp only [pure_bind]; rfl
  | query_bind i f ih => rw [bind_assoc]; exact congrArg uniformMean (funext ih)

theorem coin_probability {Z : Type} (event : Z → Prop) [DecidablePred event] (P : ProbComp Z) :
    prob P event = coinValue (fun z => hit (event z)) P := by
  induction P using OracleComp.inductionOn with
  | pure => exact prob_pure _ _
  | query_bind n k ih =>
    rw [prob_unif_query_bind]
    simp only [ih,Finset.mul_sum]
    change (∑ v : Fin (n+1), (↑n+1 : ℝ≥0∞)⁻¹ * coinValue _ (k v)) = ∑ v : Fin (n+1), unifW _ v * coinValue _ (k v)
    simp [unifW]

def playerValue {X Y σ : Type} (step : X → σ → Y × σ) (A : Scheme ProbComp)
    (pk sk : List SLHDSA.Byte) (fresh : Fresh) (P : OracleComp (Reads X Y SignSpec) Claim) :
    σ → Log → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => σ → Log → ℝ≥0∞)
    (fun claim _ log => coinValue (fun v => hit ((fresh log claim.1 claim.2 && v)=true)) (A.verify pk claim.1 claim.2))
    (fun i _ k s log => match i with
      | .inl x => let z := step x s; k z.1 z.2 log
      | .inr (.inl n) => uniformMean fun v : Fin (n+1) => k v s log
      | .inr (.inr msg) => coinValue (fun sig => k sig s (log++[⟨msg,sig⟩])) (A.sign pk sk msg)) P

def sigValue {X Y σ : Type} (step : X → σ → Y × σ) (s : σ) (A : Scheme ProbComp)
    (F : CForger X Y) (fresh : Fresh) :=
  coinValue (fun ks => playerValue step A ks.1 ks.2 fresh (F ks.1) s []) A.keygen

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

def liftClassical (x0 : X) (F : CForger X Y) : PortForger X Y Unit where
  main pk := simulateQ translate (F pk)
  ρ₀ := (SubState.basis (((x0,0),()),())).matrix
  posSemidef := (SubState.basis (((x0,0),()),())).posSemidef
  trace_eq_one := by simp [SubState.matrix_basis]

def terminal (A : Scheme ProbComp) (pk : List SLHDSA.Byte) (fresh : Fresh) (z : Claim × Log) : ProbComp Bool := do
  let v ← A.verify pk z.1.1 z.1.2
  pure (fresh z.2 z.1.1 z.1.2 && v)

theorem player_closed (H : X → Y) (A : Scheme ProbComp) (pk sk : List SLHDSA.Byte) (fresh : Fresh)
    (P : OracleComp (Reads X Y SignSpec) Claim) (log : Log) :
    coinValue (fun z => coinValue (fun v => hit (v=true)) (terminal A pk fresh z))
      ((simulateQ (signImpl A pk sk) (simulateQ (answers H) P)).run log) =
      playerValue (fun x (s : Unit) => (H x,s)) A pk sk fresh P () log := by
  induction P using OracleComp.inductionOn generalizing log with
  | pure c =>
    simp only [simulateQ_pure,StateT.run_pure]
    change coinValue _ (_ >>= _) = _
    rw [coin_bind]
    rfl
  | query_bind i k ih =>
    rcases i with x|n|msg
    · simp only [simulateQ_bind,simulateQ_spec_query,answers,pure_bind]; exact ih _ _
    · simp only [simulateQ_bind,simulateQ_spec_query,answers,StateT.run_bind,signImpl,StateT.run]
      change coinValue _ (((fun v => (v,log)) <$> (liftM (unifSpec.query n) : ProbComp _)) >>= _) = _
      simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_apply]
      rw [coin_bind]
      exact congrArg (@uniformMean (Fin (n+1)) _) (funext fun v => ih v log)
    · simp only [simulateQ_bind,simulateQ_spec_query,answers,StateT.run_bind,signImpl,StateT.run]
      change coinValue _ (((fun sig => (sig,log++[⟨msg,sig⟩])) <$> A.sign pk sk msg) >>= _) = _
      simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_apply]
      rw [coin_bind]
      exact congrArg (fun f => coinValue f (A.sign pk sk msg)) (funext fun v => ih v _)

theorem lift_value (x0 : X) (H : X → Y) (A : Scheme ProbComp) (F : CForger X Y) (fresh : Fresh) :
    qWeight (· = true) (qSigExperiment fresh ((liftClassical x0 F).at H A)) (liftClassical x0 F).ρ₀ =
      sigValue (fun x (s : Unit) => (H x,s)) () A F fresh := by
  let reg : Compression.ClassicalPort.Reg X Y := ((x0,0),())
  let value (ks : List SLHDSA.Byte × List SLHDSA.Byte) := playerValue (fun x (s : Unit) => (H x,s)) A ks.1 ks.2 fresh (F ks.1) () []
  let body (ks : List SLHDSA.Byte × List SLHDSA.Byte) :=
    (simulateQ (signImpl A ks.1 ks.2) (simulateQ (answers H) (F ks.1))).run [] >>= terminal A ks.1 fresh
  have prob_body (ks) : prob (body ks) (· = true) = value ks := by
    change prob (_ >>= _) _ = _
    rw [coin_probability,coin_bind]; exact player_closed H A ks.1 ks.2 fresh (F ks.1) []
  have he : prob (A.keygen >>= body) (· = true) = sigValue (fun x (s : Unit) => (H x,s)) () A F fresh := by
    rw [coin_probability,coin_bind]
    exact congrArg (fun f => coinValue f A.keygen) (funext fun ks => (coin_probability _ _).symm.trans (prob_body ks))
  apply Eq.trans _ he
  unfold qSigExperiment
  rw [← one_mul (prob _ _)]
  apply qWeight_liftU_bind
  intro ks
  rw [one_mul]
  let qt := fun z : Claim × Log =>
    (liftU (W := WS X Y Unit) (A.verify ks.1 z.1.1 z.1.2) >>= fun v => pure (fresh z.2 z.1.1 z.1.2 && v))
  have h := program_weight H (signImpl A ks.1 ks.2) (F ks.1) [] reg qt (terminal A ks.1 fresh) (· = true) (by
    intro z r
    rw [← one_mul (prob _ _)]
    apply qWeight_liftU_bind
    intro v
    simp [qWeight_pure,prob_pure])
  dsimp only [PortForger.at,liftClassical,SubState.matrix_basis,qt,body] at h ⊢
  convert h using 2

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.lift_value

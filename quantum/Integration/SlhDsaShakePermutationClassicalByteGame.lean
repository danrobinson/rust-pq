import Integration.SlhDsaShakePermutationClassicalBytePort

namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp MLink SLHDSA Classical PQ.Interactive PQ.QROM Quantum
open Honest (ByteMessage ByteSig RawSpec)
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section
set_option maxRecDepth 8192

def liftRaw (S : Sha2Set) (N : ℕ) : QueryImpl (RawSpec S N) (OracleComp (Outer S N))
  | .inl n => (Outer S N).query (.inl n)
  | .inr x => (Outer S N).query (.inr (.inr x))

def drive (S : Sha2Set) (N : ℕ) (A : Scheme (OracleComp (RawSpec S N))) (pk sk : List SLHDSA.Byte)
    (fresh : Fresh) (P : OracleComp (Compression.ClassicalPort.Reads Port Words SignSpec) Claim) :
    Log → OracleComp (Outer S N) Bool :=
  OracleComp.construct (C := fun _ => Log → OracleComp (Outer S N) Bool)
    (fun claim log => simulateQ (liftRaw S N) (A.verify pk claim.1 claim.2) >>= fun v =>
      pure (fresh log claim.1 claim.2 && v))
    (fun i _ k log => match i with
      | .inl x => (Outer S N).query (.inr (.inl x)) >>= fun y => k y log
      | .inr (.inl n) => (Outer S N).query (.inl n) >>= fun y => k y log
      | .inr (.inr m) => simulateQ (liftRaw S N) (A.sign pk sk m) >>= fun y => k y (log++[⟨m,y⟩])) P

def byteGame (S : Sha2Set) (N : ℕ) (A : Scheme (OracleComp (RawSpec S N))) (F : CForger Port Words) (fresh : Fresh) :
    OracleComp (Outer S N) Bool := do
  let ks ← simulateQ (liftRaw S N) A.keygen
  drive S N A ks.1 ks.2 fresh (F ks.1) []

def service (S : Sha2Set) (N : ℕ) {σ : Type} (step : Port → σ → Words × σ) (raw : ShakeApi.RawTable S N) :
    (i : (Native S N).Domain) → σ → (Native S N).Range i × σ
  | .inl x,s => step x s
  | .inr x,s => (raw x,s)

theorem mixed_bind {ι σ Z V : Type} {sp : OracleSpec ι} (step : (i : ι) → σ → sp.Range i × σ)
    (ev : V → σ → ℝ≥0∞) (P : OracleComp (unifSpec + sp) Z) (k : Z → OracleComp (unifSpec + sp) V) (s : σ) :
    mixedRun step ev (P >>= k) s = mixedRun step (fun z s' => mixedRun step ev (k z) s') P s := by
  induction P using OracleComp.inductionOn generalizing s with
  | pure => simp only [pure_bind]; rfl
  | query_bind i f ih =>
    rw [bind_assoc]
    rcases i with n|j
    · exact congrArg (@uniformMean (Fin (n+1)) _) (funext fun r => ih r s)
    · exact ih _ _

theorem service_raw (S : Sha2Set) (N : ℕ) {σ Z : Type} (step : Port → σ → Words × σ) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (RawSpec S N) Z) (ev : Z → σ → ℝ≥0∞) (s : σ) :
    mixedRun (service S N step raw) ev (simulateQ (liftRaw S N) P) s =
      coinValue (fun z => ev z s) (simulateQ (Compression.SkGame.answerImpl raw) P) := by
  induction P using OracleComp.inductionOn with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|x
    · simp only [simulateQ_bind,simulateQ_spec_query,liftRaw,Compression.SkGame.answerImpl]
      exact congrArg uniformMean (funext ih)
    · simp only [simulateQ_bind,simulateQ_spec_query,liftRaw,Compression.SkGame.answerImpl,pure_bind]
      exact ih _

theorem service_drive (S : Sha2Set) (N : ℕ) {σ : Type} (step : Port → σ → Words × σ) (raw : ShakeApi.RawTable S N)
    (A : Scheme (OracleComp (RawSpec S N))) (pk sk : List SLHDSA.Byte) (fresh : Fresh)
    (P : OracleComp (Compression.ClassicalPort.Reads Port Words SignSpec) Claim) (s : σ) (log : Log) :
    mixedRun (service S N step raw) (fun v _ => hit (v=true)) (drive S N A pk sk fresh P log) s =
      playerValue step (A.map (simulateQ' (Compression.SkGame.answerImpl raw))) pk sk fresh P s log := by
  induction P using OracleComp.inductionOn generalizing s log with
  | pure c =>
    change mixedRun _ _ (_ >>= _) _ = _
    rw [mixed_bind,service_raw]
    rfl
  | query_bind i k ih =>
    rcases i with x|n|msg
    · exact ih _ _ _
    · exact congrArg (@uniformMean (Fin (n+1)) _) (funext fun v => ih v s log)
    · change mixedRun _ _ (_ >>= _) _ = _
      rw [mixed_bind,service_raw]
      exact congrArg (fun f => coinValue f (simulateQ _ (A.sign pk sk msg))) (funext fun v => ih v s _)

theorem service_game (S : Sha2Set) (N : ℕ) {σ : Type} (step : Port → σ → Words × σ) (raw : ShakeApi.RawTable S N)
    (A : Scheme (OracleComp (RawSpec S N))) (F : CForger Port Words) (fresh : Fresh) (s : σ) :
    mixedRun (service S N step raw) (fun v _ => hit (v=true)) (byteGame S N A F fresh) s =
      sigValue step s (A.map (simulateQ' (Compression.SkGame.answerImpl raw))) F fresh := by
  rw [byteGame,mixed_bind,service_raw]
  exact congrArg (fun f => coinValue f (simulateQ _ A.keygen)) (funext fun ks => service_drive S N step raw A ks.1 ks.2 fresh _ s [])

theorem real_mixed (S : Sha2Set) (N : ℕ) {Z : Type} (π : Permutation) (P : OracleComp (Outer S N) Z) (ev : Z → ℝ≥0∞) :
    realOuter S N π ev P = mixedRun (service S N (fun x (s : Unit) => (oracle π x,s))
      (ShakeApi.restrict S N (answer S (lanes π)))) (fun z _ => ev z) P () := by
  induction P using OracleComp.inductionOn with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩|x
    · exact congrArg uniformMean (funext ih)
    · exact ih _
    · exact ih _

theorem ideal_mixed (S : Sha2Set) (N T : ℕ) {Z : Type} (H : Row T → Words) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (Outer S N) Z) (ev : Z → ℝ≥0∞) (t : EdgeTrace Words) :
    idealOuter S N T H raw ev P t = mixedRun (service S N (fun x t => visible T H t x.1 x.2) raw) (fun z _ => ev z) P t := by
  induction P using OracleComp.inductionOn generalizing t with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩|x
    · exact congrArg uniformMean (funext fun r => ih r t)
    · exact ih _ _
    · exact ih _ _

theorem byte_real (S : Sha2Set) (N : ℕ) (base : ShakeApi.Xof S) (r : S.Node → S.Node → ProbComp S.Node)
    (seeds : ProbComp S.Node) (F : CForger Port Words) (fresh : Fresh) (c : Caps)
    (cap : ShakeApi.rawCap S 67 c.ml ≤ N)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) ((liftClassical (false,0) F).main pk)) (π : Permutation) :
    realOuter S N π (fun v => hit (v=true)) (byteGame S N (Honest.rawScheme S N base r seeds) F fresh) =
      qWeight (·=true) (qSigExperiment fresh (experiment S r seeds (liftClassical (false,0) F) π)) (liftClassical (false,0) F).ρ₀ := by
  rw [real_mixed,service_game,← lift_value (false,0)]
  have full := Honest.runJoint_permutation S N base r seeds fresh _ c cap hc π
  have closed := Honest.runJoint S N (liftClassical (false,0) F) (Honest.rawScheme S N base r seeds)
    fresh (oracle π) (ShakeApi.restrict S N (answer S (lanes π)))
  exact congrArg (fun p => qWeight (·=true) p (liftClassical (false,0) F).ρ₀) (closed.symm.trans full)

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.byte_real

import Integration.SlhDsaCompressionHmacMachine
import Integration.SlhDsaCompressionHmacCollision

/-! The budgeted open machine realizes the message-PRF distinguisher used
in the strong signature reduction at every pair of compression tables. -/
namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg
open scoped Kronecker
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

private theorem machine_self (f : RandFns S.vp.params) (H : Input → Output)
    (hp : hashPort S f H = PublicHash.impl (randPrims f)) :
    machine S f rand seeds F H = qbPrfMsgWL sufCheck (qPureBytesToInternal
      (F.at H (pureBytesAlg S.vp (randPrims f) (SetOracle.codecFor S f)
      (fun pk => rand pk.pkSeed pk.pkRoot) seeds))) := by
  unfold machine qbPrfMsgWL
  rw [hp]
  congr 1
  unfold openMachine qMsgOpenW
  apply bind_congr
  intro pk
  apply bind_congr
  intro root
  unfold qRunForgerSig
  rw [mainAt_eq S f F rand seeds]
  apply bind_congr
  intro z
  simp only [liftQ_pure]
  unfold verdict
  rw [hp,sufCheckOpen_eq]

theorem machine_oracle (g : CompressionTables) :
    machine S (carrier S) rand seeds F (oracle g) = qbPrfMsgWL sufCheck (reduced S rand seeds F g) := by
  let real := functions S g
  let base := {carrier S with thash := real.thash, hmsg := real.hmsg}
  have hm : machine S (carrier S) rand seeds F (oracle g) =
      machine S base rand seeds F (oracle g) := by qm_kernel_rfl
  have hp : hashPort S base (oracle g) = PublicHash.impl (randPrims base) := by
    unfold hashPort
    rw [tablesOf_oracle]
    funext t
    cases t <;> rfl
  rw [hm, machine_self S rand seeds F base (oracle g) hp]
  have tr := QMsg.qbPrfMsgWL_setPrf (prims := randPrims base) real.prf real.prfMsg
    (SetOracle.codecFor S base) (fun k => rand k.pkSeed k.pkRoot) (fun k => rand k.pkSeed k.pkRoot)
    (fun _ => rfl) seeds (F.at (oracle g) (pureBytesAlg S.vp (randPrims base) (SetOracle.codecFor S base)
      (fun k => rand k.pkSeed k.pkRoot) seeds))
  kexact tr.symm

/-- For each wide SHA-2 set, the real-to-ideal message-PRF hop costs the
monitored inner-digest collision probability and the two hidden-state losses. -/
theorem signature_hmac_collision (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let Q := fun g => reduced S rand seeds F g
    let A := machine S (carrier S) rand seeds F
    let B := budget S c.ml q qs
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (msgPrf S.vp (randPrims (functions S g)))
      (qbPrfMsgWL sufCheck (Q g)) F.ρ₀) ≤
      (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (qbPrfMsgWL sufCheck (Q g)) F.ρ₀) +
      (∑ g : CompressionTables, unifW _ g * ∑ i : Chain512, unifW _ i * digestCollisionPr S A F.ρ₀ g i) +
      ENNReal.ofReal (8*(B:ℝ)^2 / 2^512) + ENNReal.ofReal (8*(B:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  classical
  intro Q A B
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input × Output) × E) F.ρ₀ F.posSemidef F.trace_eq_one
  have h := wide_hmac_collision S A hw B
    (machine_cost S (carrier S) rand seeds F c q qs hq hs hc) ρ
  dsimp only at h
  rw [← hρ] at h
  simp only [A,machine_oracle S rand seeds F] at h
  kexact h

end Reduction.Compression.HmacKey
#print axioms Reduction.Compression.HmacKey.machine_oracle
#print axioms Reduction.Compression.HmacKey.signature_hmac_collision

import Integration.SlhDsaShakeXofSkOpen

namespace Reduction.ShakeApi.Sk.Mixed
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Open QMsg QItsr
open ShakePermutation.Honest (RawSpec hashWeight)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "P₀" => primitives S base
local notation "Raw" => RawSpec S N
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input N) (Bytes S.vp.params.m) E)
local notation "Work" => WS (Input N) (Bytes S.vp.params.m) E
local notation "Sig" => GeneralScheme.SignatureCore S.vp (Primitives.core (primitives S base))

theorem forger_public (pk : PublicKeyCore (P₀).core) (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) :
    PU (fun H => qmForger S N F base H pk) q :=
  PU.map _ (PU.wrap0 _ (PU.map _ (PU.wrap0 _ (PU.compileQ _ _ (hq _)))))

theorem forger_signs (pk : PublicKeyCore (P₀).core) (k s : ℕ)
    (hs : ∀ pk, CountBound isSign (F.main pk) s) (H : RawTable S N) :
    WCount (qw Work (sgnW (S := Sig) k)) (qmForger S N F base H pk) (s*k) := by
  unfold qmForger
  let P := F.main (encodePublicKey (codec S base) pk)
  have no : CountBound (fun _ => False) P 0 := (countBound_iff_wCount _ _ _).2 (wCount_zero _ _)
  have h := wCount_of_countBound (fun _ => False) isSign
    (qw ((Input N × Bytes S.vp.params.m) × E) (spec := portSpec + (unifSpec + ((List SLHDSA.Byte × List SLHDSA.Byte) →ₒ Option (List SLHDSA.Byte))))
      (Sum.elim (fun (_ : Unit) => 0) (sgnW (S := Option (List SLHDSA.Byte)) k))) k
    (by rintro (j|u|n|m) <;> simp [qw,isSign,sgnW]) P 0 s no (hs _)
  simp only [Nat.zero_add] at h
  refine WCount.map (WCount.wrap0 _ (w := sgnW (S := Except External.Error Sig) k) ?_
    (WCount.map (WCount.wrap0 _ (w := sgnW (S := Option (List SLHDSA.Byte)) k) ?_ (WCount.compileQ H h)) _)) _
  · rintro (n|e)
    · exact wCount_liftM_query _ _ le_rfl
    · simp only [Guarded.signingImpl]
      split
      · trivial
      · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · rintro (n|m)
    · exact wCount_liftM_query _ _ le_rfl
    · exact WCount.map (wCount_liftM_query _ _ le_rfl) _

theorem public_cost (a : S.Node × SkAdrs S.vp → S.Node) (q : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) : PU (machine S N rand seeds F a) q := by
  apply PU.liftQ_bind
  intro pk
  apply PU.liftQ_bind
  intro sk
  apply PU.liftQ_bind
  intro root
  simpa only [Nat.add_zero] using PU.bind (PU.wrap _ (forger_public S N _ F _ q hq) [])
    (q₂ := 0) (fun z => PU.liftQ (E := E) _ 0)

private theorem uniform_cost {α : Type} (P : ProbComp α) : WCount hashWeight (liftM P : OracleComp Raw α) 0 := by
  induction P using OracleComp.inductionOn with
  | pure => trivial
  | query_bind n k ih =>
    rw [liftM_bind]
    exact (WCount.bind (wCount_liftM_query (sp := Raw) hashWeight (.inl n) le_rfl) ih)

private theorem signer_count (a : S.Node × Adrs → S.Node) (pk root sk : S.Node) (t log) :
    WCount hashWeight ((signer S N base rand a pk root sk t).run log) (sgnW (Lazy.signHashes S.vp+1) t) := by
  rcases t with n|m
  · change WCount hashWeight ((fun x => (x,log)) <$> (liftM ((Raw).query (.inl n)) : OracleComp Raw _)) 0
    exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · simp only [signer,QueryImpl.add_apply_inr,sigSignOracle,run_appendLog_apply]
    exact (WCount.bind (sign_count S N base a (signRand S rand base) ⟨pk,root⟩ sk m)
      (m := 0) (fun _ => wCount_pure _ _ _)).mono (Nat.add_zero _).le

theorem read_cost (a : S.Node × SkAdrs S.vp → S.Node) (s : ℕ)
    (hs : ∀ pk, CountBound isSign (F.main pk) s) (H : RawTable S N) :
    CountBound (QC Work isR) (machine S N rand seeds F a H) (Sk.budget S 0 s) := by
  apply (countBound_iff_wCount _ _ _).2
  apply WCount.wmono (w' := qw Work (spec := Raw) hashWeight) (fun t => by rcases t with j|n|x <;> rfl)
  unfold machine body Sk.budget
  simp only [Nat.add_zero,Nat.add_assoc]
  nth_rewrite 1 [← Nat.zero_add (Lazy.keygenHashes S.vp + _)]
  refine WCount.bind (WCount.liftQ (uniform_cost S N _)) fun pk => ?_
  nth_rewrite 1 [← Nat.zero_add (Lazy.keygenHashes S.vp + _)]
  refine WCount.bind (WCount.liftQ (uniform_cost S N _)) fun sk => ?_
  refine WCount.bind (WCount.liftQ (key_count S N _ _ pk)) fun root => ?_
  refine WCount.bind (WCount.wrap _ (signer_count S N _ rand _ pk root sk)
    (forger_signs S N _ F _ _ s hs H) []) fun z => ?_
  exact WCount.liftQ (check_count S N _ _ z.1 z.2)

end Reduction.ShakeApi.Sk.Mixed
#print axioms Reduction.ShakeApi.Sk.Mixed.public_cost
#print axioms Reduction.ShakeApi.Sk.Mixed.read_cost

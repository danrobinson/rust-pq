import Integration.SlhDsaShakePermutationMsgSplit
import Integration.SlhDsaShakeApiMsgBridge

/-! The native message-PRF reduction issues exactly one classical challenge
per signing invocation. Lazy ideal secret-key lookups and all quantum
public-port operations cost zero message-PRF calls. -/
namespace Reduction.ShakePermutation.MsgSplit
open Classical MLink Ideal SLHDSA SLHDSA.Security Quantum OracleComp OracleSpec PQ.Interactive QMsg
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives

private theorem pure_sample {ι A : Type} {sp : OracleSpec ι} (g : (unifSpec + sp).Domain → ℕ)
    (free : ∀ n, g (.inl n) = 0) (u : ProbComp A) : WCount g (liftM u : OracleComp (unifSpec + sp) A) 0 := by
  induction u using OracleComp.inductionOn with
  | pure a => simp only [liftM_pure]; trivial
  | query_bind n k ih =>
    rw [liftM_bind]
    exact (WCount.bind (wCount_liftM_query g (.inl n) (le_of_eq (free n))) ih : WCount _ _ (0+0))

variable (S : Sha2Set) (base : ShakeApi.Xof S)
local notation "P₀" => ShakeApi.primitives S base
local notation "PS" => PRFScheme.PRFOracleSpec (S.Node × List SLHDSA.Byte) S.Node
local notation "OS" => Lazy.OSpec P₀ (Lazy.msgG P₀)

private def cost {ι κ D : Type} : ℕ ⊕ ι ⊕ D ⊕ κ → ℕ := fun i => if Lazy.kind i = .game then 1 else 0

variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)

private theorem wrapped_signs (qs : ℕ) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (H : Port → Words) (pk : PublicKeyCore (P₀).core) :
    WCount (qw (WS Port Words E) (spec:=unifSpec + (List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core)) (sgnW (S:=GeneralScheme.SignatureCore S.vp (P₀).core) 1)) (SkCost.qmForger S F base H pk) qs := by
  unfold SkCost.qmForger
  refine WCount.map (WCount.wrap0 (w := sgnW 1) _ ?_ (WCount.map
    (WCount.wrap0 (w := sgnW 1) _ ?_ (WCount.compileQ H ?_)) _)) _
  · rintro (n|e)
    · exact wCount_liftM_query _ _ le_rfl
    · simp only [Guarded.signingImpl]
      split
      · trivial
      · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · rintro (n|m)
    · exact wCount_liftM_query _ _ le_rfl
    · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · apply ((countBound_iff_wCount isSign _ _).mp (hs _)).wmono
    rintro (j|u|n|m) <;> simp [qw,isSign,sgnW]

private theorem sign_count (rand : PublicKeyCore (P₀).core → ProbComp S.Node) (pk : PublicKeyCore (P₀).core)
    (m : List SLHDSA.Byte) : WCount cost (Lazy.msgSignO (vp:=S.vp) rand pk m) 1 := by
  have rest (rr : S.Node) : WCount cost (Lazy.openSign P₀ (Lazy.msgG P₀) m pk.pkSeed pk.pkRoot rr) 0 := by
    apply wCount_of_isQueryBoundP (fun i => Lazy.kind i = .game)
    apply Ideal.Realize.np_openSign <;> intros <;> exact fun h => nomatch h
  have h := WCount.bind (pure_sample (sp := (Lazy.msgG P₀) + _) cost (fun _ => rfl) (rand pk)) (fun a =>
    WCount.bind (wCount_liftM_query (sp:=OS) cost (.inr (.inl (a,m))) (le_refl 1)) rest)
  exact h

private theorem open_count (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (port : Port → Words) (qs : ℕ) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    WCount (qw _ cost) (qMsgOpenW sufCheck (qPureBytesToInternal (ShakeApi.forgerAt S rand seeds F base port))) qs := by
  unfold qMsgOpenW
  apply (WCount.bind (WCount.liftQ (pure_sample cost (fun _ => rfl) seeds)) _ : WCount _ _ (0+qs)).mono (Nat.zero_add qs).le
  intro pk
  have key : WCount cost (Lazy.openKeygen P₀ (Lazy.msgG P₀) pk) 0 := by
    apply wCount_of_isQueryBoundP (fun i => Lazy.kind i = .game)
    apply Ideal.Realize.np_openKeygen <;> intros <;> exact fun h => nomatch h
  apply (WCount.bind (WCount.liftQ key) _ : WCount _ _ (0+qs)).mono (Nat.zero_add qs).le
  intro root
  apply (WCount.bind _ (m:=0) (fun _ => WCount.liftQ (wCount_pure _ _ 0)) : WCount _ _ (qs+0))
  unfold qRunForgerSig
  rw [SkCost.main_eq_any]
  apply WCount.wrap _ (w := sgnW 1) _ (wrapped_signs S base F qs hs port _) _
  rintro (n|m) log
  · change WCount cost ((fun u => (u,log)) <$> (liftM ((OS).query (.inl n)))) 0
    exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · simp only [QueryImpl.add_apply_inr,sigSignOracle,run_appendLog_apply]
    exact (WCount.bind (sign_count S base _ _ m)
      (fun sig => wCount_pure _ (sig,log ++ [⟨m,sig⟩]) 0) : WCount _ _ (1+0))

/-- Uniform in the public oracle and the ancillary SHAKE primitive family. -/
theorem native_count (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (port : Port → Words) (qs : ℕ) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    CountBound (fun i => isChallenge i = true)
      (qbPrfMsgWL sufCheck (qPureBytesToInternal (ShakeApi.forgerAt S rand seeds F base port))) qs := by
  let fee : (PS).Domain → ℕ := fun i => if i.isRight then 1 else 0
  apply (countBound_iff_wCount _ _ _).mpr
  unfold qbPrfMsgWL qLazyRun
  have inner := open_count S base F rand seeds port qs hs
  have outer : WCount (qw _ fee) (wrap0 (Lazy.interp (PublicHash.impl P₀))
      (Prod.fst <$> wrap Lazy.lazyImplR (qMsgOpenW sufCheck
        (qPureBytesToInternal (ShakeApi.forgerAt S rand seeds F base port))) [])) qs := by
    apply WCount.wrap0 _ (w:=cost) _ (WCount.map (WCount.wrap _ (w:=cost) _ inner _) _)
    · rintro (n|d|u|t)
      · exact wCount_liftM_query _ _ le_rfl
      · exact wCount_liftM_query _ _ le_rfl
      · exact pure_sample fee (fun _ => rfl) _
      · trivial
    · intro t s
      refine wCount_of_isQueryBoundP (fun i => Lazy.kind i = .game) _ _ ?_
      rcases t with n|d|a|h
      · simp [Lazy.lazyImplR,Lazy.kind,cost]
      · simp [Lazy.lazyImplR,Lazy.kind,cost]
      · rcases hc : s.lookup a with _|v
        · rw [Lazy.lazyImplR_sec_run_miss a s hc]; simp [Lazy.kind,cost]
        · rw [Lazy.lazyImplR_sec_run_hit a s v hc]; simp [cost,Lazy.kind]
      · simp [Lazy.lazyImplR,Lazy.kind,cost]
  exact outer.wmono (by rintro (j|n|d) <;> simp [isChallenge,qw,fee])

end Reduction.ShakePermutation.MsgSplit
#print axioms Reduction.ShakePermutation.MsgSplit.native_count

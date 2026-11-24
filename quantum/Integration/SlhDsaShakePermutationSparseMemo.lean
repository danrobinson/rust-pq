import Integration.SlhDsaShakePermutationSkSignature
import Integration.SlhDsaShakeXofTcrMachine

namespace Reduction.ShakePermutation.SparsePort.Memo
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ShakeApi
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] tcrTargets arityTargets
set_option linter.unusedSectionVars false
attribute [local instance] Lazy.openQ

variable (S : Sha2Set) (N : ℕ) (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)

private theorem scale {I A : Type} {sp : OracleSpec I} (w : I → ℕ) (p : OracleComp sp A)
    (a : ℕ) (hc : WCount w p a) : WCount (fun i => 483*w i) p (483*a) := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure x => trivial
  | query_bind t f ih =>
    rw [wCount_query_bind] at hc ⊢
    exact ⟨Nat.mul_le_mul_left 483 hc.1,fun u => by simpa only [Nat.mul_sub] using ih u (a-w t) (hc.2 u)⟩

theorem open_cost (ω₀ : RawTable S N) (cap : N ≤ rawCap S 67 65536) {α : Type}
    (tbl : SecretTable S.vp (ShakeApi.primitives S (extend ω₀)))
    (p : OracleComp (Lazy.OSpec (ShakeApi.primitives S (extend ω₀)) []ₒ) α) (q : ℕ)
    (hp : IsQueryBoundP p (fun t => Lazy.kind t = .hash) q) :
    EvalCost (fun H => simulateQ (qmImpl (hashPort S N (extend ω₀) (SkCost.table S N H)) tbl) p) (483*q) := by
  let w (t : (Lazy.OSpec (ShakeApi.primitives S (extend ω₀)) []ₒ).Domain) := if Lazy.kind t = .hash then 1 else 0
  refine EvalCost.simulateQ _ (fun i => 483*w i) ?_ p _ (scale w p q (wCount_of_isQueryBoundP _ p q hp))
  rintro (n|op|addr|hash)
  · exact EvalCost.const _
  · exact PEmpty.elim op
  · exact EvalCost.const _
  · exact SkCost.hash_cost S N (extend ω₀) cap hash

noncomputable def machine (ω₀ : RawTable S N) (n : ℕ)
    (st : Open.TcrP1State S.vp (ShakeApi.primitives S (extend ω₀))) (pk : S.Node) (H : Port → Words) :=
  qmMach (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) (SkCost.table S N H)) n
    (SkCost.qmForger S F (extend ω₀) H) st pk

theorem sign_eval (ω₀ : RawTable S N) (cap : N ≤ rawCap S 67 65536) (tbl : SecretTable S.vp (ShakeApi.primitives S (extend ω₀)))
    (pkSeed : (ShakeApi.primitives S (extend ω₀)).PkSeed) (root : (ShakeApi.primitives S (extend ω₀)).Y)
    (t : (unifSpec + (List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (ShakeApi.primitives S (extend ω₀)).core)).Domain)
    (s : G2Log (ShakeApi.primitives S (extend ω₀))) :
    EvalCost (fun H ↦ (qmImplS (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) (SkCost.table S N H)) tbl pkSeed root t).run s)
      (sgnW (483*Lazy.signHashes S.vp) t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ signRand S optRand₀ (extend ω₀) ⟨pkSeed, root⟩ >>= fun addrnd ↦
      lazyRandomizer s msg addrnd >>= fun R ↦
        simulateQ (qmImpl (hashPort S N (extend ω₀) (SkCost.table S N H)) tbl)
          (Lazy.openSign (ShakeApi.primitives S (extend ω₀)) []ₒ msg pkSeed root R) >>= fun sig ↦
          (pure (sig, (s : List (List SLHDSA.Byte × S.Node × S.Node)) ++ [(msg, addrnd, R)]) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Port) (Y := Words)
        (signRand S optRand₀ (extend ω₀) ⟨pkSeed, root⟩)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := Port) (Y := Words) (lazyRandomizer s msg addrnd))
        fun R ↦ EvalCost.bind (open_cost S N ω₀ cap tbl _ _ (ShakeApi.sign_hashes S N ω₀ msg pkSeed root R))
          fun sig ↦ EvalCost.const (X := Port) (Y := Words)
            (pure (sig, (s : List (List SLHDSA.Byte × S.Node × S.Node)) ++ [(msg, addrnd, R)]) : ProbComp _)
    exact h.mono (by simp)

/-- The class-TCR machine family makes at most `q + tcrMHashes qs` port
calls plus evaluations on every path. -/
theorem machine_cost (ω₀ : RawTable S N) (cap : N ≤ rawCap S 67 65536) (n : ℕ)
    (st : SecretTable S.vp (ShakeApi.primitives S (extend ω₀)) ×
      List ((ShakeApi.primitives S (extend ω₀)).AdrsKey × List (ShakeApi.primitives S (extend ω₀)).Y))
    (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (machine S N optRand₀ F ω₀ n st pk) (q + 483*tcrMHashes S.vp qs) := by
  unfold machine qmMach
  have hB : ∀ root : (ShakeApi.primitives S (extend ω₀)).Y, PUE (spec := unifSpec) cnt0 (fun H ↦
      close (qmImplS (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) (SkCost.table S N H)) st.1 pk root)
          (SkCost.qmForger S F (extend ω₀) H ⟨pk, root⟩) [] >>= fun z ↦
        liftU (classOut (ShakeApi.primitives S (extend ω₀)) n st.2 <$>
          simulateQ (qmImpl (hashPort S N (extend ω₀) (SkCost.table S N H)) st.1) (qmTail pk st.2 root z)))
      (q + qs * (483*Lazy.signHashes S.vp) + 483*(1 + Resources2.verifyHashes S.vp * 2)) := by
    intro root
    refine PUE.bind (PUE.close _ (sign_eval S N optRand₀ ω₀ cap st.1 pk root)
      (SkCost.pue_qmForger S F (extend ω₀) q qs _ hq hqs ⟨pk, root⟩) []) fun z ↦ ?_
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS (Port) Words E) _))
      (q := 0)
      ((open_cost S N ω₀ cap st.1 _ _ (ShakeApi.tail_hashes S N ω₀ pk st.2 root z)).map
        (classOut (ShakeApi.primitives S (extend ω₀)) n st.2)) fun o ↦ PUE.pure o 0
    simpa using h
  have h := PUE.liftU_bind (open_cost S N ω₀ cap st.1 _ _ (ShakeApi.keygen_hashes S N ω₀ pk)) hB
  refine h.mono ?_
  unfold tcrMHashes
  simp only [Nat.mul_add, Nat.mul_left_comm 483 qs]
  omega

noncomputable abbrev refForger (ω₀ T : RawTable S N) (H : Port → Words) :=
  F.at H (pureBytesAlg S.vp (refPrims S N ω₀ T) (ShakeApi.codec S (extend ω₀)) (signRand S optRand₀ (extend ω₀)) pkSeedDist₀)

theorem refMain (ω₀ T : RawTable S N) (H : Port → Words) :
    (qPureBytesToInternal (refForger S N optRand₀ pkSeedDist₀ F ω₀ T H)).main =
    SkCost.qmForger S F (extend ω₀) H := by
  funext pk
  simp only [refForger,qPureBytesToInternal,qToInternal,qPureBytesToTyped,QForger.wrapForger,
    PortForger.at,qmCSign_eq,qmCRead_eq,pureBytesView]
  rfl

theorem machine_oracle (ω₀ : RawTable S N) (n : ℕ)
    (st : SecretTable S.vp (ShakeApi.primitives S (extend ω₀)) ×
      List ((ShakeApi.primitives S (extend ω₀)).AdrsKey × List (ShakeApi.primitives S (extend ω₀)).Y))
    (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed) (π : Permutation) :
    machine S N optRand₀ F ω₀ n st pk (oracle π) =
      (qbTcrArM n (qPureBytesToInternal (SkCost.capped S optRand₀ pkSeedDist₀ F N π))).forge st pk := by
  let T := SkCost.table S N (oracle π)
  let real := ShakeApi.primitives S (extend T)
  let r := signRand S optRand₀ (extend ω₀)
  let r' := signRand S optRand₀ (extend T)
  let B := refForger S N optRand₀ pkSeedDist₀ F ω₀ T (oracle π)
  have tr := QInd.qMemoForge_tr (prims := refPrims S N ω₀ T) real.PRF real.PRFmsg
    (ShakeApi.codec S (extend ω₀)) r r' pkSeedDist₀ (fun _ => rfl) n B st pk
  refine Eq.trans ?_ tr.symm
  rw [qMemoForge_eq_qmMach]
  unfold B
  rw [refMain,← ShakeApi.refHash]
  qm_kernel_rfl

end Reduction.ShakePermutation.SparsePort.Memo
#print axioms Reduction.ShakePermutation.SparsePort.Memo.machine_cost
#print axioms Reduction.ShakePermutation.SparsePort.Memo.machine_oracle

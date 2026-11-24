import Integration.SlhDsaCompressionPrfBody

namespace Reduction.Compression.SkGame
open SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive QMsg Quantum
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed} {W : Type} [Fintype W]

def seedIndex {P A : Type} (pk : P) : ℕ ⊕ (P × A) → Prop
  | .inl _ => True
  | .inr d => d.1 = pk

/-- Every secret query of the signature reduction uses the public seed selected in its first draw. -/
theorem body_seed (w : WinCheck vp prims) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (pk : prims.PkSeed) : AllQueries (QG W (seedIndex pk)) (fun _ => True) (body w Q pk) := by
  let sp := PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y
  letI : HasQuery (publicHashSpec prims.core) (OracleComp sp) := ⟨fun q => pure (PublicHash.impl prims q)⟩
  let pred := fun {α : Type} (oa : OracleComp sp α) => AllQueries (seedIndex pk) (fun _ => True) oa
  have pureP {α : Type} (x : α) : pred (pure x) := trivial
  have bindP {α β : Type} (a : OracleComp sp α) (b : α → OracleComp sp β)
      (ha : pred a) (hb : ∀ x, pred (b x)) : pred (a >>= b) := allQ_bind ha (fun x _ => hb x)
  have key (a b : Adrs) (_ : b ∈ constructionAddresses vp) (_ : Sum.inl a ∈ childAdrs vp b) :
      pred (PRFScheme.functionQuery (pk,a) : OracleComp sp prims.Y) := allQ_query (sp₁ := sp) (seedIndex pk) (.inr (pk,a)) rfl
  unfold body
  refine allQ_bind (allQ_liftQ (allQ_liftProb (G := seedIndex pk) (fun _ => trivial) _)) fun sk _ =>
    allQ_bind (mid := fun _ => True) (allQ_liftQ ?_) fun root _ => allQ_bind (mid := fun _ => True) ?_ fun z _ => allQ_liftQ (pureP _)
  · exact keygenInternalWithSecretM_pred_of_ledger (@pred) (@pureP) (@bindP) prims.core key pk
      (fun _ _ _ => pureP _)
  · unfold qRunForgerSig
    apply allQ_wrap (G := fun _ => True) (G' := seedIndex pk) (goodOut := fun _ => True)
    · rintro (n|m) s _
      · exact allQ_map (good := seedIndex pk) (goodOut' := fun _ => True) (fun v => (v,s)) (fun _ _ => trivial) (allQ_liftProb (G := seedIndex pk) (fun _ => trivial) (liftM (unifSpec.query n)))
      · simp only [QueryImpl.add_apply_inr,sigSignOracle,appendLog,StateT.run_bind,StateT.run_monadLift,
          StateT.run_modify,StateT.run_pure,pure_bind,bind_assoc]
        refine allQ_bind (mid := fun _ => True) ?_ (fun _ _ => pureP _)
        refine allQ_bind (allQ_liftProb (G := seedIndex pk) (fun _ => trivial) _) fun rnd _ => ?_
        exact signInternalWithSecretRandomizerM_pred_of_ledger (@pred) (@pureP) (@bindP) prims.core key
          m pk root _ (fun _ _ _ => pureP _) (pureP _)
    · apply allQ_true_of
      rintro (j|t) <;> trivial

theorem checkedBody_seed (w : WinCheck vp prims) (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (pk : prims.PkSeed) : AllQueries (QG W (seedIndex pk)) (fun _ => True) (checkedBody w Q pk) := by
  apply allQ_wrap0 _ _ (body_seed w Q pk)
  rintro (n|⟨k,a⟩) hk
  · exact allQ_query (sp₁ := PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) (seedIndex pk) (.inl n) trivial
  · change k = pk at hk
    subst k
    by_cases ha : SkDom vp a
    · rw [Restrict.restrictImpl_inr_some _ (skRestrict_of_dom ha)]
      exact allQ_query (sp₁ := PRFScheme.PRFOracleSpec (prims.PkSeed × SkAdrs vp) prims.Y) (seedIndex pk) (.inr (pk, ⟨a,ha⟩)) rfl
    · have no : skRestrict vp prims (pk,a) = none := by simp [skRestrict,ha]
      rw [Restrict.restrictImpl_inr_none _ no]
      trivial

end Reduction.Compression.SkGame
#print axioms Reduction.Compression.SkGame.checkedBody_seed

import Integration.SlhDsaBridgePrf
import Ideal.Transport.AdvPrf
import Ideal.Transport.AdvMsg

/-!
# `hInd`: the quantum `PRF` distinguishers do not depend on the `PRF` component

NOT part of the default target; compiled like the other `Integration/*.lean` files.

`prfMachSuf_withPrf`, `prfMachEuf_withPrf` prove the hypothesis `hInd` of
`slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc` (`Integration/SlhDsaComposedEnc.lean`):

  `prfMachSuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H = prfMachSuf c optRand₀ pkSeedDist₀ F ω H`

(and the same for `prfMachEuf`), literally, for every world `ω`, `PRF` table `g`, port function
`H`.  Route: the quantum analogue of `Ideal.Transport.bPrfWC_setPrf` / `bPrfC_setPrf`.

* `primsΩ (ω.withPrf g)` is definitionally `setPrf (primsΩ ω) prf' (primsΩ ω).PRFmsg` with
  `prf' pk sk a = g pk sk (sha2AdrsKey a)`, the codec `codecR` is `trCodec` of the codec at `ω`,
  and the byte-level forger `F.at H _` has the same program at both bundles.
* Generic plumbing (`wrap0_wrap0`, `wrap_wrap0`, `wrap_map`, `wrap_map_state`): the classical
  wrappers around a quantum machine compose into one stateful handler; related handlers give
  related wrapped machines.
* `wrap_qPureBytesToInternal_tr`: the internal quantum forger `qPureBytesToInternal` over
  `setPrf prims prf pm`, run in any harness whose signing handler is related by `trSig`, equals
  the run over `prims` up to `trSig` on the output.  Instances `qRunForgerSig_tr`,
  `qRunForger_tr`.
* `qbPrfW_setPrf`, `qbPrfWC_setPrf`, `qbPrf_setPrf`, `qbPrfC_setPrf`: the four quantum machines
  (signing via the classical `bSignW_tr` / `bSignC_tr`; final checks via `sufCheck_setPrf` /
  `harnessValid_setPrf`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Reduction.QInd

variable {W : Type} [Fintype W] {α β γ : Type}
variable {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃}
  {τ σ σ' : Type}

theorem wrap0_liftQ_bind (h : QueryImpl spec₁ (OracleComp (unifSpec + spec₂)))
    (x : OracleComp spec₁ γ) (k : γ → QOC W spec₁ α) :
    wrap0 h (liftQ x >>= k) = liftQ (simulateQ h x) >>= fun a => wrap0 h (k a) := by
  induction x using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k' ih =>
    rw [liftQ_query_bind, bind_assoc, wrap0_query_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, liftQ_bind, bind_assoc, ih]

theorem wrap_liftQ_bind (implB : QueryImpl spec₁ (StateT τ (OracleComp (unifSpec + spec₂))))
    (x : OracleComp spec₁ γ) (k : γ → QOC W spec₁ α) (t : τ) :
    wrap implB (liftQ x >>= k) t =
      liftQ ((simulateQ implB x).run t) >>= fun z => wrap implB (k z.1) z.2 := by
  induction x using OracleComp.inductionOn generalizing t with
  | pure a => simp
  | query_bind q k' ih =>
    rw [liftQ_query_bind, bind_assoc, wrap_query_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liftQ_bind, bind_assoc, ih]

theorem wrap0_wrap0 (h' : QueryImpl spec₁ (OracleComp (unifSpec + spec₂)))
    (h : QueryImpl (unifSpec + spec₂) (OracleComp (unifSpec + spec₃))) (P : QOC W spec₁ α) :
    wrap0 h (wrap0 h' P) = wrap0 (fun q => simulateQ h (h' q)) P := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | q
    · rw [wrap0_instr_bind, wrap0_instr_bind, wrap0_instr_bind]
      simp only [ih]
    · rw [wrap0_query_bind, wrap0_liftQ_bind, wrap0_query_bind]
      simp only [ih]

theorem wrap_wrap0 (h : QueryImpl spec₁ (OracleComp (unifSpec + spec₂)))
    (implB : QueryImpl (unifSpec + spec₂) (StateT τ (OracleComp (unifSpec + spec₃))))
    (P : QOC W spec₁ α) (t : τ) :
    wrap implB (wrap0 h P) t = wrap (fun q => simulateQ implB (h q)) P t := by
  induction P using OracleComp.inductionOn generalizing t with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [wrap0_instr_bind, wrap_instr_bind, wrap_instr_bind]
      simp only [ih]
    · rw [wrap0_query_bind, wrap_liftQ_bind, wrap_query_bind]
      simp only [ih]

theorem wrap0_map (h : QueryImpl spec₁ (OracleComp (unifSpec + spec₂))) (f : α → β)
    (P : QOC W spec₁ α) : wrap0 h (f <$> P) = f <$> wrap0 h P := by
  unfold wrap0; rw [simulateQ_map]

theorem wrap_map (implB : QueryImpl spec₁ (StateT τ (OracleComp (unifSpec + spec₂)))) (f : α → β)
    (P : QOC W spec₁ α) (t : τ) :
    wrap implB (f <$> P) t = (fun z => (f z.1, z.2)) <$> wrap implB P t := by
  unfold wrap; rw [simulateQ_map, StateT.run_map]

theorem liftQ_map (f : α → β) (x : OracleComp spec₁ α) :
    (liftQ (f <$> x) : QOC W spec₁ β) = f <$> liftQ x := by
  unfold liftQ; rw [simulateQ_map]

/-- Related stateful handlers give related wrapped machines. -/
theorem wrap_map_state (f : σ → σ')
    (impl : QueryImpl spec₁ (StateT σ (OracleComp (unifSpec + spec₂))))
    (impl' : QueryImpl spec₁ (StateT σ' (OracleComp (unifSpec + spec₂))))
    (h : ∀ t s, (impl' t).run (f s) = (fun z => (z.1, f z.2)) <$> (impl t).run s)
    (P : QOC W spec₁ α) (s : σ) :
    wrap impl' P (f s) = (fun z => (z.1, f z.2)) <$> wrap impl P s := by
  induction P using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [wrap_instr_bind, wrap_instr_bind, map_bind]
      simp only [ih]
    · rw [wrap_query_bind, wrap_query_bind, h, liftQ_map, bind_map_left, map_bind]
      simp only [ih]


section Forger
open Ideal.Transport

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- The same byte-level quantum forger, read as a forger against the scheme over
`setPrf prims prf pm`. -/
def trB (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    QForger W (pureBytesAlg vp (setPrf prims prf pm) (trCodec _ prf pm codec) optRand'
      pkSeedDist) :=
  ⟨B.main, B.ρ₀, B.posSemidef, B.trace_eq_one⟩

theorem readForgery_pure_tr (out : (List Byte × List Byte) × Option (List Byte)) :
    Guarded.readForgery pureEncode ([], constSig default)
        (Coded.readForgery
          (pureBytesView vp (setPrf prims prf pm) (trCodec _ prf pm codec) optRand' pkSeedDist)
          (Except.error (External.Error.contextTooLong 0)) out) =
      ((Guarded.readForgery pureEncode ([], constSig default)
          (Coded.readForgery (pureBytesView vp prims codec optRand pkSeedDist)
            (Except.error (External.Error.contextTooLong 0)) out)).1,
        trSig _ prf pm (Guarded.readForgery pureEncode ([], constSig default)
          (Coded.readForgery (pureBytesView vp prims codec optRand pkSeedDist)
            (Except.error (External.Error.contextTooLong 0)) out)).2) := by
  obtain ⟨mc, o⟩ := out
  simp only [Coded.readForgery, pureBytesView]
  cases o with
  | none =>
    simp only [decodePureSig, Option.getD_none, Guarded.readForgery]
    cases pureEncode mc <;> exact congrArg (Prod.mk []) (constSig_tr prf pm default)
  | some raw =>
    simp only [decodePureSig, decodeSignature_tr]
    cases decodeSignature vp codec raw with
    | error e =>
      simp only [Guarded.readForgery]
      cases pureEncode mc <;> exact congrArg (Prod.mk []) (constSig_tr prf pm default)
    | ok sg =>
      simp only [Guarded.readForgery]
      cases pureEncode mc
      · exact congrArg (Prod.mk []) (constSig_tr prf pm default)
      · rfl

/-- **The internal quantum forger built from a byte-level quantum forger, over
`setPrf prims prf pm`, run against any stateful signing handler, is the one over `prims` up to
`trSig`**, when the two handlers are related by `trSig` on the answers and a map `f` of states. -/
theorem wrap_qPureBytesToInternal_tr {ι : Type} {spec : OracleSpec ι} {σ σ' : Type} (f : σ → σ')
    (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (impl : QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT σ (OracleComp (unifSpec + spec))))
    (impl' : QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm))
      (StateT σ' (OracleComp (unifSpec + spec))))
    (h : ∀ m s, (impl' m).run (f s) = (fun z => (trSig _ prf pm z.1, f z.2)) <$> (impl m).run s)
    (pk : PublicKeyCore prims.core) (s : σ) :
    wrap ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
          (StateT σ' (OracleComp (unifSpec + spec))) + impl')
        ((qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B)).main
          (trPk _ prf pm pk)) (f s) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), f z.2)) <$>
        wrap ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
          (StateT σ (OracleComp (unifSpec + spec))) + impl)
          ((qPureBytesToInternal B).main pk) s := by
  unfold qPureBytesToInternal qToInternal qPureBytesToTyped QForger.wrapForger trB
  dsimp only
  simp only [wrap0_map, wrap0_wrap0, wrap_map, wrap_wrap0]
  have hpk : (pureBytesView vp (setPrf prims prf pm) (trCodec _ prf pm codec) optRand'
      pkSeedDist).encPk (trPk _ prf pm pk) = (pureBytesView vp prims codec optRand pkSeedDist).encPk pk :=
    encodePublicKey_tr _ prf pm codec pk
  rw [hpk, wrap_map_state f _ _ ?_]
  · simp only [Functor.map_map]
    congr 1
    funext z
    exact Prod.ext (readForgery_pure_tr prf pm codec optRand optRand' pkSeedDist z.1) rfl
  · intro t s
    rcases t with n | mc
    · simp [Coded.signingImpl, Guarded.signingImpl]
    · simp only [Coded.signingImpl, simulateQ_map]
      simp only [simulateQ_HasQuery_query, Guarded.signingImpl]
      cases pureEncode mc with
      | error x => simp [pureBytesView, encodePureSig]; rfl
      | ok m =>
        simp only [simulateQ_map, simulateQ_HasQuery_query, QueryImpl.add_apply_inr, StateT.run_map,
          h, Functor.map_map]
        simp only [pureBytesView, encodePureSig]
        congr 1
        funext a
        exact Prod.ext (congrArg some (encodeSignature_tr vp _ prf pm codec a.1)) rfl

theorem qRunForgerSig_tr {ι : Type} {spec : OracleSpec ι}
    (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core))
    (sign' : List Byte →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m, sign' m = trSig _ prf pm <$> sign m) :
    qRunForgerSig (prims := setPrf prims prf pm)
        (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B))
        (trPk _ prf pm pk) sign' =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), trLog prf pm z.2)) <$>
        qRunForgerSig (qPureBytesToInternal B) pk sign := by
  unfold qRunForgerSig
  refine wrap_qPureBytesToInternal_tr prf pm codec optRand optRand' pkSeedDist (trLog prf pm) B
    _ _ ?_ pk []
  intro m s
  simp only [sigSignOracle, run_appendLog_apply, hs]
  simp [trLog]

theorem qRunForger_tr {ι : Type} {spec : OracleSpec ι}
    (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core))
    (sign' : List Byte →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm)))
    (hs : ∀ m, sign' m = trSig _ prf pm <$> sign m) :
    qRunForger ((qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B)).main
        (trPk _ prf pm pk)) sign' =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        qRunForger ((qPureBytesToInternal B).main pk) sign := by
  unfold qRunForger harnessImpl
  refine wrap_qPureBytesToInternal_tr prf pm codec optRand optRand' pkSeedDist id B
    _ _ ?_ pk []
  intro m s
  simp only [PQ.Interactive.harnessSignOracle, hs, id]
  simp

end Forger

section Prf
open Ideal.Transport

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf prims.PRFmsg) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf prims.PRFmsg pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)

include hopt in
theorem qbPrfW_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qbPrfW (prims := setPrf prims prf prims.PRFmsg) sufCheck
        (qPureBytesToInternal (trB prf prims.PRFmsg codec optRand optRand' pkSeedDist B)) =
      qbPrfW sufCheck (qPureBytesToInternal B) := by
  unfold qbPrfW
  refine bind_congr fun pkSeed => ?_
  refine bind_congr fun skPrf => ?_
  refine bind_congr_k (by krfl) fun root => ?_
  have h := qRunForgerSig_tr prf prims.PRFmsg codec optRand optRand' pkSeedDist B ⟨pkSeed, root⟩
    (bSignW optRand ⟨pkSeed, root⟩ skPrf) _
    (fun m => bSignW_tr prims prf optRand optRand' hopt ⟨pkSeed, root⟩ skPrf m)
  refine (bind_congr_k h fun z => rfl).trans ?_
  rw [bind_map_left]
  refine bind_congr fun z => ?_
  have hv := sufCheck_setPrf prims prf prims.PRFmsg ⟨pkSeed, root⟩ z.1 z.2
  simp only [trPk_mk] at hv
  rw [hv]

include hopt in
theorem qbPrfWC_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qbPrfWC (prims := setPrf prims prf prims.PRFmsg) sufCheck
        (qPureBytesToInternal (trB prf prims.PRFmsg codec optRand optRand' pkSeedDist B)) =
      qbPrfWC sufCheck (qPureBytesToInternal B) := by
  unfold qbPrfWC
  rw [qbPrfW_setPrf prf codec optRand optRand' hopt pkSeedDist B]
  rfl

include hopt in
theorem qbPrf_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qbPrf (prims := setPrf prims prf prims.PRFmsg)
        (qPureBytesToInternal (trB prf prims.PRFmsg codec optRand optRand' pkSeedDist B)) =
      qbPrf (qPureBytesToInternal B) := by
  unfold qbPrf
  refine bind_congr fun pkSeed => ?_
  refine bind_congr fun skPrf => ?_
  refine bind_congr_k (by krfl) fun root => ?_
  have h := qRunForger_tr prf prims.PRFmsg codec optRand optRand' pkSeedDist B ⟨pkSeed, root⟩
    (bSignC optRand ⟨pkSeed, root⟩ skPrf) _
    (fun m => bSignC_tr prims prf optRand optRand' hopt ⟨pkSeed, root⟩ skPrf m)
  refine (bind_congr_k h fun z => rfl).trans ?_
  rw [bind_map_left]
  refine bind_congr fun z => ?_
  have hv := harnessValid_setPrf prims prf prims.PRFmsg ⟨pkSeed, root⟩ z.2 z.1.1 z.1.2
  simp only [trPk_mk] at hv
  rw [hv]

include hopt in
theorem qbPrfC_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qbPrfC (prims := setPrf prims prf prims.PRFmsg)
        (qPureBytesToInternal (trB prf prims.PRFmsg codec optRand optRand' pkSeedDist B)) =
      qbPrfC (qPureBytesToInternal B) := by
  unfold qbPrfC
  rw [qbPrf_setPrf prf codec optRand optRand' hopt pkSeedDist B]
  rfl

end Prf

section Omega

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **`hInd`, SUF-CMA.** -/
theorem prfMachSuf_withPrf (ω : Ω128 c) (g : Bytes Link.vp.params.n → Bytes Link.vp.params.n →
      Bytes 22 → Bytes Link.vp.params.n) (H : EncX c → EncY) :
    prfMachSuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H = prfMachSuf c optRand₀ pkSeedDist₀ F ω H :=
  qbPrfWC_setPrf (prims := primsΩ ω) (fun pk sk a => g pk sk (Concrete.sha2AdrsKey a))
    (codecR ω.toRand) (optRandOf c optRand₀ ω) (optRandOf c optRand₀ (ω.withPrf g)) (fun _ => rfl)
    pkSeedDist₀ (F.at H (algΩ c optRand₀ pkSeedDist₀ ω))

/-- **`hInd`, EUF-CMA.** -/
theorem prfMachEuf_withPrf (ω : Ω128 c) (g : Bytes Link.vp.params.n → Bytes Link.vp.params.n →
      Bytes 22 → Bytes Link.vp.params.n) (H : EncX c → EncY) :
    prfMachEuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H = prfMachEuf c optRand₀ pkSeedDist₀ F ω H :=
  qbPrfC_setPrf (prims := primsΩ ω) (fun pk sk a => g pk sk (Concrete.sha2AdrsKey a))
    (codecR ω.toRand) (optRandOf c optRand₀ ω) (optRandOf c optRand₀ (ω.withPrf g)) (fun _ => rfl)
    pkSeedDist₀ (F.at H (algΩ c optRand₀ pkSeedDist₀ ω))

end Omega
end Reduction.QInd

#print axioms Reduction.QInd.wrap0_wrap0
#print axioms Reduction.QInd.wrap_wrap0
#print axioms Reduction.QInd.wrap_map_state
#print axioms Reduction.QInd.readForgery_pure_tr
#print axioms Reduction.QInd.wrap_qPureBytesToInternal_tr
#print axioms Reduction.QInd.qRunForgerSig_tr
#print axioms Reduction.QInd.qRunForger_tr
#print axioms Reduction.QInd.qbPrfW_setPrf
#print axioms Reduction.QInd.qbPrfWC_setPrf
#print axioms Reduction.QInd.qbPrf_setPrf
#print axioms Reduction.QInd.qbPrfC_setPrf
#print axioms Reduction.QInd.prfMachSuf_withPrf
#print axioms Reduction.QInd.prfMachEuf_withPrf

import Integration.SlhDsaBridgeInd

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped Kronecker ComplexOrder
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Reduction.QMsg

section AllQ
variable {α β : Type} {ι₁ ι₂ : Type} {sp₁ : OracleSpec ι₁} {sp₂ : OracleSpec ι₂}

lemma allQ_pure (good : ι₁ → Prop) (goodOut : α → Prop) (a : α) :
    AllQueries good goodOut (pure a : OracleComp sp₁ α) ↔ goodOut a := Iff.rfl

lemma allQ_query_bind (good : ι₁ → Prop) (goodOut : α → Prop) (t : ι₁)
    (k : sp₁.Range t → OracleComp sp₁ α) :
    AllQueries good goodOut (liftM (sp₁.query t) >>= k) ↔ good t ∧ ∀ r, AllQueries good goodOut (k r) :=
  Iff.rfl

lemma allQ_query (good : ι₁ → Prop) (t : ι₁) (h : good t) :
    AllQueries good (fun _ ↦ True) (liftM (sp₁.query t) : OracleComp sp₁ _) := by
  rw [← bind_pure (liftM (sp₁.query t) : OracleComp sp₁ _)]
  exact ⟨h, fun _ ↦ trivial⟩

lemma allQ_bind {good : ι₁ → Prop} {mid : α → Prop} {goodOut : β → Prop} {P : OracleComp sp₁ α}
    {f : α → OracleComp sp₁ β} (hP : AllQueries good mid P)
    (hf : ∀ a, mid a → AllQueries good goodOut (f a)) : AllQueries good goodOut (P >>= f) := by
  induction P using OracleComp.inductionOn with
  | pure a => rw [pure_bind]; exact hf a hP
  | query_bind t k ih =>
    rw [bind_assoc]
    exact ⟨hP.1, fun r ↦ ih r (hP.2 r)⟩

lemma allQ_mono {good good' : ι₁ → Prop} {goodOut goodOut' : α → Prop}
    (hg : ∀ t, good t → good' t) (ho : ∀ a, goodOut a → goodOut' a) {P : OracleComp sp₁ α}
    (hP : AllQueries good goodOut P) : AllQueries good' goodOut' P := by
  induction P using OracleComp.inductionOn with
  | pure a => exact ho a hP
  | query_bind t k ih => exact ⟨hg t hP.1, fun r ↦ ih r (hP.2 r)⟩

lemma allQ_map {good : ι₁ → Prop} {goodOut : α → Prop} {goodOut' : β → Prop} (f : α → β)
    (hf : ∀ a, goodOut a → goodOut' (f a)) {P : OracleComp sp₁ α}
    (hP : AllQueries good goodOut P) : AllQueries good goodOut' (f <$> P) := by
  rw [map_eq_bind_pure_comp]
  exact allQ_bind hP fun a ha ↦ hf a ha

lemma allQ_true_of {good : ι₁ → Prop} (hg : ∀ t, good t) (P : OracleComp sp₁ α) :
    AllQueries good (fun _ ↦ True) P := by
  induction P using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih => exact ⟨hg t, ih⟩

lemma allQ_simulateQ {good₁ : ι₁ → Prop} {good₂ : ι₂ → Prop} {goodOut : α → Prop}
    (h : QueryImpl sp₁ (OracleComp sp₂))
    (hh : ∀ t, good₁ t → AllQueries good₂ (fun _ ↦ True) (h t)) {P : OracleComp sp₁ α}
    (hP : AllQueries good₁ goodOut P) : AllQueries good₂ goodOut (simulateQ h P) := by
  induction P using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact hP
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact allQ_bind (hh t hP.1) fun r _ ↦ ih r (hP.2 r)

lemma allQ_simulateQ_state {σ : Type} {good₁ : ι₁ → Prop} {good₂ : ι₂ → Prop} {goodOut : α → Prop}
    (h : QueryImpl sp₁ (StateT σ (OracleComp sp₂)))
    (hh : ∀ t s, good₁ t → AllQueries good₂ (fun _ ↦ True) ((h t).run s)) {P : OracleComp sp₁ α}
    (hP : AllQueries good₁ goodOut P) :
    ∀ s, AllQueries good₂ (fun z ↦ goodOut z.1) ((simulateQ h P).run s) := by
  induction P using OracleComp.inductionOn with
  | pure a => intro s; rw [simulateQ_pure, StateT.run_pure]; exact hP
  | query_bind t k ih =>
    intro s
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQ_bind (hh t s hP.1) fun r _ ↦ ih r.1 (hP.2 r.1) r.2

end AllQ

section QAllQ
variable {W : Type} [Fintype W] {α : Type} {ι ι' : Type} {spec : OracleSpec ι}
  {spec' : OracleSpec ι'} {τ : Type}

/-- A predicate on the classical indices of a quantum machine (instruments always allowed). -/
def QG (W : Type) [Fintype W] (G : ι → Prop) : InstrIdx W ⊕ ι → Prop
  | .inl _ => True
  | .inr t => G t

lemma allQ_liftQ {G : ι → Prop} {goodOut : α → Prop} {ob : OracleComp spec α}
    (h : AllQueries G goodOut ob) : AllQueries (QG W G) goodOut (liftQ ob : QOC W spec α) :=
  allQ_simulateQ _ (fun t ht ↦ allQ_query (QG W G) (Sum.inr t) ht) h

lemma allQ_wrap0 {G : ι → Prop} {G' : (unifSpec + spec').Domain → Prop} {goodOut : α → Prop}
    (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    (hh : ∀ t, G t → AllQueries G' (fun _ ↦ True) (h t)) {Q : QOC W spec α}
    (hQ : AllQueries (QG W G) goodOut Q) :
    AllQueries (QG W G') goodOut (wrap0 h Q) := by
  refine allQ_simulateQ _ ?_ hQ
  rintro (j | t) ht
  · exact allQ_query _ (Sum.inl j) trivial
  · exact allQ_liftQ (hh t ht)

lemma allQ_wrap {G : ι → Prop} {G' : (unifSpec + spec').Domain → Prop} {goodOut : α → Prop}
    (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    (hh : ∀ t s, G t → AllQueries G' (fun _ ↦ True) ((implB t).run s)) {Q : QOC W spec α}
    (hQ : AllQueries (QG W G) goodOut Q) (s : τ) :
    AllQueries (QG W G') (fun z ↦ goodOut z.1) (wrap implB Q s) := by
  refine allQ_simulateQ_state _ ?_ hQ s
  rintro (j | t) s ht
  · exact allQ_map _ (fun _ _ ↦ trivial) (allQ_query _ (Sum.inl j) trivial)
  · exact allQ_liftQ (hh t s ht)

end QAllQ

section Lift
variable {α : Type} {ι : Type} {sp : OracleSpec ι}

lemma allQ_liftProb {G : ℕ ⊕ ι → Prop} (hG : ∀ n, G (.inl n)) (pc : ProbComp α) :
    AllQueries G (fun _ ↦ True) (liftM pc : OracleComp (unifSpec + sp) α) := by
  induction pc using OracleComp.inductionOn with
  | pure a => simp; trivial
  | query_bind n k ih =>
    rw [liftM_bind]
    have e : (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (unifSpec + sp) _) =
        liftM ((unifSpec + sp).query (.inl n)) := rfl
    rw [e]
    exact ⟨hG n, ih⟩

end Lift

section Chain
variable {W : Type} [Fintype W] (L : ℕ)

/-- Byte-level signing queries within the cap. -/
def Gbyte : ℕ ⊕ (List Byte × List Byte) → Prop
  | .inl _ => True
  | .inr mc => mc.1.length + mc.2.length + 2 ≤ L

/-- Internal signing queries within the cap. -/
def Gint : ℕ ⊕ List Byte → Prop
  | .inl _ => True
  | .inr m => m.length ≤ L

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E]

theorem allQ_compileQ (c : Caps) (H : X → Y)
    (P : QOC ((X × Y) × E) (portSpec + (unifSpec + ((List Byte × List Byte) →ₒ Option (List Byte))))
      ((List Byte × List Byte) × Option (List Byte)))
    (hP : AllQueries (capIdx c) (capOut c) P) :
    AllQueries (QG (WS X Y E) (Gbyte c.ml)) (fun _ ↦ True) (compileQ H P) := by
  refine allQ_mono (fun _ h ↦ h) (fun _ _ ↦ trivial) (allQ_simulateQ _ ?_ hP)
  rintro (j | ⟨⟩ | n | mc) ht
  · exact allQ_query _ (Sum.inl _) trivial
  · exact allQ_map _ (fun _ _ ↦ trivial) (allQ_query _ (Sum.inl _) trivial)
  · exact allQ_query (QG (WS X Y E) (Gbyte c.ml)) (Sum.inr (Sum.inl n)) trivial
  · exact allQ_query (QG (WS X Y E) (Gbyte c.ml)) (Sum.inr (Sum.inr mc)) ht

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
  [Inhabited prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
  {optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}

theorem allQ_qPureBytesToInternal (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist))
    (hB : ∀ pk, AllQueries (QG W (Gbyte L)) (fun _ ↦ True) (B.main pk))
    (pk : PublicKeyCore prims.core) :
    AllQueries (QG W (Gint L)) (fun _ ↦ True) ((qPureBytesToInternal B).main pk) := by
  unfold qPureBytesToInternal qToInternal qPureBytesToTyped QForger.wrapForger
  dsimp only
  refine allQ_map (goodOut := fun _ ↦ True) _ (fun _ _ ↦ trivial)
    (allQ_wrap0 (G := Gbyte L) _ ?_
      (allQ_map (goodOut := fun _ ↦ True) _ (fun _ _ ↦ trivial)
        (allQ_wrap0 (G := Gbyte L) _ ?_ (hB _))))
  · rintro (n | mc) ht
    · exact allQ_query (Gint L) (Sum.inl n) trivial
    · simp only [Guarded.signingImpl]
      rcases he : pureEncode mc with x | m
      · trivial
      · refine allQ_map _ (fun _ _ ↦ trivial) (allQ_query (Gint L) (Sum.inr m) ?_)
        have h := (encodePureMessage_ok_iff mc.2 mc.1 m).1 he
        show m.length ≤ L
        have ht' : mc.1.length + mc.2.length + 2 ≤ L := ht
        rw [h.2]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
  · rintro (n | mc) ht
    · exact allQ_query (Gbyte L) (Sum.inl n) trivial
    · exact allQ_map _ (fun _ _ ↦ trivial) (allQ_query (Gbyte L) (Sum.inr mc) ht)

end Chain

section Open
open Lazy

/-- Constrain only the game queries. -/
def GameG {A B : Type} (P : A → Prop) : ℕ ⊕ (A ⊕ B) → Prop
  | .inr (.inl a) => P a
  | _ => True

variable {vp : ValidatedParams} (prims : Primitives vp.params) {ι : Type} (G : OracleSpec ι)
  (P : ι → Prop)

theorem allQ_openQ (q : (publicHashSpec prims.core).Domain) :
    AllQueries (GameG P) (fun _ ↦ True)
      ((openQ prims G).query q : OracleComp (OSpec prims G) _) :=
  allQ_query (GameG P) (Sum.inr (Sum.inr (Sum.inr q))) trivial

theorem allQ_secQ (a : Adrs) :
    AllQueries (GameG P) (fun _ ↦ True) (secQ prims G a) :=
  allQ_query (GameG P) (Sum.inr (Sum.inr (Sum.inl _))) trivial

theorem allQ_openKeygen (pkSeed : prims.PkSeed) :
    AllQueries (GameG P) (fun _ ↦ True) (Lazy.openKeygen prims G pkSeed) := by
  unfold Lazy.openKeygen
  exact keygenInternalWithSecretM_pred_of_ledger
    (m := OracleComp (OSpec prims G)) (fun {α} oa ↦ AllQueries (GameG P) (fun _ ↦ True) oa)
    (fun _ ↦ trivial) (fun _ _ h1 h2 ↦ allQ_bind h1 fun x _ ↦ h2 x) prims.core
    (fun a _ _ _ ↦ allQ_secQ prims G P a) pkSeed
    (fun a _ xs ↦ allQ_openQ prims G P _)

theorem allQ_openSign (msg : List Byte) (pkSeed : prims.PkSeed) (pkRoot R : prims.Y) :
    AllQueries (GameG P) (fun _ ↦ True) (Lazy.openSign prims G msg pkSeed pkRoot R) := by
  unfold Lazy.openSign
  exact signInternalWithSecretRandomizerM_pred_of_ledger
    (m := OracleComp (OSpec prims G)) (fun {α} oa ↦ AllQueries (GameG P) (fun _ ↦ True) oa)
    (fun _ ↦ trivial) (fun _ _ h1 h2 ↦ allQ_bind h1 fun x _ ↦ h2 x) prims.core
    (fun a _ _ _ ↦ allQ_secQ prims G P a) msg pkSeed pkRoot R
    (fun a _ xs ↦ allQ_openQ prims G P _) (allQ_openQ prims G P _)

theorem allQ_msgSignO [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.Y] [DecidableEq prims.Y] [DecidableEq prims.PkSeed]
    [DecidableEq prims.AdrsKey] [Inhabited prims.Y] (L : ℕ)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (pk : PublicKeyCore prims.core)
    (m : List Byte) (hm : m.length ≤ L) :
    AllQueries (GameG fun d : prims.Y × List Byte ↦ d.2.length ≤ L) (fun _ ↦ True)
      (Lazy.msgSignO optRand pk m) := by
  unfold Lazy.msgSignO
  refine allQ_bind (allQ_liftProb (fun _ ↦ trivial) _) fun addrnd _ ↦ ?_
  refine allQ_bind (allQ_query _ (Sum.inr (Sum.inl (addrnd, m))) hm) fun R _ ↦ ?_
  exact allQ_openSign prims (msgG prims) _ m pk.pkSeed pk.pkRoot R

/-- Constrain only the game queries (closed interface). -/
def Gfin {A : Type} (P : A → Prop) : ℕ ⊕ A → Prop
  | .inr a => P a
  | _ => True

section Machine
variable {W : Type} [Fintype W]
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.Y] [DecidableEq prims.Y] [DecidableEq prims.PkSeed]
    [DecidableEq prims.AdrsKey] [Inhabited prims.Y] (L : ℕ)
  {optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}

theorem allQ_qMsgOpenW (w : WinCheck vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, AllQueries (QG W (Gint L)) (fun _ ↦ True) (Q.main pk)) :
    AllQueries (QG W (GameG fun d : prims.Y × List Byte ↦ d.2.length ≤ L)) (fun _ ↦ True)
      (qMsgOpenW w Q) := by
  unfold qMsgOpenW
  refine allQ_bind (allQ_liftQ (allQ_liftProb (fun _ ↦ trivial) _)) fun pkSeed _ ↦ ?_
  refine allQ_bind (allQ_liftQ (allQ_openKeygen prims _ _ pkSeed)) fun root _ ↦ ?_
  refine allQ_bind (allQ_wrap (G := Gint L) _ ?_ (hQ _) []) fun z _ ↦ allQ_liftQ trivial
  rintro (n | m) s ht
  · simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
    exact allQ_bind (allQ_query _ (Sum.inl n) trivial) fun _ _ ↦ trivial
  · simp only [QueryImpl.add_apply_inr, sigSignOracle, run_appendLog_apply]
    exact allQ_bind (allQ_msgSignO prims L optRand _ m ht) fun _ _ ↦ trivial

theorem allQ_qMsgOpen (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, AllQueries (QG W (Gint L)) (fun _ ↦ True) (Q.main pk)) :
    AllQueries (QG W (GameG fun d : prims.Y × List Byte ↦ d.2.length ≤ L)) (fun _ ↦ True)
      (qMsgOpen Q) := by
  unfold qMsgOpen qRunForger harnessImpl
  refine allQ_bind (allQ_liftQ (allQ_liftProb (fun _ ↦ trivial) _)) fun pkSeed _ ↦ ?_
  refine allQ_bind (allQ_liftQ (allQ_openKeygen prims _ _ pkSeed)) fun root _ ↦ ?_
  refine allQ_bind (allQ_wrap (G := Gint L) _ ?_ (hQ _) []) fun z _ ↦ allQ_liftQ trivial
  rintro (n | m) s ht
  · simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
    exact allQ_bind (allQ_query _ (Sum.inl n) trivial) fun _ _ ↦ trivial
  · simp only [QueryImpl.add_apply_inr, PQ.Interactive.harnessSignOracle, StateT.run_bind,
      StateT.run_monadLift, StateT.run_modify, bind_assoc, pure_bind]
    exact allQ_bind (allQ_msgSignO prims L optRand _ m ht) fun _ _ ↦ trivial

end Machine

end Open

section LazyQ
open Lazy
variable {W : Type} [Fintype W] {α ι κ : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κ}
  {D V : Type} [DecidableEq D] [SampleableType V]

theorem allQ_qLazyRun (hI : QueryImpl hspec Id) (P : ι → Prop)
    (X : QOC W (RSpec gspec D V hspec) α)
    (hX : AllQueries (QG W (GameG P)) (fun _ ↦ True) X) :
    AllQueries (QG W (Gfin P)) (fun _ ↦ True) (qLazyRun hI X) := by
  unfold qLazyRun
  refine allQ_wrap0 (G := GameG P) _ ?_
    (allQ_map (goodOut := fun _ ↦ True) _ (fun _ _ ↦ trivial)
      (allQ_wrap (G := GameG P) _ ?_ hX []))
  · rintro (n | t | d | q) ht
    · exact allQ_query (Gfin P) (Sum.inl n) trivial
    · exact allQ_query (Gfin P) (Sum.inr t) ht
    · exact allQ_liftProb (fun _ ↦ trivial) _
    · trivial
  · rintro (n | t | d | q) s ht
    · exact allQ_bind (allQ_query _ (Sum.inl n) trivial) fun _ _ ↦ trivial
    · exact allQ_bind (allQ_query (GameG P) (Sum.inr (Sum.inl t)) ht) fun _ _ ↦ trivial
    · simp only [lazyImplR, StateT.run_bind, StateT.run_get, pure_bind]
      cases List.lookup d s with
      | some v => trivial
      | none =>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure]
        exact allQ_bind (mid := fun _ ↦ True)
          (allQ_bind (mid := fun _ ↦ True) (allQ_query _ (Sum.inr (Sum.inr (Sum.inl ()))) trivial)
          fun _ _ ↦ trivial) fun _ _ ↦ allQ_bind (mid := fun _ ↦ True) trivial fun _ _ ↦ trivial
    · exact allQ_bind (allQ_query _ (Sum.inr (Sum.inr (Sum.inr q))) trivial) fun _ _ ↦ trivial

end LazyQ

open Ideal.Transport Reduction.QInd

variable {W : Type} [Fintype W]

section Cast
variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable {ι : Type} (G : OracleSpec ι)

/-- A quantum program over the open interface of `setPrf prims prf pm`, read over that of
`prims` (kernel identity). -/
def castQ {α : Type} (x : QOC W (Lazy.OSpec (setPrf prims prf pm) G) α) :
    QOC W (Lazy.OSpec prims G) α := by
  kexact x

theorem castQ_bind {α β : Type} (x : QOC W (Lazy.OSpec (setPrf prims prf pm) G) α)
    (f : α → QOC W (Lazy.OSpec (setPrf prims prf pm) G) β) :
    castQ prims prf pm G (x >>= f) = castQ prims prf pm G x >>= fun a => castQ prims prf pm G (f a) := by
  krfl

variable [DecidableEq prims.Y] [SampleableType prims.Y]

theorem qLazyRun_setPrf {α : Type} (X : QOC W (Lazy.OSpec (setPrf prims prf pm) G) α) :
    qLazyRun (PublicHash.impl (setPrf prims prf pm)) X =
      qLazyRun (PublicHash.impl prims) (castQ prims prf pm G X) := by krfl

end Cast

section Msg
variable {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)

include hopt in
theorem qMsgOpenW_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    castQ prims prf pm (Lazy.msgG prims)
        (qMsgOpenW (prims := setPrf prims prf pm) sufCheck
          (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B))) =
      qMsgOpenW sufCheck (qPureBytesToInternal B) := by
  unfold qMsgOpenW
  rw [castQ_bind]
  refine bind_congr_k (by krfl) fun pkSeed => ?_
  rw [castQ_bind]
  refine bind_congr_k (by krfl) fun root => ?_
  rw [castQ_bind]
  have h := qRunForgerSig_tr prf pm codec optRand optRand' pkSeedDist B ⟨pkSeed, root⟩
    (fun m => castO' prims prf pm (Lazy.msgG prims) (Lazy.msgSignO optRand ⟨pkSeed, root⟩ m))
    (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' (trPk _ prf pm ⟨pkSeed, root⟩))
    (fun m => msgSignO_tr prims prf pm optRand optRand' hopt ⟨pkSeed, root⟩ m)
  have h2 : castQ prims prf pm (Lazy.msgG prims)
      (qRunForgerSig (prims := setPrf prims prf pm)
        (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B))
        ⟨pkSeed, root⟩ (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' ⟨pkSeed, root⟩)) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), trLog prf pm z.2)) <$>
        qRunForgerSig (qPureBytesToInternal B) ⟨pkSeed, root⟩
          (Lazy.msgSignO optRand ⟨pkSeed, root⟩) := by
    have h' := congrArg (castQ prims prf pm (Lazy.msgG prims)) h
    exact h'.trans (by krfl)
  refine (bind_congr_k h2 fun z => rfl).trans ?_
  rw [bind_map_left]
  refine bind_congr fun z => ?_
  have hv := sufCheck_setPrf prims prf pm ⟨pkSeed, root⟩ z.1 z.2
  simp only [trPk_mk] at hv
  rw [hv]
  show _ = _
  krfl

include hopt in
theorem qbPrfMsgWL_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qbPrfMsgWL (prims := setPrf prims prf pm) sufCheck
        (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B)) =
      qbPrfMsgWL sufCheck (qPureBytesToInternal B) := by
  unfold qbPrfMsgWL
  rw [qLazyRun_setPrf prims prf pm (Lazy.msgG prims),
    qMsgOpenW_setPrf prf pm codec optRand optRand' hopt pkSeedDist B]

include hopt in
theorem qMsgOpen_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    castQ prims prf pm (Lazy.msgG prims)
        (qMsgOpen (prims := setPrf prims prf pm)
          (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B))) =
      qMsgOpen (qPureBytesToInternal B) := by
  unfold qMsgOpen
  rw [castQ_bind]
  refine bind_congr_k (by krfl) fun pkSeed => ?_
  rw [castQ_bind]
  refine bind_congr_k (by krfl) fun root => ?_
  rw [castQ_bind]
  have h := qRunForger_tr prf pm codec optRand optRand' pkSeedDist B ⟨pkSeed, root⟩
    (fun m => castO' prims prf pm (Lazy.msgG prims) (Lazy.msgSignO optRand ⟨pkSeed, root⟩ m))
    (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' (trPk _ prf pm ⟨pkSeed, root⟩))
    (fun m => msgSignO_tr prims prf pm optRand optRand' hopt ⟨pkSeed, root⟩ m)
  have h2 : castQ prims prf pm (Lazy.msgG prims)
      (qRunForger ((qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B)).main
        ⟨pkSeed, root⟩) (Lazy.msgSignO (prims := setPrf prims prf pm) optRand' ⟨pkSeed, root⟩)) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        qRunForger ((qPureBytesToInternal B).main ⟨pkSeed, root⟩)
          (Lazy.msgSignO optRand ⟨pkSeed, root⟩) := by
    have h' := congrArg (castQ prims prf pm (Lazy.msgG prims)) h
    exact h'.trans (by krfl)
  refine (bind_congr_k h2 fun z => rfl).trans ?_
  rw [bind_map_left]
  refine bind_congr fun z => ?_
  have hv := harnessValid_setPrf prims prf pm ⟨pkSeed, root⟩ z.2 z.1.1 z.1.2
  simp only [trPk_mk] at hv
  rw [hv]
  show _ = _
  krfl

include hopt in
theorem qbPrfMsgL_setPrf (B : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qbPrfMsgL (prims := setPrf prims prf pm)
        (qPureBytesToInternal (trB prf pm codec optRand optRand' pkSeedDist B)) =
      qbPrfMsgL (qPureBytesToInternal B) := by
  unfold qbPrfMsgL
  rw [qLazyRun_setPrf prims prf pm (Lazy.msgG prims),
    qMsgOpen_setPrf prf pm codec optRand optRand' hopt pkSeedDist B]

end Msg

open Reduction.QInd

variable {W : Type} [Fintype W] {α : Type}

section Restrict
variable {D D' R : Type} [Inhabited R] (r : D → Option D')

lemma liftQ_restrict_unif (n : ℕ) :
    (liftQ (Restrict.restrictImpl (V := R) r (.inl n)) :
        QOC W (PRFScheme.PRFOracleSpec D' R) _) =
      liftM ((instrSpec W + PRFScheme.PRFOracleSpec D' R).query (Sum.inr (Sum.inl n))) := by
  simp [Restrict.restrictImpl, liftQ]
  rfl

lemma liftQ_restrict_some (d : D) (d' : D') (h : r d = some d') :
    (liftQ (Restrict.restrictImpl (V := R) r (.inr d)) :
        QOC W (PRFScheme.PRFOracleSpec D' R) _) =
      liftM ((instrSpec W + PRFScheme.PRFOracleSpec D' R).query (Sum.inr (Sum.inr d'))) := by
  simp [Restrict.restrictImpl, h, liftQ, PRFScheme.functionQuery]

lemma liftQ_restrict_none (d : D) (h : r d = none) :
    (liftQ (Restrict.restrictImpl (V := R) r (.inr d)) :
        QOC W (PRFScheme.PRFOracleSpec D' R) _) = pure default := by
  simp [Restrict.restrictImpl, h]

theorem ansRun_restrict (f : D → R) (f' : D' → R)
    (hf : ∀ d, f d = match r d with | some d' => f' d' | none => default)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) α) :
    ansRun f Q = ansRun f' (wrap0 (Restrict.restrictImpl r) Q) := by
  induction Q using OracleComp.inductionOn with
  | pure a => simp [ansRun_pure]
  | query_bind t k ih =>
    rcases t with j | n | d
    · rw [wrap0_instr_bind, ansRun_instr, ansRun_instr]
      simp only [ih]
    · rw [wrap0_query_bind, liftQ_restrict_unif, ansRun_unif, ansRun_unif]
      simp only [ih]
    · rw [wrap0_query_bind, ansRun_oracle]
      rcases hr : r d with _ | d'
      · rw [liftQ_restrict_none r d hr, pure_bind, ih, hf d, hr]
      · rw [liftQ_restrict_some r d d' hr, ansRun_oracle, ih, hf d, hr]

theorem qPrfRealPr_restrict {K : Type} (P : PRFScheme K D R) (P' : PRFScheme K D' R)
    (hk : P.keygen = P'.keygen)
    (he : ∀ k d, P.eval k d = match r d with | some d' => P'.eval k d' | none => default)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool) (ρ : Matrix W W ℂ) :
    qPrfRealPr P Q ρ = qPrfRealPr P' (wrap0 (Restrict.restrictImpl r) Q) ρ := by
  unfold qPrfRealPr qPrfRealExperiment
  rw [hk]
  congr 2
  funext k
  exact ansRun_restrict r (P.eval k) (P'.eval k) (he k) Q

/-- Every function query of a PRF distinguisher is in the domain of `r`. -/
def InDom : (instrSpec W + PRFScheme.PRFOracleSpec D R).Domain → Prop
  | .inr (.inr d) => (r d).isSome
  | _ => True

variable [DecidableEq D] [DecidableEq D'] [SampleableType R]

theorem idealRun_restrict
    (hinj : ∀ d₁ d₂ d', r d₁ = some d' → r d₂ = some d' → d₁ = d₂)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) α) (hQ : AllQueries (InDom (W := W) (R := R) r)
      (fun _ ↦ True) Q) :
    ∀ (c : (D →ₒ R).QueryCache) (c' : (D' →ₒ R).QueryCache),
      (∀ d d', r d = some d' → c d = c' d') →
      idealRun Q c = idealRun (wrap0 (Restrict.restrictImpl r) Q) c' := by
  induction Q using OracleComp.inductionOn with
  | pure a => intro c c' _; simp [idealRun_pure]
  | query_bind t k ih =>
    intro c c' hc
    have hQ' : InDom (W := W) (R := R) r t ∧ ∀ u, AllQueries (InDom (W := W) (R := R) r)
        (fun _ ↦ True) (k u) := hQ
    rcases t with j | n | d
    · rw [wrap0_instr_bind, idealRun_instr, idealRun_instr]
      simp only [fun i ↦ ih i (hQ'.2 i) c c' hc]
    · rw [wrap0_query_bind, liftQ_restrict_unif, idealRun_unif, idealRun_unif]
      simp only [fun i ↦ ih i (hQ'.2 i) c c' hc]
    · obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1 hQ'.1
      rw [wrap0_query_bind, liftQ_restrict_some r d d' hd']
      rcases hcd : c d with _ | v
      · have hcd' : c' d' = none := (hc d d' hd').symm.trans hcd
        rw [idealRun_oracle_none _ _ _ hcd, idealRun_oracle_none _ _ _ hcd']
        refine bind_congr fun v ↦ ih v (hQ'.2 v) _ _ ?_
        intro d₁ d₁' h₁
        by_cases e : d₁ = d
        · subst e
          rw [hd'] at h₁
          cases h₁
          simp
        · have e' : d₁' ≠ d' := fun e' ↦ e (hinj _ _ _ h₁ (e' ▸ hd'))
          rw [QueryCache.cacheQuery_of_ne _ _ e, QueryCache.cacheQuery_of_ne _ _ e']
          exact hc d₁ d₁' h₁
      · have hcd' : c' d' = some v := (hc d d' hd').symm.trans hcd
        rw [idealRun_oracle_some _ _ _ v hcd, idealRun_oracle_some _ _ _ v hcd']
        exact ih v (hQ'.2 v) c c' hc

theorem qPrfIdealPr_restrict
    (hinj : ∀ d₁ d₂ d', r d₁ = some d' → r d₂ = some d' → d₁ = d₂)
    (Q : QOC W (PRFScheme.PRFOracleSpec D R) Bool)
    (hQ : AllQueries (InDom (W := W) (R := R) r) (fun _ ↦ True) Q) (ρ : Matrix W W ℂ) :
    qPrfIdealPr Q ρ = qPrfIdealPr (wrap0 (Restrict.restrictImpl r) Q) ρ := by
  unfold qPrfIdealPr qPrfIdealExperiment
  have h := idealRun_restrict r hinj Q hQ ∅ ∅ (fun _ _ _ ↦ rfl)
  unfold idealRun at h
  rw [h]

end Restrict

section term

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- The finite `PRF_msg` domain within the cap: `(opt_rand-derived R, bounded message)`. -/
abbrev MsgD (c : Caps) : Type := BN × BList Byte c.ml

/-- The restriction of `PRF_msg` inputs to the cap. -/
def rcap (c : Caps) (d : BN × List Byte) : Option (MsgD c) :=
  if h : d.2.length ≤ c.ml then some (d.1, BList.ofList d.2 h) else none

theorem rcap_inj (c : Caps) (d₁ d₂ : BN × List Byte) (d' : MsgD c) (h₁ : rcap c d₁ = some d')
    (h₂ : rcap c d₂ = some d') : d₁ = d₂ := by
  unfold rcap at h₁ h₂
  split_ifs at h₁ h₂ with e₁ e₂
  cases h₁
  obtain ⟨a, b⟩ := d₁
  obtain ⟨a', b'⟩ := d₂
  simp only [Option.some.injEq, Prod.mk.injEq] at h₂
  obtain ⟨rfl, h⟩ := h₂
  have := congrArg (fun x : BList Byte c.ml ↦ List.ofFn x.2) h
  simp only [BList.ofFn_ofList] at this
  rw [this]

/-- Replace the `PRF_msg` component. -/
def _root_.Reduction.FinFns.withPrfMsg {p : Params} {c : Caps} (ω : FinFns p c)
    (g : Bytes p.n → Bytes p.n → BList Byte c.ml → Bytes p.n) : FinFns p c :=
  { ω with prfMsg := g }

/-- The SUF-CMA `PRF_msg` distinguisher in world `ω` with the port computing `H`. -/
noncomputable def msgMachSuf (ω : Ω128 c) (H : EncX c → EncY) :
    QOC (WS (EncX c) EncY E) (PRFScheme.PRFOracleSpec (BN × List Byte) BN) Bool :=
  qbPrfMsgWL sufCheck (intF c optRand₀ pkSeedDist₀ F ω H)

theorem msgMachSuf_withPrfMsg (ω : Ω128 c) (g : BN → BN → BList Byte c.ml → BN)
    (H : EncX c → EncY) :
    msgMachSuf c optRand₀ pkSeedDist₀ F (ω.withPrfMsg g) H = msgMachSuf c optRand₀ pkSeedDist₀ F ω H :=
  qbPrfMsgWL_setPrf (prims := primsΩ ω) (primsΩ ω).PRF
    (fun sk r m ↦ if h : m.length ≤ c.ml then g sk r (BList.ofList m h) else default)
    (codecR ω.toRand) (optRandOf c optRand₀ ω) (optRandOf c optRand₀ (ω.withPrfMsg g)) (fun _ ↦ rfl)
    pkSeedDist₀ (F.at H (algΩ c optRand₀ pkSeedDist₀ ω))

theorem pu_msgMachSuf (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) (ω : Ω128 c) :
    PU (msgMachSuf c optRand₀ pkSeedDist₀ F ω) q := by
  unfold msgMachSuf qbPrfMsgWL qLazyRun qMsgOpenW qRunForgerSig
  refine PU.wrap0 _ (PU.map _ (PU.wrap _ ?_ []))
  refine PU.liftQ_bind _ fun pkSeed ↦ PU.liftQ_bind _ fun root ↦ ?_
  exact PU.bind (q₂ := 0) (PU.wrap _ (pu_intF c optRand₀ pkSeedDist₀ F q hq ω _) []) fun z ↦
    PU.liftQ _ 0

theorem allQ_msgMachSuf (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (ω : Ω128 c) (H : EncX c → EncY) :
    AllQueries (InDom (W := WS (EncX c) EncY E) (R := BN) (rcap c)) (fun _ ↦ True)
      (msgMachSuf c optRand₀ pkSeedDist₀ F ω H) := by
  have h := allQ_qLazyRun (W := WS (EncX c) EncY E) (PublicHash.impl (primsΩ ω))
    (fun d : BN × List Byte ↦ d.2.length ≤ c.ml) _
    (allQ_qMsgOpenW (primsΩ ω) c.ml sufCheck (intF c optRand₀ pkSeedDist₀ F ω H)
      (allQ_qPureBytesToInternal c.ml _ fun pkb ↦ allQ_compileQ c H (F.main pkb) (hcap pkb)))
  refine allQ_mono ?_ (fun _ _ ↦ trivial) h
  rintro (j | n | d) ht
  · trivial
  · trivial
  · show (rcap c d).isSome
    have hd : d.2.length ≤ c.ml := ht
    simp [rcap, hd]

/-- The `PRF_msg` component as a keyed function `(SK.prf, (R, M)) ↦ value`. -/
def msgTable (g : BN × MsgD c → BN) : BN → BN → BList Byte c.ml → BN :=
  fun k r ms ↦ g (k, (r, ms))

/-- The keyed table of world `ω`. -/
def msgKeyed (ω : Ω128 c) : BN × MsgD c → BN := fun p ↦ ω.prfMsg p.1 p.2.1 p.2.2

/-- The `PRF_msg` point read by a port query. -/
def msgLoc : EncX c → Option (BN × MsgD c)
  | .inr (.inr (.inr x)) => some (x.1, (x.2.1, x.2.2))
  | _ => none

theorem encΩ_withPrfMsg_local (ω : Ω128 c) (g g' : BN × MsgD c → BN) (x : EncX c)
    (h : ∀ p, msgLoc c x = some p → g p = g' p) :
    encΩ (ω.withPrfMsg (msgTable c g)) x = encΩ (ω.withPrfMsg (msgTable c g')) x := by
  rcases x with x | x | x | x
  · rfl
  · rfl
  · rfl
  · change (g (x.1, (x.2.1, x.2.2)), _) = (g' (x.1, (x.2.1, x.2.2)), _)
    rw [h _ rfl]

/-- The keyed table as the `PRF_msg` component. -/
def msgTableEquiv : (BN × MsgD c → BN) ≃ (BN → BN → BList Byte c.ml → BN) where
  toFun := msgTable c
  invFun h := fun x ↦ h x.1 x.2.1 x.2.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Resampling the `PRF_msg` component does not change a uniform average. -/
theorem avΩ_resample_prfMsg (f : Ω128 c → ℝ≥0∞) :
    avΩ c f = avΩ c fun ω ↦ ∑ g : BN × MsgD c → BN,
      (Fintype.card (BN × MsgD c → BN) : ℝ≥0∞)⁻¹ * f (ω.withPrfMsg (msgTable c g)) := by
  classical
  unfold avΩ
  set u : ℝ≥0∞ := (Fintype.card (Ω128 c) : ℝ≥0∞)⁻¹ with hu
  have hw : ∀ ω : Ω128 c, unifW (Ω128 c) ω = u := fun _ ↦ rfl
  simp only [hw]
  set cG : ℝ≥0∞ := (Fintype.card (BN × MsgD c → BN) : ℝ≥0∞) with hcG
  have hne : cG ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hnt : cG ≠ ⊤ := ENNReal.natCast_ne_top _
  let Φ : Ω128 c × (BN × MsgD c → BN) → Ω128 c × (BN × MsgD c → BN) :=
    fun p ↦ (p.1.withPrfMsg (msgTable c p.2), (msgTableEquiv c).symm p.1.prfMsg)
  have hΦ : Function.Involutive Φ := by
    rintro ⟨⟨a, b, h, d⟩, g⟩
    rfl
  have h := Equiv.sum_comp hΦ.toPerm fun p : Ω128 c × (BN × MsgD c → BN) ↦ f p.1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  have h' : ∑ ω : Ω128 c, ∑ g : BN × MsgD c → BN, f (ω.withPrfMsg (msgTable c g)) =
      cG * ∑ ω : Ω128 c, f ω := by
    refine h.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, hcG]
  calc ∑ ω : Ω128 c, u * f ω = u * (cG⁻¹ * (cG * ∑ ω : Ω128 c, f ω)) := by
        rw [← mul_assoc cG⁻¹, ENNReal.inv_mul_cancel hne hnt, one_mul, Finset.mul_sum]
    _ = _ := by
        rw [← h', Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum]

theorem msgPrf_real_restrict (ω : Ω128 c)
    (X : QOC (WS (EncX c) EncY E) (PRFScheme.PRFOracleSpec (BN × List Byte) BN) Bool)
    (ρ : Matrix (WS (EncX c) EncY E) (WS (EncX c) EncY E) ℂ) :
    qPrfRealPr (msgPrf Link.vp (primsΩ ω)) X ρ =
      qPrfRealPr (keyedScheme id (msgKeyed c ω)) (wrap0 (Restrict.restrictImpl (rcap c)) X) ρ := by
  refine qPrfRealPr_restrict (rcap c) _ _ rfl ?_ _ ρ
  rintro k ⟨r, m⟩
  by_cases h : m.length ≤ c.ml
  · simp [rcap, h, msgPrf, msgPrfScheme, keyedScheme, msgKeyed, FinFns.toRand]
  · simp [rcap, h, msgPrf, msgPrfScheme, FinFns.toRand]

theorem msgKeyed_withPrfMsg (ω : Ω128 c) (g : BN × MsgD c → BN) :
    msgKeyed c (ω.withPrfMsg (msgTable c g)) = g := by
  funext p
  rfl

/-- **The `PRF_msg` term for a port-uniform machine family that does not depend on the
`PRF_msg` component of the world and whose function queries are within the cap.** -/
theorem msg_term_of_indep
    (mach : Ω128 c → (EncX c → EncY) →
      QOC (WS (EncX c) EncY E) (PRFScheme.PRFOracleSpec (BN × List Byte) BN) Bool)
    (q : ℕ) (hPU : ∀ ω, PU (mach ω) q)
    (hInd : ∀ ω g H, mach (ω.withPrfMsg g) H = mach ω H)
    (hCap : ∀ ω H, AllQueries (InDom (W := WS (EncX c) EncY E) (R := BN) (rcap c))
      (fun _ ↦ True) (mach ω H))
    (M : Matrix (WS (EncX c) EncY E) (WS (EncX c) EncY E) ℂ) (hM : M.PosSemidef)
    (h1 : M.trace = 1) :
    avΩ c (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω)) (mach ω (encΩ ω)) M) ≤
      avΩ c (fun ω ↦ qPrfIdealPr (mach ω (encΩ ω)) M) + epsPrf q := by
  obtain ⟨ρ, rfl⟩ := exists_subState M hM h1
  set machR := fun ω H ↦ wrap0 (Restrict.restrictImpl (rcap c)) (mach ω H) with hmachR
  have hR : ∀ ω : Ω128 c, qPrfRealPr (msgPrf Link.vp (primsΩ ω)) (mach ω (encΩ ω))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) =
      qPrfRealPr (keyedScheme id (msgKeyed c ω)) (machR ω (encΩ ω))
        (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := fun ω ↦
    msgPrf_real_restrict c ω _ _
  have hI : ∀ ω : Ω128 c, qPrfIdealPr (mach ω (encΩ ω))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) =
      qPrfIdealPr (machR ω (encΩ ω)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := fun ω ↦
    qPrfIdealPr_restrict (rcap c) (rcap_inj c) _ (hCap ω (encΩ ω)) _
  have hIndR : ∀ ω g H, machR (ω.withPrfMsg g) H = machR ω H := fun ω g H ↦ by
    simp only [hmachR, hInd]
  simp only [hR, hI]
  rw [avΩ_resample_prfMsg c fun ω ↦ qPrfRealPr (keyedScheme id (msgKeyed c ω))
      (machR ω (encΩ ω)) _,
    avΩ_resample_prfMsg c fun ω ↦ qPrfIdealPr (machR ω (encΩ ω)) _]
  simp only [msgKeyed_withPrfMsg, hIndR]
  have key : ∀ ω : Ω128 c, _ ≤ _ := fun ω ↦
    prf_PU_real_le_ideal_add (K := BN) (Dm := MsgD c) (R := BN) id Function.injective_id
      (machR ω) q (PU.wrap0 _ (hPU ω))
      (fun g ↦ encΩ (ω.withPrfMsg (msgTable c g))) (msgLoc c) (encΩ_withPrfMsg_local c ω) ρ
  refine (avΩ_mono c key).trans (le_of_eq ?_)
  rw [avΩ_add, avΩ_const, card_cast_real card_bytes_n]
  rfl

/-- **The `PRF_msg` term, SUF-CMA.**  No charge for the reduction's own hashing. -/
theorem msg_term_suf (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    avΩ c (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω))
        (qbPrfMsgWL sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) ≤
      avΩ c (fun ω ↦ qPrfIdealPr (qbPrfMsgWL sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) + epsPrf q :=
  msg_term_of_indep c (msgMachSuf c optRand₀ pkSeedDist₀ F) q
    (pu_msgMachSuf c optRand₀ pkSeedDist₀ F q hq)
    (msgMachSuf_withPrfMsg c optRand₀ pkSeedDist₀ F)
    (allQ_msgMachSuf c optRand₀ pkSeedDist₀ F hcap) F.ρ₀ F.posSemidef F.trace_eq_one

/-- The EUF-CMA `PRF_msg` distinguisher in world `ω` with the port computing `H`. -/
noncomputable def msgMachEuf (ω : Ω128 c) (H : EncX c → EncY) :
    QOC (WS (EncX c) EncY E) (PRFScheme.PRFOracleSpec (BN × List Byte) BN) Bool :=
  qbPrfMsgL (intF c optRand₀ pkSeedDist₀ F ω H)

theorem msgMachEuf_withPrfMsg (ω : Ω128 c) (g : BN → BN → BList Byte c.ml → BN)
    (H : EncX c → EncY) :
    msgMachEuf c optRand₀ pkSeedDist₀ F (ω.withPrfMsg g) H = msgMachEuf c optRand₀ pkSeedDist₀ F ω H :=
  qbPrfMsgL_setPrf (prims := primsΩ ω) (primsΩ ω).PRF
    (fun sk r m ↦ if h : m.length ≤ c.ml then g sk r (BList.ofList m h) else default)
    (codecR ω.toRand) (optRandOf c optRand₀ ω) (optRandOf c optRand₀ (ω.withPrfMsg g)) (fun _ ↦ rfl)
    pkSeedDist₀ (F.at H (algΩ c optRand₀ pkSeedDist₀ ω))

theorem pu_msgMachEuf (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) (ω : Ω128 c) :
    PU (msgMachEuf c optRand₀ pkSeedDist₀ F ω) q := by
  unfold msgMachEuf qbPrfMsgL qLazyRun qMsgOpen qRunForger
  refine PU.wrap0 _ (PU.map _ (PU.wrap _ ?_ []))
  refine PU.liftQ_bind _ fun pkSeed ↦ PU.liftQ_bind _ fun root ↦ ?_
  exact PU.bind (q₂ := 0) (PU.wrap _ (pu_intF c optRand₀ pkSeedDist₀ F q hq ω _) []) fun z ↦
    PU.liftQ _ 0

theorem allQ_msgMachEuf (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (ω : Ω128 c) (H : EncX c → EncY) :
    AllQueries (InDom (W := WS (EncX c) EncY E) (R := BN) (rcap c)) (fun _ ↦ True)
      (msgMachEuf c optRand₀ pkSeedDist₀ F ω H) := by
  have h := allQ_qLazyRun (W := WS (EncX c) EncY E) (PublicHash.impl (primsΩ ω))
    (fun d : BN × List Byte ↦ d.2.length ≤ c.ml) _
    (allQ_qMsgOpen (primsΩ ω) c.ml (intF c optRand₀ pkSeedDist₀ F ω H)
      (allQ_qPureBytesToInternal c.ml _ fun pkb ↦ allQ_compileQ c H (F.main pkb) (hcap pkb)))
  refine allQ_mono ?_ (fun _ _ ↦ trivial) h
  rintro (j | n | d) ht
  · trivial
  · trivial
  · show (rcap c d).isSome
    have hd : d.2.length ≤ c.ml := ht
    simp [rcap, hd]

/-- **The `PRF_msg` term, EUF-CMA.**  No charge for the reduction's own hashing. -/
theorem msg_term_euf (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    avΩ c (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω))
        (qbPrfMsgL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) ≤
      avΩ c (fun ω ↦ qPrfIdealPr (qbPrfMsgL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) + epsPrf q :=
  msg_term_of_indep c (msgMachEuf c optRand₀ pkSeedDist₀ F) q
    (pu_msgMachEuf c optRand₀ pkSeedDist₀ F q hq)
    (msgMachEuf_withPrfMsg c optRand₀ pkSeedDist₀ F)
    (allQ_msgMachEuf c optRand₀ pkSeedDist₀ F hcap) F.ρ₀ F.posSemidef F.trace_eq_one

end term
end Reduction.QMsg

#print axioms Reduction.QMsg.msg_term_suf
#print axioms Reduction.QMsg.msg_term_euf

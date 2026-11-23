import Ideal.Direct.RomGame

/-!
# H3: the ROM experiment of the simulator is the ROM-side game (`status/DIRECT.md` §12)

Pieces of the exact game match `RomGameSuf` between VCVio's SUF experiment of `simAdv` and
`Yrom` (`Direct/RomGame.lean`):

* `romO k`: the ROM interpretation of the realisers' open programs (no port) at the secret seed
  `k`; `romH_embQT`: the tagged handler on an open program leaves the simulator's table alone and is
  `romO`.
* `keygen_romO`, `sign_romO`, `verify_romO`: under `romO k`, the open key generation, signing and
  final check ARE `romScheme`'s key generation (at `SK.seed = k`), signing and verification (exact
  equalities of programs over `unifSpec + hashSpec Cr`): naturality of the generic SLH-DSA programs
  (`GeneralScheme.*_natural`) and the ledger congruence (honest programs read secrets only at
  secret children of ledger addresses, which are in the PRF-game domain `SkDom`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf Reduction Reduction.Open
open Ideal.Realize.Msg (Rd mainC optRand₀ harnP)

/-! ## The stateless ROM interpretation of an open program -/

/-- **The ROM interpretation of an open program at the secret seed `k`**: coins forwarded, a
PRF-game query at an in-domain address `(PK.seed, a)` is the `Thash` oracle at
`(PK.seed, key a, [k])` (out of the domain: `default`, as the restriction does), hash and
`PRF_msg` queries are oracle queries. -/
noncomputable def romO (k : Bytes 16) : QueryImpl (Reduction.Open.PSpec Rd (D₀ Rd)) (OracleComp RS)
  | .inl n => rq (.inl n)
  | .inr (.inl d) =>
    match skRestrict Link.vp Rd d with
    | some d' => rq (.inr (.inl (PublicHashQuery.thash d'.1 (Cr.adrsToKey d'.2.1) [k])))
    | none => pure (default : Bytes 16)
  | .inr (.inr (.inl q)) => rq (.inr (.inl q))
  | .inr (.inr (.inr t)) => rq (.inr (.inr ⟨t.1, t.2.1, t.2.2⟩))

/-- A stateful handler that never touches its state is its stateless part. -/
theorem run_simulateQ_stateless {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (ψ : QueryImpl spec (StateT σ (OracleComp RS))) (φ : QueryImpl spec (OracleComp RS))
    (h : ∀ t s, (ψ t).run s = (fun a => (a, s)) <$> φ t) (X : OracleComp spec α) (s : σ) :
    (simulateQ ψ X).run s = (fun a => (a, s)) <$> simulateQ φ X := by
  induction X using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t f ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, h, bind_map_left, map_bind,
      ih]

theorem romH_step (k : Bytes 16) (t : (Reduction.Open.PSpec Rd (D₀ Rd)).Domain)
    (T : (hS St Blk).QueryCache) :
    (((romH k ∘ₛ restrictPT (D' := Dsk) (skRestrict Link.vp Rd)) ∘ₛ embQT) t).run T =
      (fun a => (a, T)) <$> romO k t := by
  rcases t with n | d | q | t
  · simp only [QueryImpl.apply_compose, embQT, restrictPT, simulateQ_spec_query, romH, romO,
      StateT.run_monadLift, monadLift_self]
    rfl
  · show (simulateQ (romH k ∘ₛ restrictPT (D' := Dsk) (skRestrict Link.vp Rd))
        (liftM ((QT (D₀ Rd)).query (.inr (.inl (.inr d)))))).run T = _
    erw [simulateQ_spec_query]
    simp only [QueryImpl.apply_compose]
    cases hd : skRestrict Link.vp Rd d with
    | none =>
      simp only [restrictPT, hd, romO, simulateQ_pure, StateT.run_pure]
      exact (map_pure _ _).symm
    | some d' =>
      simp only [restrictPT, hd, romO]
      erw [simulateQ_spec_query]
      rfl
  · simp only [QueryImpl.apply_compose, embQT, restrictPT, simulateQ_spec_query, romH, romO,
      StateT.run_monadLift, monadLift_self]
    rfl
  · simp only [QueryImpl.apply_compose, embQT, restrictPT, simulateQ_spec_query, romH, romO,
      StateT.run_monadLift, monadLift_self]
    rfl

/-- **The tagged handler on an open program (no port query) leaves the table alone.** -/
theorem romH_embQT (k : Bytes 16) {α : Type} (X : OracleComp (Reduction.Open.PSpec Rd (D₀ Rd)) α)
    (T : (hS St Blk).QueryCache) :
    (simulateQ (romH k) (simulateQ (restrictPT (D' := Dsk) (skRestrict Link.vp Rd)) (simulateQ embQT X))).run T =
      (fun a => (a, T)) <$> simulateQ (romO k) X := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  exact run_simulateQ_stateless _ _ (romH_step k) X T

/-! ## `romO` on lifted samples -/

theorem romO_liftM (k : Bytes 16) {α : Type} (ob : ProbComp α) :
    simulateQ (romO k) (liftM ob : OracleComp (Reduction.Open.PSpec Rd (D₀ Rd)) α) =
      (liftM ob : OracleComp RS α) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n f ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    have : simulateQ (romO k)
        (liftM (liftM (unifSpec.query n) : ProbComp _) :
          OracleComp (Reduction.Open.PSpec Rd (D₀ Rd)) _) =
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp RS _) := by
      show simulateQ (romO k) (liftM ((Reduction.Open.PSpec Rd (D₀ Rd)).query (.inl n))) = _
      rw [simulateQ_spec_query]
      rfl
    rw [this]

/-! ## The open programs under `romO` are `romScheme`'s -/

section Hom

/-- `romO k` as a query-preserving morphism from the open interface (`openQ`). -/
noncomputable def romOHom (k : Bytes 16) :
    @HasQuery.QueryHom _ (publicHashSpec Cr) (OracleComp (Reduction.Open.PSpec Rd (D₀ Rd))) _
      (openQ Rd (D₀ Rd)) (OracleComp RS) _ _ :=
  { toMonadHom := simulateQ' (romO k)
    map_query' := fun q => by
      show simulateQ (romO k) (liftM ((Reduction.Open.PSpec Rd (D₀ Rd)).query (.inr (.inr (.inl q))))) = _
      rw [simulateQ_spec_query]
      rfl }

/-- The public-hash interface beside an abstract secret-value oracle. -/
abbrev SecM := publicHashSpec Cr + (Adrs →ₒ Cr.Y)

/-- Answer the public hash by the ROM and the secrets by `s`. -/
def secI (s : Adrs → OracleComp RS Cr.Y) : QueryImpl SecM (OracleComp RS)
  | .inl q => rq (.inr (.inl q))
  | .inr a => s a

/-- `secI s` as a query-preserving morphism. -/
noncomputable def secH (s : Adrs → OracleComp RS Cr.Y) :
    HasQuery.QueryHom (publicHashSpec Cr) (OracleComp SecM) (OracleComp RS) :=
  { toMonadHom := simulateQ' (secI s)
    map_query' := fun q => by
      show simulateQ (secI s) (liftM (SecM.query (.inl q))) = _
      rw [simulateQ_spec_query]
      rfl }

theorem secH_query (s : Adrs → OracleComp RS Cr.Y) (a : Adrs) :
    (secH s).toMonadHom (liftM (SecM.query (.inr a)) : OracleComp SecM Cr.Y) = s a := by
  change simulateQ (secI s) _ = _
  rw [simulateQ_spec_query]
  rfl

variable {s₁ s₂ : Adrs → OracleComp RS Cr.Y}
  (h12 : ∀ a b, b ∈ constructionAddresses Link.vp → .inl a ∈ childAdrs Link.vp b → s₁ a = s₂ a)
include h12

/-- **Ledger congruence (key generation)**: secrets that agree at the secret children of ledger
addresses give the same program. -/
theorem keygenWS_congr (pkSeed : Cr.PkSeed) :
    (GeneralScheme.keygenInternalWithSecretM Cr s₁ pkSeed : OracleComp RS Cr.Y) =
      GeneralScheme.keygenInternalWithSecretM Cr s₂ pkSeed := by
  rw [← GeneralScheme.keygenInternalWithSecretM_natural Cr (secH s₁)
      (fun a => (liftM (SecM.query (.inr a)) : OracleComp SecM Cr.Y))
      _ (fun a _ => secH_query s₁ a),
    ← GeneralScheme.keygenInternalWithSecretM_natural Cr (secH s₂)
      (fun a => (liftM (SecM.query (.inr a)) : OracleComp SecM Cr.Y))
      _ (fun a _ => secH_query s₂ a)]
  refine keygenInternalWithSecretM_pred_of_ledger (m := OracleComp SecM)
    (fun {α} oa => (secH s₁).toMonadHom oa = (secH s₂).toMonadHom oa)
    (fun x => by simp) (fun oa ob h1 h2 => by
      rw [(secH s₁).toMonadHom.mmap_bind, (secH s₂).toMonadHom.mmap_bind, h1]
      exact bind_congr fun x => h2 x)
    Cr (fun a b hb hab => by rw [secH_query, secH_query, h12 a b hb hab]) pkSeed
    (fun a _ xs => by rw [PublicHash.tl_natural, PublicHash.tl_natural])

/-- **Ledger congruence (signing).** -/
theorem signWS_congr (msg : List Byte) (pkSeed : Cr.PkSeed) (pkRoot R : Cr.Y) :
    (GeneralScheme.signInternalWithSecretRandomizerM Cr s₁ msg pkSeed pkRoot R :
        OracleComp RS (GeneralScheme.SignatureCore Link.vp Cr)) =
      GeneralScheme.signInternalWithSecretRandomizerM Cr s₂ msg pkSeed pkRoot R := by
  rw [← GeneralScheme.signInternalWithSecretRandomizerM_natural Cr (secH s₁)
      (fun a => (liftM (SecM.query (.inr a)) : OracleComp SecM Cr.Y))
      _ (fun a _ => secH_query s₁ a),
    ← GeneralScheme.signInternalWithSecretRandomizerM_natural Cr (secH s₂)
      (fun a => (liftM (SecM.query (.inr a)) : OracleComp SecM Cr.Y))
      _ (fun a _ => secH_query s₂ a)]
  refine signInternalWithSecretRandomizerM_pred_of_ledger (m := OracleComp SecM)
    (fun {α} oa => (secH s₁).toMonadHom oa = (secH s₂).toMonadHom oa)
    (fun x => by simp) (fun oa ob h1 h2 => by
      rw [(secH s₁).toMonadHom.mmap_bind, (secH s₂).toMonadHom.mmap_bind, h1]
      exact bind_congr fun x => h2 x)
    Cr (fun a b hb hab => by rw [secH_query, secH_query, h12 a b hb hab]) msg pkSeed pkRoot R
    (fun a _ xs => by rw [PublicHash.tl_natural, PublicHash.tl_natural])
    (by rw [PublicHash.hmsg_natural, PublicHash.hmsg_natural])

end Hom

/-- The PRF-game secret under `romO k` is the oracle secret at every ledger secret child. -/
theorem romO_secret (k pkSeed : Bytes 16) (a b : Adrs) (hb : b ∈ constructionAddresses Link.vp)
    (hab : .inl a ∈ childAdrs Link.vp b) :
    simulateQ (romO k) (gameQ Rd (pkSeed, a) : OracleComp (Reduction.Open.PSpec Rd (D₀ Rd)) _) =
      (oracleSecret Cr (Equiv.refl _) pkSeed k a : OracleComp RS (Bytes 16)) := by
  have hdom : SkDom Link.vp a := skDom_of_secretChild
    (fipsApprovedAddressBounds Link.S128).toCanonicalAddressBounds hb hab
  unfold gameQ
  rw [simulateQ_spec_query]
  simp only [romO, skRestrict_of_dom (prims := Rd) (d := (pkSeed, a)) hdom]
  rfl

/-- **Open key generation under `romO k` is `romScheme`'s key generation at `SK.seed = k`.** -/
theorem keygen_romO (k pkSeed : Bytes 16) :
    simulateQ (romO k) (openKeygenP Rd pkSeed) =
      (GeneralScheme.keygenInternalWithSecretM Cr (oracleSecret Cr (Equiv.refl _) pkSeed k) pkSeed :
        OracleComp RS (Bytes 16)) := by
  have h := GeneralScheme.keygenInternalWithSecretM_natural Cr (romOHom k)
    (fun a => gameQ Rd (pkSeed, a))
    (fun a => simulateQ (romO k) (gameQ Rd (pkSeed, a))) (fun a _ => rfl) pkSeed
  refine h.trans (keygenWS_congr ?_ pkSeed)
  exact fun a b hb hab => romO_secret k pkSeed a b hb hab

/-- **Open signing under `romO k` is `romScheme`'s signing at `SK = (k, skPrf, pk)`.** -/
theorem sign_romO (k skPrf : Bytes 16) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pk : PublicKeyCore Cr) (m : List Byte) :
    simulateQ (romO k) (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m) =
      (romS oR ($ᵗ (Bytes 16))).sign pk ⟨k, skPrf, pk.pkSeed, pk.pkRoot⟩ m := by
  unfold openSignP openSignCoreP
  rw [simulateQ_bind, romO_liftM]
  refine bind_congr fun addrnd => ?_
  unfold prfMsgQ
  rw [simulateQ_bind, simulateQ_spec_query]
  refine bind_congr fun R => ?_
  have h := GeneralScheme.signInternalWithSecretRandomizerM_natural Cr (romOHom k)
    (fun a => gameQ Rd (pk.pkSeed, a))
    (fun a => simulateQ (romO k) (gameQ Rd (pk.pkSeed, a))) (fun a _ => rfl) m pk.pkSeed
    pk.pkRoot R
  refine h.trans (signWS_congr ?_ m pk.pkSeed pk.pkRoot R)
  exact fun a b hb hab => romO_secret k pk.pkSeed a b hb hab

/-- **The open final check under `romO k` is `romScheme`'s verification.** -/
theorem verify_romO (k : Bytes 16) (msg : List Byte) (sig : GeneralScheme.SignatureCore Link.vp Cr)
    (pk : PublicKeyCore Cr) :
    simulateQ (romO k) (simulateQ (hashEmb Rd (D₀ Rd))
        (GeneralScheme.verifyInternalM Link.vp Rd.core msg sig pk :
          OracleComp (publicHashSpec Rd.core) Bool)) =
      (GeneralScheme.verifyInternalM Link.vp Cr msg sig pk : OracleComp RS Bool) := by
  rw [← QueryImpl.simulateQ_compose]
  have e : (romO k ∘ₛ hashEmb Rd (D₀ Rd)) =
      HasQuery.toQueryImpl (spec := publicHashSpec Cr) (m := OracleComp RS) := by
    funext q
    simp only [QueryImpl.apply_compose, hashEmb]
    rw [simulateQ_spec_query]
    rfl
  rw [e]
  exact GeneralScheme.verifyInternalM_natural Link.vp Cr
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec Cr) (m := OracleComp RS)) msg sig pk

/-! ## The forger phase: two states nested in the two orders -/

/-- **State swap**: a stateless-in-`T` harness under a `T`-handler is the `T`-simulation under the
log handler, when it is so query by query. -/
theorem swap_nest {ι₀ ι₁ ι₂ ι₃ : Type} {S₀ : OracleSpec ι₀} {S₁ : OracleSpec ι₁}
    {S₂ : OracleSpec ι₂} {S₃ : OracleSpec ι₃} {σL σT β : Type}
    (Φ : QueryImpl S₁ (StateT σT (OracleComp S₃))) (H : QueryImpl S₀ (StateT σL (OracleComp S₁)))
    (G : QueryImpl S₀ (StateT σT (OracleComp S₂))) (P : QueryImpl S₂ (StateT σL (OracleComp S₃)))
    (h : ∀ t l T, (simulateQ Φ ((H t).run l)).run T =
      (fun z => ((z.1.1, z.2), z.1.2)) <$> (simulateQ P ((G t).run T)).run l)
    (oa : OracleComp S₀ β) (l : σL) (T : σT) :
    (simulateQ Φ ((simulateQ H oa).run l)).run T =
      (fun z => ((z.1.1, z.2), z.1.2)) <$> (simulateQ P ((simulateQ G oa).run T)).run l := by
  induction oa using OracleComp.inductionOn generalizing l T with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, h, bind_map_left,
      map_bind, ih]

section Forger

variable (k skPrf : Bytes 16) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pk : PublicKeyCore Cr)

/-- The tagged handler after the restriction. -/
noncomputable abbrev ΦR : QueryImpl (QT (D₀ Rd)) (StateT (hS St Blk).QueryCache (OracleComp RS)) :=
  romH k ∘ₛ restrictPT (D' := Dsk) (skRestrict Link.vp Rd)

/-- The harness of the tagged program, after the forger's encoding. -/
noncomputable abbrev HT : QueryImpl (FSpecP (List Byte))
    (StateT (SigLog Link.vp Rd) (OracleComp (QT (D₀ Rd)))) :=
  harnP (portQT pk) (sigSignOracle (fun m => simulateQ embQT
    (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m))) ∘ₛ Ideal.Realize.Msg.signPC Wots.codec₀

/-- VCVio's signing run as a `StateT` log. -/
noncomputable abbrev PV : QueryImpl BSpec (StateT (SigLog Link.vp Rd) (OracleComp RS)) :=
  (QueryImpl.id' RS).liftTarget (StateT (SigLog Link.vp Rd) (OracleComp RS)) +
    appendLog ((romS oR ($ᵗ (Bytes 16))).sign pk ⟨k, skPrf, pk.pkSeed, pk.pkRoot⟩)

theorem liftM_eq_simulateQ {α : Type} (X : ProbComp α) :
    (liftM X : OracleComp RS α) = simulateQ (fun n => rq (.inl n)) X := by
  induction X using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n f ih =>
    rw [liftM_bind, simulateQ_bind, simulateQ_spec_query]
    simp only [← ih]
    rfl

theorem freshSt_PV (l : SigLog Link.vp Rd) :
    (simulateQ (PV k skPrf oR pk) freshSt).run l = (fun u => (u, l)) <$> freshR := by
  unfold freshSt freshR
  rw [← QueryImpl.simulateQ_compose, liftM_eq_simulateQ]
  refine run_simulateQ_stateless _ _ (fun n l' => ?_) _ l
  show (simulateQ (PV k skPrf oR pk) (liftM (BSpec.query (.inl (.inl n))))).run l' = _
  rw [simulateQ_spec_query]
  rfl

theorem hq_PV (t : (hashSpec Cr).Domain) (l : SigLog Link.vp Rd) :
    (simulateQ (PV k skPrf oR pk) (hq t)).run l = (fun y => (y, l)) <$> rq (.inr t) := by
  show (simulateQ (PV k skPrf oR pk) (liftM (BSpec.query (.inl (.inr t))))).run l = _
  rw [simulateQ_spec_query]
  rfl

theorem simStep_PV (q : St × Blk) (T : (hS St Blk).QueryCache) (l : SigLog Link.vp Rd) :
    (simulateQ (PV k skPrf oR pk) ((simStep pk q).run T)).run l =
      (fun z => (z, l)) <$> (simStepR pk q).run T := by
  show (simulateQ (PV k skPrf oR pk) (simStep pk q T)).run l = (fun z => (z, l)) <$> simStepR pk q T
  unfold simStep simStepR
  cases hT : T q with
  | some v => simp
  | none =>
    simp only [simulateQ_bind, StateT.run_bind, freshSt_PV, bind_map_left, map_bind]
    refine bind_congr fun u => ?_
    cases relQ pk T q with
    | none => simp
    | some t =>
      simp only [simulateQ_bind, StateT.run_bind, hq_PV, bind_map_left, map_bind, simulateQ_pure,
        StateT.run_pure, map_pure]

theorem ΦR_embQT {α : Type} (X : OracleComp (Reduction.Open.PSpec Rd (D₀ Rd)) α)
    (T : (hS St Blk).QueryCache) :
    (simulateQ (ΦR k) (simulateQ embQT X)).run T = (fun a => (a, T)) <$> simulateQ (romO k) X := by
  rw [QueryImpl.simulateQ_compose]
  exact romH_embQT k X T

theorem forger_step (t : (FSpecP (List Byte)).Domain) (l : SigLog Link.vp Rd)
    (T : (hS St Blk).QueryCache) :
    (simulateQ (ΦR k) ((HT skPrf oR pk t).run l)).run T =
      (fun z => ((z.1.1, z.2), z.1.2)) <$>
        (simulateQ (PV k skPrf oR pk) ((simImpl pk t).run T)).run l := by
  rcases t with n | q | m
  · simp only [HT, QueryImpl.apply_compose, Ideal.Realize.Msg.signPC, simulateQ_spec_query, harnP,
      simImpl]
    simp only [StateT.run_monadLift, monadLift_self]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind,
      simulateQ_query]
    rfl
  · simp only [HT, QueryImpl.apply_compose, Ideal.Realize.Msg.signPC, simulateQ_spec_query, harnP,
      simImpl]
    rw [simStep_PV]
    simp only [StateT.run_monadLift, monadLift_self]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind,
      simulateQ_query, Functor.map_map]
    unfold portQT
    rw [simulateQ_spec_query]
    simp only [map_eq_bind_pure_comp, Function.comp_def, ΦR, QueryImpl.apply_compose, restrictPT]
    erw [simulateQ_spec_query]
    rfl
  · simp only [HT, QueryImpl.apply_compose, Ideal.Realize.Msg.signPC, simulateQ_map, simImpl]
    erw [simulateQ_spec_query]
    simp only [harnP, sigSignOracle, StateT.run_map, run_appendLog_apply, simulateQ_map,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    rw [ΦR_embQT, sign_romO]
    simp only [StateT.run_monadLift, monadLift_self, StateT.run_map, simulateQ_map]
    show _ = (fun z => ((z.1.1, z.2), z.1.2)) <$>
      (simulateQ (PV k skPrf oR pk) ((fun a => (a, T)) <$> (encodeSignature Link.vp Wots.codec₀ <$>
        (liftM (BSpec.query (.inr m)) : OracleComp BSpec _)))).run l
    rw [simulateQ_map, simulateQ_map, simulateQ_spec_query]
    simp only [StateT.run_map, PV, QueryImpl.add_apply_inr, run_appendLog_apply, map_bind,
      Functor.map_map, bind_map_left, map_pure]

end Forger

/-! ## Assembly -/

section Assembly

theorem liftM_eq_simulateQ_gen {ι : Type} {X : OracleSpec ι} {α : Type} (ob : ProbComp α) :
    (liftM ob : OracleComp (unifSpec + X) α) =
      simulateQ (fun n => (liftM ((unifSpec + X).query (.inl n)) : OracleComp (unifSpec + X) _))
        ob := by
  induction ob using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n f ih =>
    rw [liftM_bind, simulateQ_bind, simulateQ_spec_query]
    simp only [← ih]
    rfl

theorem ΦR_liftM (k : Bytes 16) {α : Type} (ob : ProbComp α) (T : (hS St Blk).QueryCache) :
    (simulateQ (ΦR k) (liftM ob : OracleComp (QT (D₀ Rd)) α)).run T =
      (fun a => (a, T)) <$> (liftM ob : OracleComp RS α) := by
  rw [liftM_eq_simulateQ_gen, ← QueryImpl.simulateQ_compose, liftM_eq_simulateQ]
  refine run_simulateQ_stateless _ _ (fun n T' => ?_) ob T
  simp only [QueryImpl.apply_compose, simulateQ_spec_query, ΦR, restrictPT]
  rfl

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))

open scoped Classical in
/-- **VCVio's SUF experiment of `simAdv` after drawing `PK.seed` and `SK.seed = k`.** -/
noncomputable def Wexp (pkSeed k : Bytes 16) : OracleComp RS Bool := do
  let skPrf ← (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp RS (Bytes 16))
  let root ← (GeneralScheme.keygenInternalWithSecretM Cr (oracleSecret Cr (Equiv.refl _) pkSeed k)
    pkSeed : OracleComp RS Cr.Y)
  let z ← (simulateQ (PV k skPrf oR ⟨pkSeed, root⟩)
    ((simAdv S oR ($ᵗ (Bytes 16))).main ⟨pkSeed, root⟩)).run []
  let v ← (GeneralScheme.verifyInternalM Link.vp Cr z.1.1 z.1.2 ⟨pkSeed, root⟩ : OracleComp RS Bool)
  pure (!signingLogContains z.2 z.1.1 z.1.2 && v)

theorem forger_phase (k skPrf : Bytes 16) (pk : PublicKeyCore Cr) (T : (hS St Blk).QueryCache) :
    (simulateQ (ΦR k) ((simulateQ (harnP (portQT pk) (sigSignOracle (fun m => simulateQ embQT
        (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m)))) (mainC S pk)).run [])).run T =
      (fun z => ((readOut z.1.1, z.2), z.1.2)) <$>
        (simulateQ (PV k skPrf oR pk)
          ((simulateQ (simImpl pk) (S.main (encodePublicKey Wots.codec₀ pk))).run T)).run [] := by
  unfold mainC Ideal.Realize.Msg.typedC
  rw [simulateQ_map, StateT.run_map, simulateQ_map, StateT.run_map, ← QueryImpl.simulateQ_compose]
  erw [swap_nest _ _ _ _ (forger_step k skPrf oR pk)]
  simp only [Functor.map_map]
  rfl

theorem simAdv_PV (k skPrf : Bytes 16) (pk : PublicKeyCore Cr) :
    (simulateQ (PV k skPrf oR pk) ((simAdv S oR ($ᵗ (Bytes 16))).main pk)).run [] =
      (fun z => (readOut z.1.1, z.2)) <$>
        (simulateQ (PV k skPrf oR pk)
          ((simulateQ (simImpl pk) (S.main (encodePublicKey Wots.codec₀ pk))).run ∅)).run [] := by
  simp only [simAdv, StateT.run', simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

theorem bRest_eq_Wexp (k pkSeed : Bytes 16) :
    Prod.fst <$> (simulateQ (ΦR k) (bRestWOpenPT oR sufCheckOpen (mainC S) pkSeed)).run ∅ =
      Wexp S oR pkSeed k := by
  unfold bRestWOpenPT Wexp
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  erw [ΦR_liftM]
  simp only [bind_map_left]
  refine bind_congr fun skPrf => ?_
  erw [ΦR_embQT, keygen_romO]
  simp only [bind_map_left]
  refine bind_congr fun root => ?_
  erw [forger_phase, simAdv_PV]
  simp only [bind_map_left]
  refine bind_congr fun z => ?_
  erw [ΦR_embQT]
  simp only [Functor.map_map, id_map']
  unfold sufCheckOpen
  rw [simulateQ_bind, simulateQ_bind]
  erw [verify_romO]
  refine bind_congr fun v => ?_
  simp only [simulateQ_pure, signingLogContains]
  congr

theorem runWS_eq (k skPrf : Bytes 16) (pk : PublicKeyCore Cr) {α : Type}
    (oa : OracleComp BSpec α) :
    (romS oR ($ᵗ (Bytes 16))).runWithSigningOracle pk ⟨k, skPrf, pk.pkSeed, pk.pkRoot⟩ oa =
      (simulateQ (PV k skPrf oR pk) oa).run [] := by
  have h := Reduction.run_withLogging_eq_run_appendLog (spec₀ := RS) (m₀ := OracleComp RS)
    ((romS oR ($ᵗ (Bytes 16))).sign pk ⟨k, skPrf, pk.pkSeed, pk.pkRoot⟩) oa []
  simp only [List.nil_append, Prod.mk.eta, id_map'] at h
  refine Eq.trans ?_ h
  simp [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle]
  rfl

/-- **VCVio's SUF experiment of the simulator, sample by sample.** -/
theorem exp_eq : strongUnforgeableExperiment (simAdv S oR ($ᵗ (Bytes 16))) =
    (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun pkSeed =>
      (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun k => Wexp S oR pkSeed k := by
  unfold strongUnforgeableExperiment
  rw [show (romS oR ($ᵗ (Bytes 16))).keygen = _ from romScheme_keygen Cr _ _ _]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pkSeed => ?_
  refine bind_congr fun k => ?_
  unfold Wexp
  refine bind_congr fun skPrf => ?_
  refine bind_congr fun root => ?_
  erw [runWS_eq oR k skPrf ⟨pkSeed, root⟩]
  refine bind_congr fun z => bind_congr fun v => ?_
  simp only [signingLogContains]
  congr

/-- **The ROM-side game at `SK.seed = k`, sample by sample.** -/
theorem yrom_inner (k : Bytes 16) :
    (simulateQ (romH k) (PprfST oR ($ᵗ (Bytes 16)) S)).run' ∅ =
      (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun pkSeed => Wexp S oR pkSeed k := by
  unfold PprfST
  rw [← QueryImpl.simulateQ_compose, StateT.run'_eq, simulateQ_bind, StateT.run_bind]
  erw [ΦR_liftM]
  simp only [bind_map_left, map_bind]
  exact bind_congr fun pkSeed => bRest_eq_Wexp S oR k pkSeed

theorem run'_liftM_bind_rom {α β : Type} (a : ProbComp α) (f : α → OracleComp RS β) :
    (simulateQ (hashSpec Cr).romImpl ((liftM a : OracleComp RS α) >>= f)).run' ∅ =
      a >>= fun x => (simulateQ (hashSpec Cr).romImpl (f x)).run' ∅ := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, OracleSpec.simulateQ_romImpl_liftM_run]
  simp only [bind_map_left, map_bind]
  rfl

theorem rom_swap (a b : ProbComp (Bytes 16)) (W : Bytes 16 → Bytes 16 → OracleComp RS Bool) :
    (ProbCompRuntime.rom (hashSpec Cr)).evalDist
        ((liftM a : OracleComp RS (Bytes 16)) >>= fun x =>
          (liftM b : OracleComp RS (Bytes 16)) >>= fun y => W x y) =
      (ProbCompRuntime.rom (hashSpec Cr)).evalDist
        ((liftM b : OracleComp RS (Bytes 16)) >>= fun y =>
          (liftM a : OracleComp RS (Bytes 16)) >>= fun x => W x y) := by
  rw [ProbCompRuntime.rom_evalDist, ProbCompRuntime.rom_evalDist, run'_liftM_bind_rom,
    run'_liftM_bind_rom]
  simp only [run'_liftM_bind_rom]
  exact OracleComp.evalDist_bind_bind_swap a b _

end Assembly

/-! ## H3 -/

/-- **H3 (SUF), proved**: VCVio's SUF advantage of the simulator in the ROM is the success
probability of the ROM-side game `Yrom`. -/
theorem romGameSuf : RomGameSuf := by
  intro S oR
  unfold strongUnforgeableAdvantage
  have hY : Yrom S oR = (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun k =>
      (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun pkSeed => Wexp S oR pkSeed k :=
    bind_congr fun k => yrom_inner S oR k
  rw [exp_eq, hY, rom_swap]


/-! ## H3, EUF -/

/-- **State swap with a log map** (the harness keeps a function `ρ` of the outer log). -/
theorem swap_nest_map {ι₀ ι₁ ι₂ ι₃ : Type} {S₀ : OracleSpec ι₀} {S₁ : OracleSpec ι₁}
    {S₂ : OracleSpec ι₂} {S₃ : OracleSpec ι₃} {σL σL' σT β : Type} (ρ : σL → σL')
    (Φ : QueryImpl S₁ (StateT σT (OracleComp S₃))) (H : QueryImpl S₀ (StateT σL' (OracleComp S₁)))
    (G : QueryImpl S₀ (StateT σT (OracleComp S₂))) (P : QueryImpl S₂ (StateT σL (OracleComp S₃)))
    (h : ∀ t l T, (simulateQ Φ ((H t).run (ρ l))).run T =
      (fun z => ((z.1.1, ρ z.2), z.1.2)) <$> (simulateQ P ((G t).run T)).run l)
    (oa : OracleComp S₀ β) (l : σL) (T : σT) :
    (simulateQ Φ ((simulateQ H oa).run (ρ l))).run T =
      (fun z => ((z.1.1, ρ z.2), z.1.2)) <$> (simulateQ P ((simulateQ G oa).run T)).run l := by
  induction oa using OracleComp.inductionOn generalizing l T with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, h, bind_map_left,
      map_bind, ih]

section ForgerE

variable (k skPrf : Bytes 16) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pk : PublicKeyCore Cr)

/-- The messages of a signing log. -/
def msgs (l : SigLog Link.vp Rd) : List (List Byte) := l.map (fun e => e.1)

/-- The EUF harness of the tagged program, after the forger's encoding. -/
noncomputable abbrev HTE : QueryImpl (FSpecP (List Byte))
    (StateT (List (List Byte)) (OracleComp (QT (D₀ Rd)))) :=
  harnP (portQT pk) (harnessSignOracle (vp := Link.vp) (prims := Rd) (fun m => simulateQ embQT
    (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m))) ∘ₛ Ideal.Realize.Msg.signPC Wots.codec₀

theorem forger_stepE (t : (FSpecP (List Byte)).Domain) (l : SigLog Link.vp Rd)
    (T : (hS St Blk).QueryCache) :
    (simulateQ (ΦR k) ((HTE skPrf oR pk t).run (msgs l))).run T =
      (fun z => ((z.1.1, msgs z.2), z.1.2)) <$>
        (simulateQ (PV k skPrf oR pk) ((simImpl pk t).run T)).run l := by
  rcases t with n | q | m
  · simp only [HTE, QueryImpl.apply_compose, Ideal.Realize.Msg.signPC, simulateQ_spec_query, harnP,
      simImpl]
    simp only [StateT.run_monadLift, monadLift_self]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind,
      simulateQ_query]
    rfl
  · simp only [HTE, QueryImpl.apply_compose, Ideal.Realize.Msg.signPC, simulateQ_spec_query, harnP,
      simImpl]
    rw [simStep_PV]
    simp only [StateT.run_monadLift, monadLift_self]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      Functor.map_map]
    unfold portQT
    rw [simulateQ_spec_query]
    simp only [map_eq_bind_pure_comp, Function.comp_def, ΦR, QueryImpl.apply_compose, restrictPT]
    erw [simulateQ_spec_query]
    rfl
  · simp only [HTE, QueryImpl.apply_compose, Ideal.Realize.Msg.signPC, simulateQ_map, simImpl]
    erw [simulateQ_spec_query]
    simp only [harnP, harnessSignOracle, StateT.run_map, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_modify, StateT.run_pure, simulateQ_map, simulateQ_bind,
      simulateQ_pure, bind_assoc, pure_bind]
    rw [ΦR_embQT, sign_romO]
    erw [simulateQ_spec_query]
    simp only [StateT.run_map, PV, QueryImpl.add_apply_inr, run_appendLog_apply, map_bind,
      Functor.map_map, bind_map_left, map_pure, msgs, List.map_append, List.map_cons,
      List.map_nil, bind_assoc, pure_bind]

end ForgerE

section AssemblyE

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))

theorem forger_phaseE (k skPrf : Bytes 16) (pk : PublicKeyCore Cr) (T : (hS St Blk).QueryCache) :
    (simulateQ (ΦR k) ((simulateQ (harnP (portQT pk) (harnessSignOracle (vp := Link.vp)
        (prims := Rd) (fun m => simulateQ embQT
        (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m)))) (mainC S pk)).run [])).run T =
      (fun z => ((readOut z.1.1, msgs z.2), z.1.2)) <$>
        (simulateQ (PV k skPrf oR pk)
          ((simulateQ (simImpl pk) (S.main (encodePublicKey Wots.codec₀ pk))).run T)).run [] := by
  unfold mainC Ideal.Realize.Msg.typedC
  rw [simulateQ_map, StateT.run_map, simulateQ_map, StateT.run_map, ← QueryImpl.simulateQ_compose]
  have h := swap_nest_map msgs _ _ _ _ (forger_stepE k skPrf oR pk)
    (S.main (encodePublicKey Wots.codec₀ pk)) [] T
  erw [h]
  simp only [Functor.map_map]
  rfl

open scoped Classical in
/-- **VCVio's EUF experiment of the simulator after drawing `PK.seed` and `SK.seed = k`.** -/
noncomputable def WexpE (pkSeed k : Bytes 16) : OracleComp RS Bool := do
  let skPrf ← (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp RS (Bytes 16))
  let root ← (GeneralScheme.keygenInternalWithSecretM Cr (oracleSecret Cr (Equiv.refl _) pkSeed k)
    pkSeed : OracleComp RS Cr.Y)
  let z ← (simulateQ (PV k skPrf oR ⟨pkSeed, root⟩)
    ((simAdv S oR ($ᵗ (Bytes 16))).main ⟨pkSeed, root⟩)).run []
  let v ← (GeneralScheme.verifyInternalM Link.vp Cr z.1.1 z.1.2 ⟨pkSeed, root⟩ : OracleComp RS Bool)
  pure (!z.2.wasQueried z.1.1 && v)

theorem bRestE_eq_WexpE (k pkSeed : Bytes 16) :
    Prod.fst <$> (simulateQ (ΦR k) (bRestOpenPT oR (mainC S) pkSeed)).run ∅ =
      WexpE S oR pkSeed k := by
  unfold bRestOpenPT WexpE
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  erw [ΦR_liftM]
  simp only [bind_map_left]
  refine bind_congr fun skPrf => ?_
  erw [ΦR_embQT, keygen_romO]
  simp only [bind_map_left]
  refine bind_congr fun root => ?_
  erw [forger_phaseE, simAdv_PV]
  simp only [bind_map_left]
  refine bind_congr fun z => ?_
  erw [ΦR_embQT, bind_map_left, verify_romO]
  refine bind_congr fun v => ?_
  simp only [QueryLog.wasQueried_eq_decide_mem_map_fst, msgs]
  by_cases h : (readOut z.1.1).1 ∈ List.map (fun e => e.fst) z.2 <;> simp [h]

theorem expE_eq : unforgeableExperiment (simAdvE S oR ($ᵗ (Bytes 16))) =
    (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun pkSeed =>
      (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun k => WexpE S oR pkSeed k := by
  unfold unforgeableExperiment
  rw [show (romS oR ($ᵗ (Bytes 16))).keygen = _ from romScheme_keygen Cr _ _ _]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun pkSeed => ?_
  refine bind_congr fun k => ?_
  unfold WexpE
  refine bind_congr fun skPrf => ?_
  refine bind_congr fun root => ?_
  erw [runWS_eq oR k skPrf ⟨pkSeed, root⟩]
  refine bind_congr fun z => bind_congr fun v => ?_
  simp only [QueryLog.wasQueried_eq_decide_mem_map_fst]
  congr

theorem yromE_inner (k : Bytes 16) :
    (simulateQ (romH k) (PprfET oR ($ᵗ (Bytes 16)) S)).run' ∅ =
      (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun pkSeed => WexpE S oR pkSeed k := by
  unfold PprfET
  rw [← QueryImpl.simulateQ_compose, StateT.run'_eq, simulateQ_bind, StateT.run_bind]
  erw [ΦR_liftM]
  simp only [bind_map_left, map_bind]
  exact bind_congr fun pkSeed => bRestE_eq_WexpE S oR k pkSeed

end AssemblyE

/-- **H3 (EUF), proved.** -/
theorem romGameEuf : RomGameEuf := by
  intro S oR
  unfold unforgeableAdvantage
  have hY : YromE S oR = (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun k =>
      (liftM ($ᵗ (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun pkSeed => WexpE S oR pkSeed k :=
    bind_congr fun k => yromE_inner S oR k
  rw [expE_eq, hY, rom_swap]

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.romH_embQT
#print axioms Ideal.Direct.Rom.keygen_romO
#print axioms Ideal.Direct.Rom.sign_romO
#print axioms Ideal.Direct.Rom.verify_romO
#print axioms Ideal.Direct.Rom.forger_phase
#print axioms Ideal.Direct.Rom.romGameSuf
#print axioms Ideal.Direct.Rom.romGameEuf

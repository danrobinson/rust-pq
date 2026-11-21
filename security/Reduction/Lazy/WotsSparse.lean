import Reduction.Lazy.Sparse

/-!
# Step 7 with a sparse table: `bWotsS`

`bWots A` (`Reduction.WotsEmbed`) samples the eager table `sampleTable` (`2 ^ 256` cells) and
uses only its FORS secret cells; the WOTS+ start values are drawn by the WOTS game.  `bWotsS A`
is the same adversary with the table replaced by `sparseOn vp prims (forsSkIdx vp)`: one uniform
value for each FORS leaf secret of the key structure and `default` elsewhere.

* `bWotsWith my A` — `bWots A` with the table sampler `my` as a parameter
  (`bWotsWith_sampleTable : bWotsWith (sampleTable vp prims) A = bWots A` by `rfl`);
* `hyb_bWotsWith_eq` — sampler-generic form of `hyb_bWots_eq`;
* `bWotsS A = bWotsWith (sparseOn vp prims (forsSkIdx vp)) A`;
* `stepWotsEmbed_sparse : StepWotsEmbed A (bWotsS A)`.

## Resources of `bWotsS A`

* **Fresh uniform samples of `choose`.**  `bWotsS_choose_eq`: `choose` is
  `Tables.sampleList prims.Y (forsSkIdx vp).length` (that many draws of `$ᵗ prims.Y`, by
  definition of `Tables.sampleList`), followed by the deterministic `chooseBody` at the table
  `Tables.updateList (fun _ => default) (forsSkIdx vp) xs`.  `chooseBody` contains no uniform
  query (it is built from `wColl`, `topsAt`, `get`/`modify` only).  The count is
  `bWotsS_sampleCount : (forsSkIdx vp).length = (forsLeafAddresses vp).length`, i.e.
  `2^h · k · 2^a` values.
* **Signing queries of `choose`.**  `bWotsS_choose_signed`: in every run of phase 1 of the WOTS
  game `hyb 0` the final signing history has pairwise distinct instance addresses, all in
  `wotsInsts vp` (at most one answered signing query per WOTS+ instance).
  `bWotsS_chooseBody_signed`: against the table-reading oracles (the form of the game used in the
  proof of the step; in law it is the game, `fresh_eq_sparse`) the run is deterministic, the
  game's history equals the mirrored history, every entry is the honest entry of its instance,
  and the addresses of the history are duplicate-free and are exactly the members of
  `wotsInsts vp`.  So every WOTS+ instance of the hypertree is signed exactly once.  No query is
  refused: `topsAt` queries instance `a` only if `a` is absent from the mirrored history (which
  equals the game's history) and `chooseBody` only asks for instances of `wotsInsts vp`.
* **Collection (`Thash`) queries of `choose`** (counting argument, not formalised): `msgAt` is
  evaluated once per WOTS+ instance (memoisation by `topsAt`) and once for `PK.root`.  A layer-0
  message is a FORS public key: `k·2^a` leaf hashes, `k·(2^a - 1)` node hashes, one `T_k`.  The
  root of each XMSS tree costs `2^h'` calls `T_len` and `2^h' - 1` node hashes.  With
  `2^h` bottom positions and `#trees = Σ_{ℓ<d} 2^(h - (ℓ+1)·h')` XMSS trees this is
  `2^h · (k·(2^(a+1) - 1) + 1) + #trees · (2^(h'+1) - 1)` collection queries, plus the re-evaluation
  of the top tree for `PK.root` (its `topsAt` calls are answered from the history):
  `2^(h'+1) - 1` more.  No chain-step tweak is queried (`x1_not_reserved`).
* **`forge`** has no oracle; it runs the forger once (`g2RunWith`) and reads the table only at
  FORS cells and the recorded history.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Lazy

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## The adversary with an abstract table sampler -/

/-- `bWots A` with the table sampler as a parameter. -/
noncomputable def bWotsWith (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) : WotsGame.Adversary prims where
  State := SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y
  choose := do
    let tbl ← (monadLift my : OracleComp (WSpec prims) (SecretTable vp prims))
    let (root, hist) ← (chooseBody tbl).run []
    return (tbl, hist, root)
  forge := fun st pkSeed => do
    let pk : PublicKeyCore prims.core := ⟨pkSeed, st.2.2⟩
    let ((msg, sig), _) ← g2RunWith A pk (signFromHist st.1 st.2.1 pk)
    return wotsAnswer st.1 st.2.1 pk msg sig

theorem bWotsWith_sampleTable (A : Forger vp prims optRand pkSeedDist) :
    bWotsWith (sampleTable vp prims) A = bWots A := rfl

theorem bWotsWith_choose_eq (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    (bWotsWith my A).choose = (monadLift my : OracleComp (WSpec prims) (SecretTable vp prims)) >>=
      fun tbl => (chooseBody tbl).run [] >>= fun x =>
        (pure (tbl, x.2, x.1) : OracleComp (WSpec prims) (bWotsWith my A).State) := rfl

/-- `WotsGame.hyb 0` at `bWotsWith my A`, with the start values requested from a fresh-sampling
block oracle. -/
theorem hyb_bWotsWith_eq (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    WotsGame.hyb pkSeedDist (wotsInsts vp) 0 (bWotsWith my A) =
      pkSeedDist >>= fun pk => my >>= fun tbl =>
        simulateQ (Tables.freshImpl Adrs (Vector prims.Y vp.params.len)) (qGame A pk tbl) := by
  unfold WotsGame.hyb
  refine bind_congr fun pk => ?_
  rw [oracles_eq_oraclesIn]
  have h1 := oraclesIn_run_lift (vp := vp) (prims := prims)
    (fun _ => ($ᵗ (Vector prims.Y vp.params.len) : ProbComp _)) (wotsInsts vp) pk my
    (fun tbl => (chooseBody tbl).run [] >>= fun x =>
      (pure (tbl, x.2, x.1) : OracleComp (WSpec prims) (bWotsWith my A).State)) []
  rw [bWotsWith_choose_eq, h1, bind_assoc]
  refine bind_congr fun tbl => ?_
  rw [simulateQ_qGame A pk tbl _ (fun _ => rfl) (fun ob => Tables.simulateQ_freshImpl_liftM ob)]
  rw [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine bind_congr fun r => ?_
  change ((g2RunWith A ⟨pk, r.1.1⟩ (signFromHist tbl r.1.2 ⟨pk, r.1.1⟩) >>= fun z =>
      (pure (wotsAnswer tbl r.1.2 ⟨pk, r.1.1⟩ z.1.1 z.1.2) : ProbComp _)) >>= fun x =>
      match r.2[x.1]? with
      | none => pure false
      | some (a, m, _, tops) =>
        pure (decide (x.2.1 ≠ m ∧ wotsPkFromSigTops prims x.2.2 x.2.1 pk a = tops))) = _
  rw [finish, bind_assoc]
  refine bind_congr fun z => ?_
  rw [pure_bind]
  simp only [WotsGame.win]
  split <;> rename_i heq <;> simp only [heq]

/-- The WOTS-game adversary built from a forger, sampling only the FORS secret cells of the key
structure (`(forsSkIdx vp).length = 2^h·k·2^a` uniform values). -/
noncomputable def bWotsS (A : Forger vp prims optRand pkSeedDist) : WotsGame.Adversary prims :=
  bWotsWith (sparseOn vp prims (forsSkIdx vp)) A

/-! ## Facts about restricted tables -/

theorem fors_not_wotsCell (hS : Structural vp prims) {i : SecIdx} (hi : i ∈ forsSkIdx vp) :
    ¬ IsWotsCell vp i := fun hw =>
  (List.disjoint_of_nodup_append (structSecIdx_nodup hS)) hi (mem_wotsSkIdx.2 hw)

/-- The table restricted to the FORS cells and the table restricted to the whole structure agree
off the WOTS+ cells. -/
theorem restrictTo_fors_agree (tbl : SecretTable vp prims) (i : SecIdx) (hi : ¬ IsWotsCell vp i) :
    restrictTo (forsSkIdx vp) tbl i = restrictTo (structSecIdx vp) tbl i := by
  have hw : i ∉ wotsSkIdx vp := fun h => hi (mem_wotsSkIdx.1 h)
  by_cases hf : i ∈ forsSkIdx vp
  · exact (restrictTo_apply_of_mem tbl hf).trans
      (restrictTo_apply_of_mem tbl (is := structSecIdx vp) (List.mem_append_left _ hf)).symm
  · exact (restrictTo_apply_of_not_mem tbl hf).trans
      (restrictTo_apply_of_not_mem tbl (is := structSecIdx vp)
        (fun h => (List.mem_append.1 h).elim hf hw)).symm

/-- Restricting to the FORS cells forgets everything about the WOTS+ cells. -/
theorem restrictTo_fors_congr (hS : Structural vp prims) {tbl tbl' : SecretTable vp prims}
    (h : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i) :
    restrictTo (forsSkIdx vp) tbl = restrictTo (forsSkIdx vp) tbl' := by
  funext i
  by_cases hf : i ∈ forsSkIdx vp
  · rw [restrictTo_apply_of_mem tbl hf, restrictTo_apply_of_mem tbl' hf]
    exact h i (fors_not_wotsCell hS hf)
  · rw [restrictTo_apply_of_not_mem tbl hf, restrictTo_apply_of_not_mem tbl' hf]

theorem readBlock_restrictTo_struct (tbl : SecretTable vp prims) {a : Adrs}
    (ha : a ∈ wotsInsts vp) :
    Tables.readBlock (restrictTo (structSecIdx vp) tbl) (wotsCells vp a) =
      Tables.readBlock tbl (wotsCells vp a) := by
  unfold Tables.readBlock
  refine congrArg Vector.ofFn (funext fun j => ?_)
  exact restrictTo_apply_of_mem tbl
    (List.mem_append_right _ (mem_wotsSkIdx.2 ⟨a, ha, j, rfl⟩))

theorem qGame_restrictTo (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) (tbl : SecretTable vp prims) :
    qGame A pk (restrictTo (forsSkIdx vp) tbl) = qGame A pk (restrictTo (structSecIdx vp) tbl) := by
  rw [qGame, qGame, chooseBody_congr hS (restrictTo_fors_agree tbl),
    finish_congr hS A pk (restrictTo_fors_agree tbl)]

/-! ## The probabilistic half with sparse tables -/

theorem fresh_eq_mid (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    𝒟[sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.freshImpl Adrs (Vector prims.Y vp.params.len))
          (qGame A pk (restrictTo (forsSkIdx vp) tbl))] =
      𝒟[sampleTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
          (qGame A pk (restrictTo (forsSkIdx vp) tbl))] := by
  have hempty : ({a : Adrs | a ∈ ([] : List (WotsGame.Entry prims)).map (·.1)} : Set Adrs) = ∅ := by
    ext a; simp
  refine evalDist_sampleTable_bind_freshImpl_block (wotsCells vp) (S := {a | a ∈ wotsInsts vp})
    (fun a ha a' ha' j j' h => wotsCell_inj hS a ha a' ha' j j' h)
    (fun tbl => qGame A pk (restrictTo (forsSkIdx vp) tbl))
    (fun tbl => q_queriesIn pk _ _ _) (fun tbl => hempty ▸ q_noRepeat pk _ _ _) ?_
  intro tbl tbl' h
  have h' : ∀ i, ¬ IsWotsCell vp i → tbl i = tbl' i :=
    fun i hi => h i fun d hd j hji => hi ⟨d, hd, j, hji⟩
  exact congrArg (qGame A pk) (restrictTo_fors_congr hS h')

theorem fnImpl_qGame_restrictTo (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) (tbl : SecretTable vp prims) :
    simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
        (qGame A pk (restrictTo (forsSkIdx vp) tbl)) =
      simulateQ (Tables.fnImpl fun a =>
          Tables.readBlock (restrictTo (structSecIdx vp) tbl) (wotsCells vp a))
        (qGame A pk (restrictTo (structSecIdx vp) tbl)) := by
  rw [qGame_restrictTo hS A pk tbl]
  exact Tables.simulateQ_fnImpl_congr (S := {a | a ∈ wotsInsts vp}) (q_queriesIn pk _ _ _)
    fun a ha => (readBlock_restrictTo_struct tbl ha).symm

/-- **Fresh start values next to the sparse FORS table = one sparse structure table.** -/
theorem fresh_eq_sparse (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    𝒟[sparseOn vp prims (forsSkIdx vp) >>= fun tbl =>
        simulateQ (Tables.freshImpl Adrs (Vector prims.Y vp.params.len)) (qGame A pk tbl)] =
      𝒟[sparseTable vp prims >>= fun tbl =>
        simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
          (qGame A pk tbl)] := by
  refine (evalDist_sparseOn_bind (forsSkIdx_nodup hS) _).trans ?_
  refine (fresh_eq_mid hS A pk).trans ?_
  refine Eq.trans ?_ (evalDist_sparseOn_bind (structSecIdx_nodup hS)
    (fun tbl => simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
          (qGame A pk tbl))).symm
  exact congrArg (fun f => 𝒟[sampleTable vp prims >>= f])
    (funext fun tbl => fnImpl_qGame_restrictTo hS A pk tbl)

/-- **Step 7 with the sparse adversary.** -/
theorem stepWotsEmbed_sparse (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    StepWotsEmbed A (bWotsS A) := by
  unfold StepWotsEmbed bWotsS
  rw [hyb_bWotsWith_eq, prTrue_g2Class_eq_sparse hS A .wots]
  calc prTrue (pkSeedDist >>= fun pkSeed => sparseTable vp prims >>= fun tbl =>
        g2ClassAt A .wots pkSeed tbl)
      ≤ prTrue (pkSeedDist >>= fun pk => sparseTable vp prims >>= fun tbl =>
          simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
            (qGame A pk tbl)) :=
        prTrue_bind_bind_mono pkSeedDist (sparseTable vp prims) _ _ (table_step hS A)
    _ = _ := prTrue_bind_congr _ _ _ fun pk _ => prTrue_congr (fresh_eq_sparse hS A pk).symm

/-! ## Resources of `bWotsS` -/

/-- **Fresh samples of `choose`.**  Phase 1 of `bWotsS A` draws exactly the list
`Tables.sampleList prims.Y (forsSkIdx vp).length` of uniform values and is otherwise the
sampling-free program `chooseBody` at the table holding these values at the FORS cells. -/
theorem bWotsS_choose_eq (A : Forger vp prims optRand pkSeedDist) :
    (bWotsS A).choose =
      (monadLift (Tables.sampleList prims.Y (forsSkIdx vp).length) :
        OracleComp (WSpec prims) (List prims.Y)) >>= fun xs =>
        (chooseBody (Tables.updateList (fun _ => default) (forsSkIdx vp) xs)).run [] >>= fun x =>
          (pure (Tables.updateList (fun _ => default) (forsSkIdx vp) xs, x.2, x.1) :
            OracleComp (WSpec prims) (bWotsS A).State) := by
  have h : (monadLift (sparseOn vp prims (forsSkIdx vp)) :
      OracleComp (WSpec prims) (SecretTable vp prims)) =
      (fun xs => Tables.updateList (fun _ => default) (forsSkIdx vp) xs) <$>
        (monadLift (Tables.sampleList prims.Y (forsSkIdx vp).length) :
          OracleComp (WSpec prims) (List prims.Y)) :=
    OracleComp.liftComp_map _ _ _
  unfold bWotsS
  rw [bWotsWith_choose_eq, h, bind_map_left]

/-- The number of uniform values drawn by `bWotsS A`: one per FORS leaf of the key structure. -/
theorem bWotsS_sampleCount : (forsSkIdx vp).length = (forsLeafAddresses vp).length :=
  forsSkIdx_length

/-- A signing history whose instance addresses are pairwise distinct and allowed. -/
def HistInv (vp : ValidatedParams) {prims : Primitives vp.params}
    (s : List (WotsGame.Entry prims)) : Prop :=
  (s.map (·.1)).Nodup ∧ ∀ a ∈ s.map (·.1), a ∈ wotsInsts vp

theorem histInv_nil : HistInv vp ([] : List (WotsGame.Entry prims)) := by
  simp [HistInv]

theorem histInv_append {s : List (WotsGame.Entry prims)} (hs : HistInv vp s)
    (e : WotsGame.Entry prims) (h1 : e.1 ∈ wotsInsts vp) (h2 : e.1 ∉ s.map (·.1)) :
    HistInv vp (s ++ [e]) := by
  refine ⟨?_, fun a ha => ?_⟩
  · rw [List.map_append, List.map_singleton]
    exact List.Nodup.append hs.1 (List.nodup_singleton _)
      (fun x hx hx' => h2 (List.mem_singleton.1 hx' ▸ hx))
  · rw [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hs.2 a ha
    · exact h1

/-- The game's signing history keeps `HistInv`, however the start values are produced. -/
theorem q_histInv {α : Type} (pk : prims.PkSeed) (I : QueryImpl (QSpec prims) ProbComp)
    (c : OracleComp (WSpec prims) α) (s : List (WotsGame.Entry prims)) (hs : HistInv vp s) :
    ∀ z ∈ support (simulateQ I ((simulateQ (qOracles (vp := vp) pk) c).run s)), HistInv vp z.2 := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hs
  | query_bind t k ih =>
    intro z hz
    rw [q_run_bind] at hz
    rcases t with n | q | q
    · rw [q_step_unif] at hz
      simp only [bind_assoc, pure_bind, simulateQ_bind, support_bind, Set.mem_iUnion] at hz
      obtain ⟨u, -, hz⟩ := hz
      exact ih u s hs z hz
    · rw [q_step_sign] at hz
      split_ifs at hz with h
      · simp only [pure_bind] at hz
        exact ih _ s hs z hz
      · simp only [bind_assoc, pure_bind, simulateQ_bind, support_bind, Set.mem_iUnion] at hz
        obtain ⟨u, -, hz⟩ := hz
        simp only [not_or, not_not] at h
        exact ih _ _ (histInv_append hs _ h.1 h.2) z hz
    · rw [q_step_coll] at hz
      simp only [pure_bind] at hz
      exact ih _ s hs z hz

/-- **Signing queries of `choose`, in the WOTS game.**  In every run of phase 1 of `hyb 0`
against `bWotsWith my A` the recorded signing history has pairwise distinct instance addresses,
all among `wotsInsts vp`: at most one signature per WOTS+ instance of the hypertree, hence at
most `(wotsInsts vp).length` answered signing queries. -/
theorem bWotsWith_choose_signed (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (WotsGame.oracles 0 (wotsInsts vp) pk) (bWotsWith my A).choose).run
        ([] : List (WotsGame.Entry prims))),
      (z.2.map (·.1)).Nodup ∧ ∀ a ∈ z.2.map (·.1), a ∈ wotsInsts vp := by
  intro z hz
  rw [oracles_eq_oraclesIn, bWotsWith_choose_eq, oraclesIn_run_lift, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨tbl, -, hz⟩ := hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  obtain ⟨r, hr, hz⟩ := Set.mem_iUnion₂.1 hz
  have hI := q_push (vp := vp) (prims := prims)
    (Tables.freshImpl Adrs (Vector prims.Y vp.params.len)) (fun _ => rfl) pk
    ((chooseBody tbl).run []) []
  have hr' : HistInv vp r.2 := q_histInv pk _ _ [] histInv_nil r (by rw [hI]; exact hr)
  have hz' : z ∈ support (pure ((tbl, r.1.2, r.1.1), r.2) :
      ProbComp ((SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) ×
        List (WotsGame.Entry prims))) := hz
  rw [support_pure] at hz'
  rw [Set.mem_singleton_iff.1 hz']
  exact hr'

theorem bWotsS_choose_signed (A : Forger vp prims optRand pkSeedDist) (pk : prims.PkSeed) :
    ∀ z ∈ support ((simulateQ (WotsGame.oracles 0 (wotsInsts vp) pk) (bWotsS A).choose).run
        ([] : List (WotsGame.Entry prims))),
      (z.2.map (·.1)).Nodup ∧ ∀ a ∈ z.2.map (·.1), a ∈ wotsInsts vp := by
  unfold bWotsS
  exact bWotsWith_choose_signed (sparseOn vp prims (forsSkIdx vp)) A pk

/-- **Signing queries of `choose`, against the table-reading oracles** (the form used in the
proof of the step).  The run of `chooseBody` is deterministic; the game's history equals the
mirrored history, consists of honest entries, and its instance addresses are duplicate-free and
are exactly the instances of `wotsInsts vp`: every WOTS+ instance of the hypertree is signed
exactly once. -/
theorem bWotsS_chooseBody_signed (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : prims.PkSeed) :
    ∃ hist, (simulateQ (tblOracles tbl pk) ((chooseBody tbl).run [])).run [] =
        pure ((idealRoot vp prims tbl pk, hist), hist) ∧ HistGood tbl pk hist ∧
      (hist.map (·.1)).Nodup ∧ ∀ a, a ∈ hist.map (·.1) ↔ a ∈ wotsInsts vp := by
  obtain ⟨hist, hrun, hg⟩ := chooseBody_run hS tbl pk
  have hI := q_push (vp := vp) (prims := prims)
    (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a)) (fun _ => rfl) pk
    ((chooseBody tbl).run []) []
  have hI' : simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
      ((simulateQ (qOracles (vp := vp) pk) ((chooseBody tbl).run [])).run []) =
      pure ((idealRoot vp prims tbl pk, hist), hist) := hI.trans hrun
  have hinv : HistInv vp hist :=
    q_histInv pk _ _ [] histInv_nil ((idealRoot vp prims tbl pk, hist), hist)
      (by rw [hI']; exact Set.mem_singleton _)
  exact ⟨hist, hrun, hg, hinv.1, fun a => ⟨hinv.2 a, hg.2 a⟩⟩

end Lazy
end Reduction

#print axioms Reduction.Lazy.stepWotsEmbed_sparse
#print axioms Reduction.Lazy.bWotsS_choose_eq
#print axioms Reduction.Lazy.bWotsS_choose_signed
#print axioms Reduction.Lazy.bWotsS_chooseBody_signed

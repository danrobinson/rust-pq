# R-tcr — class-TCR realisers (agent `tcr`)

State: **done** for SUF and EUF, all four arities (in fact every `n`). All files build with
`lake build <module>`; `#print axioms` of every headline ⊆ `[propext, Classical.choice, Quot.sound]`.
Not wired into `Ideal.lean` (coordinator: add the three modules below).

## Modules (new, owned by `tcr`)
- `Ideal/Transport/AdvTcr.lean` — whole-adversary `setPrf` invariance of `bTcrArM n`.
- `Ideal/Realize/Tcr.lean` — the ideal-model adversary `advT` and the experiment equality.
- `Ideal/Realize/TcrCount.lean` — counts, `tcrP`, the realisers, `P5.Le` bounds.

## Headline statements (verbatim)
`Ideal/Transport/AdvTcr.lean:59` (and SUF twin `:81`, `bTcrArM_bytesToTypedS_setPrf`):
```
theorem bTcrArM_bytesToTyped_setPrf (n : ℕ)
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte)) :
    bTcrArM (prims := setPrf prims prf pm) n
        (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) =
      bTcrArM n (bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩)
```
(section hypothesis `hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk`; plain `=` of adversaries.)

`Ideal/Realize/Tcr.lean:196`:
```
theorem advT_eq (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (n : ℕ) (g : CF St Blk) :
    𝒟[SM_DT_TCR_Experiment (bTcrArM n (S.typedS (optRandU oR) pkSeedDist g))] =
      𝒟[SM_DT_TCR_Experiment (instRT (advT S oR pkSeedDist n) g)]
```
`Ideal/Realize/TcrCount.lean:266` (EUF twin `realizesTcrE` `:286`; named instances
`realizesTcr{F,H,Len,K}_{S,E}` `:350–381` for `n = 1, 2, Link.vp.params.len, Link.vp.params.k`):
```
noncomputable def realizesTcrS   -- variables: (S : ForgerI) (oR) (pkSeedDist) (n) {qf qs ℓ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    RealizesTcr pkSeedDist n (fun g => Reduction.bTcrArM n (S.typedS (optRandU oR) pkSeedDist g))
      (tcrP qf qs ℓ)
```
Parameters (`TcrCount.lean:258`): `tcrP qf qs ℓ = ⟨q₁ := 0, qch := tcrTargets Link.vp,
qc := tcrTargets Link.vp, L := tcrL, q₂ := q₂T qf qs ℓ⟩`, where
`q₂T qf qs ℓ = qf·1 + hashBudget qs · thashCost Bmax + (qs+1) · hmsgCost ℓ`,
`hashBudget qs = keygenHashes + qs·signHashes + (1 + verifyHashes·2)` (the count of
`tcrMOpenP_hashes` = `tcrM_phase2_open_hashes`), `Bmax = len`, `tcrL = (22+16·len+8)/64`.
Bounds: `tcrP_le : (tcrP qf qs ℓ).Le (QcT qf qs ℓ) (tcrTargets Link.vp)` (`:301`),
`tcrP_le_of` (any larger caps), `q₂T_128s : q₂T qf qs ℓ = qf + (269824 + qs*2007385 + 7857)*11
+ (qs+1)*((ℓ+56)/64+3)`, `q₂T_le : q₂T ≤ qf + (qs+1)*(25135729 + (ℓ+56)/64)`,
`tcrP_le_2_81 : qf + (qs+1)*(25135729+(ℓ+56)/64) ≤ Qc → (tcrP qf qs ℓ).Le Qc (2^81)`,
`tcrP_128s_consts : tcrTargets Link.vp < 2^80 ∧ tcrL = 9`.

Hypotheses: exactly `hqf hqs hlong hout` in the agreed form. Nothing else.
Not via `RealizesTcr.ofEq`: the adversaries are NOT equal (the ideal adversary clamps the stored
list, see below); the `eq` field is proved directly at the level of experiment distributions.

## Recipe (two-phase pattern; for `fors`, `wots`)
1. **Transport** (`Transport/AdvTcr.lean`): first phase by `Open.bTcrArM_choose_eq` + `krfl`
   (forger-free program, same term at both bundles); second phase `bTcrArM_forge_setPrf` with
   `hrun := g2Run_bytesToTyped_tr …`; assemble with `tcrAdv_ext_AdvTcr` (cases on the structures,
   `State` by `rfl`, phases by `heq_of_eq`).
2. **step1** (`Tcr.lean`): instantiate it at `prims := R₀ (thG g) (hmG g)`, `prf := prfG g`,
   `pm := pmG g`, `codec := codec₀`, `optRand := optRand₀ oR`, `optRand' := optRandU oR g`,
   `hopt := fun _ => rfl`. `primsG (liftC g) = setPrf (R₀ …) … := rfl` makes the statement
   typecheck with no comparison of SHA terms. Result: adversary over `R₀ (thG g) (hmG g)` built
   from the byte forger with port answered by `g` (`B₀`).
3. **Ideal adversary over `P₀ = R₀ dT dH`**: state `TcrP1State Link.vp P₀`; choose
   `simulateQ embImpl (tcrPhase1 Link.vp P₀ n : …)` (TYPE-ASCRIBE the inner program);
   forge `forgeP … st.1 (clampL Bmax st.2)` with `forgeP tbl L pk = simulateQ (chainImpl tbl)
   (tcrMOpenP (optRand₀ oR) (typedP codec₀ S.main) L pk) >>= pure ∘ classOut P₀ n L`.
4. **Second phase at `g`** (`forgeP_inst`): `tcrM_phase2_open_eq` at `R₀ (thG g) (hmG g)` +
   `instImpl₀_liftM`; on the other side `chainImpl_inst … (hashC_inst g)`,
   `← QueryImpl.simulateQ_compose` (twice), `tcrMOpenP_fusion` with
   `φ := instImpl₀ g ∘ₛ Lazy.tblImpl (implTH …) tbl` (`hφ := fun q => rfl`), `typedP_inst`
   (pass `(vp := Link.vp) (prims := P₀)` explicitly!), `← impl_R₀`, `bytesToTypedS_open_main
   (prims := P₀) (thG g) (hmG g)` (turns `B₀`'s main into the `P₀` main WITHOUT comparing bundles),
   `tcrMOpen_withTH (prims := P₀)`, `simp only [classOut_withTH (prims := P₀) …]`.
5. **First phase at `g`**: `advT_choose_inst` by `kexact instImpl_emb g (tcrPhase1 … : …)`;
   `bTcrArM_choose_eq` + `tcrPhase1_withTH (prims := P₀) (thG g) (hmG g) n`.
6. **Clamp**: `routeHF_clamp … (tcrChooseHF_len Bmax …) [] (by simp)` gives
   `φ <$> tcrPhase1 = tcrPhase1`; `experiment_map_choose` moves `φ` into the second phase.
7. **Assembly** (`advT_eq`): all intermediate equalities stated at the problem over
   `R₀ (thG g) (hmG g)` (`hB_lem` via `exp_choose_congr`, `hE_lem`); only the last step crosses to
   the `primsG (liftC g)` problem, by `kexact`.
8. **Counts** (`TcrCount.lean`): second phase by `qb_simulateQ_classes` with classes
   bad (`isBadIdx Bmax ℓ`, from `tcrMOpenP_bad`), port (`kind = .game`, `tcrMOpenP_port`), `Thash`
   (`isThIdx`, bounded by the hash count `tcrMOpenP_hashes` via `of_imp`), `H_msg`
   (`tcrMOpenP_hmsg`), step lemma `chainImpl_step`; forger hypotheses moved to `typedP` by
   `typedP_bound`/`typedP_out` (explicit `pb`, `pt`, and `(vp := Link.vp) (prims := P₀)`).
   First phase: `rw [advT_choose]`, `generalize hoa : (tcrPhase1 … : Ph1 n) = oa`, then
   `emb_noH`/`emb_bound` with lemmas about `oa` given `hoa`; `routeHF_cap`, `routeHF_len`,
   `isQueryBoundP_zero_iff` for `CollLen`.

## Pitfalls (each cost an hour)
- **Never let the elaborator compare programs over different bundles** (`P₀` vs
  `R₀ (thG g) (hmG g)` vs `primsG (liftC g)`) or with syntactically different but defeq specs: it
  unfolds `simulateQ`/the program and dies (max recursion / timeout). Use `kexact`/`krfl` (kernel)
  or generic `…_withTH`/`…_open_main` lemmas. Type-level comparisons are cheap and fine.
- **Closed `IsQueryBoundP` statements about the key-structure walk explode**: any statement (even
  `theorem … := sorry`) whose type is `IsQueryBoundP (tcrChooseHF Link.vp P₀) …` makes `whnf`
  evaluate `structSecIdx Link.vp`. Fix: `attribute [local irreducible] Reduction.Lazy.sparseTable
  Reduction.Lazy.structSecIdx` (and `Reduction.arityTargets Reduction.tcrTargets`); prefer lemmas
  over an fvar `oa` with `hoa : oa = <program>` and `generalize` the constant away.
- `have h := lemma args` whose type is an `IsQueryBoundP` of a closed program also explodes; same fix.
- `IsQueryBoundP.of_imp` synthesizes its `DecidablePred` instances and fails when the index type
  is still a metavariable: use `of_imp'` (`TcrCount.lean`, instances as `{}` binders).
- `typedP_bound`/`typedP_inst`/`typedP_out`: pass `(vp := …) (prims := …)`; otherwise
  `prims.core =?= core₀` is a non-pattern unification and times out.
- `classical` + `isQueryBoundP_zero_iff`: rewrite the goal with `← isQueryBoundP_zero_iff` so the
  instance comes from the goal, then supply the proof via `of_imp'`.

## Not done / not verified
- Not wired into `Ideal.lean`; not composed into `SufRealizers` (other fields belong to other agents).
- `qch, qc = tcrTargets` (≈ 2^79.8) are the router cap, not the finer `arityTargets n` split.
- Second-phase count charges every hash query (incl. `H_msg`) as a `Thash` chain on `len` values
  and the `H_msg` queries again at `hmsgCost ℓ`: an over-count (≤ 2× on the `H_msg` part), not tight.

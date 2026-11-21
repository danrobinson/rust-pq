# R-itsr — the twelfth realiser `RealizesItsrF` (agent `itsr`)

State: **done**, sorry-free; `lake build Ideal.Realize.Itsr` → `Build completed successfully (7258 jobs)`.
Every `#print axioms` line of the six files ⊆ `[propext, Classical.choice, Quot.sound]`.
Modules to add to `Ideal.lean`: `Ideal.Realize.Itsr` (imports the five others:
`ItsrWalk`, `ItsrOpen`, `ItsrCount`, `ItsrReal`, `ItsrBound`). New import of an existing
non-default module: `Ideal.Transport.AdvItsr` (for `bItsrL_setPrf`, `bItsrL_setPrf_S`).
No existing file was edited. Namespace `Ideal.Realize.Itsr`.

## Headline results (`Ideal/Realize/Itsr.lean`)

Common hypotheses (exactly the agreed form; nothing else):
```
(hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
(hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
(hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
(hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
```
`S : ForgerI`, `oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)`, `d : ProbComp (Bytes 16)` (any
public-seed distribution).

* `:60` `noncomputable def realizesItsrS … : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS (optRandU oR) d g)) qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ`
* `:79` `noncomputable def realizesItsrE … : RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedE (optRandU oR) d g)) qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ`
* `:98` `theorem itsrSufI_le_optRandU … : itsrSufI S (optRandU oR) d ≤ epsItsrF qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ`
* `:107` `theorem itsrEufI_le_optRandU … : itsrEufI S (optRandU oR) d ≤ epsItsrF qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ`
* parameters: `:42` `def itsrQc (qs : ℕ) : ℕ := Lazy.keygenHashes Link.vp + qs * Lazy.signHashes Link.vp + qs`;
  `:44` `itsrQc_eq : itsrQc qs = 269824 + qs * 2007386`;
  `ItsrBound.lean:427` `def itsrLc (ℓ : ℕ) : ℕ := max (thashCost thMax) ((ℓ + 56) / 64 + 1)` with
  `thMax := max 2 (max Link.vp.params.len Link.vp.params.k)`; `:51` `itsrLc_eq : itsrLc ℓ = max 11 ((ℓ + 56) / 64 + 1)`.
* `:120` `def raiseItsr` (same program, larger parameters); realisers at the parameters of the
  closed theorems of `ComposeFinal`: `realizesItsrS_2_60_2_20` / `E` (`qf ≤ 2^60, qs ≤ 2^20, ℓ ≤ 2^26`),
  `realizesItsrS_2_80_2_40` (`qf ≤ 2^64, qs ≤ 2^40`), `realizesItsrS_2_90_2_64` / `E` (`qf ≤ 2^64, qs ≤ 2^64`).
* Plugged in (the eleven `SufRealizers`/`EufRealizers` still hypotheses): `:229`
  `suf_final_optRandU_itsr`, `:242` `euf_final_optRandU_itsr`, `:256` `suf_final_2_60_2_20_itsr`
  (`sufI S (optRandU oR) ($ᵗ _) ≤ 2^-70 + 2^-128 + 2^-61`), `:269` `euf_final_2_60_2_20_itsr`.

## Accounting (what each parameter is, proved)
* `qP = q = qf`: the only raw compression queries are the forger's own (`itsrA_raw`, `itsrA_rawP`).
  All of the Reduction's hashing is issued as CHAIN queries.
* `cP = 2·qs` (`ItsrBound.lean:383` `itsrA_chainP`): chain queries with second block `cB` are only
  the inner and outer chain of each of the ≤ `qs` `H_msg` evaluations (the inner chain's second
  block is message bytes, so it may be `cB`; both counted). `itsrOpen` has no final check, so
  no `(qs+1)`-th `H_msg`. No `PRF`/`PRF_msg` chains exist: secrets are lazily drawn, randomizers
  are target queries.
* Block lemmas (`ItsrWalk.lean`): `tblocks_one_ne_cB'` (F, byte 38), `tblocks_two_ne_cB` (H, byte 54),
  `tblocks_ne_cB_of_key9` (any arity, key byte 9 ≠ 0), `key9_wotsPk`, `key9_forsPk`
  (`T_len` at `wotsPkAdrs b`, `T_k` at `forsPkAdrs b`: byte 9 is the type byte 1 / 4, or 7 on the
  fallback key). The walks were re-proved with the `T_ℓ` hypothesis restricted to these addresses
  (`npA_*`, `npA_openKeygen`, `npA_openSign`), giving `itsrOpenP_badKey` and `thBlocks_secondP`.
* `qc = itsrQc qs` (`itsrA_chain`): one chain per `Thash`, two per `H_msg`; from
  `itsrOpenP_hashes` (same closed form as `Reduction.Open.itsrOpen_hashes`) and `itsrOpenP_hmsg`.
* `Lc = itsrLc ℓ` (`itsrA_chainLen`): `Thash` chains have `thashCost |xs|` blocks, all `|xs|` are
  `1, 2, len, k`; `H_msg` chains have `(|M|+56)/64+1` and `2` blocks.
* `qs` target queries (`itsrA_tgt`), on messages ≤ ℓ (`itsrA_tgtOK`); output message ≤ ℓ (`itsrA_out`).

## Construction (one program for all tables)
`ItsrReal.lean:82` `itsrA S oR d := simulateQ outerImpl (lazyRes (itsrOpenP (prims := P₀) (oR₀ oR) d (typedP codec₀ S.main)))`
over the reference core `core₀` (`P₀ := R₀ dT dH`). Correctness at every `g`: `itsrA_adv_eqS`/`E`
(`:222`/`:211`) = `transportS`/`E` (`bItsrL_setPrf(_S)` with `primsG (liftC g) ≡ setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g)`)
+ `itsrA_main_eq_gen` (fusion of the port `itsrOpenP_fusion`, `lazyRes_portAns`, chains =
`thG`/`hmG` by `thG_shape`/`hmG_shape`, and `itsrOpenP_TH`, a kernel-checked `krfl`: the open
program does not depend on `Thash`/`H_msg`).

## Not done / caveats
* Nothing open for this realiser. The eleven other realisers remain hypotheses of the composed theorems.
* Known limitation (accepted): `qP` includes the forger's own `cB`-shaped compression queries.
* `itsrOpenP_TH` and the last step of `itsrA_main_eq_gen` use `krfl` (kernel-only `Eq.refl`, no axiom).
* Not audited by anyone else.

import Ideal.Realize.ItsrCount
import Ideal.Transport.AdvItsr

/-!
# The ITSR realiser: the program and its correctness

* `codec₀`, `oR₀ oR` — the wire codec and the `opt_rand` sampler over the reference core `core₀`;
* `hashCh` — a hash query of `core₀` as CHAIN queries of the fine ITSR game (`Thash`: one chain
  `sb128 pk, tblocks a xs`; `H_msg`: the inner and the outer chain of `hmsg_shape`);
* `outerImpl` — the resource-explicit open program (secrets drawn lazily) interpreted over the
  fine ITSR interface `unifSpec + (aS St Blk + ITSRTargetSpec X128 (Bytes 16))`: port queries
  become raw compression queries, target queries target queries, draws uniform samples, hash
  queries chains;
* **`itsrA S oR d`** — the realising program (one program for all tables);
* `itsrA_main_eq` — at every table `g`, the ITSR adversary of the Reduction built from the
  forger is `instItsrF (itsrA S oR d) g` (equality of `main`), for the EUF (`typedE`) and the
  SUF (`typedS`) wrappers; `itsrA_adv_eqE`, `itsrA_adv_eqS` — equal advantages.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security KeyedHash

namespace Ideal.Realize.Itsr

open Reduction Reduction.Lazy Ideal.Realize Ideal.Itsr Ideal.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Data over the reference core -/

/-- The wire codec over `core₀` (every carrier is `Bytes 16`, encoded as itself). -/
def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

/-- The table-independent `opt_rand` sampler over `core₀`. -/
def oR₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) :
    ProbComp (Bytes 16) :=
  oR pk.pkSeed pk.pkRoot

/-- The bundle over which the realising program is written (its `Thash`, `H_msg` are never
evaluated). -/
abbrev P₀ : Primitives Link.vp.params := R₀ dT dH

/-! ## The fine ITSR interface -/

/-- The interface of the fine ITSR game at 128s. -/
abbrev ASpec := unifSpec + (aS St Blk + ITSRTargetSpec X128 (Bytes 16))

/-- A chain query. -/
def chQ (bs : List Blk) : OracleComp ASpec St :=
  (liftM (ASpec.query (.inr (.inl (.inr bs)))) : OracleComp ASpec St)

/-- The blocks of the chain of `Thash(pk, a, xs)`. -/
def thBlocks (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) : List Blk :=
  sb128 pk :: (tblocks a xs).1 :: (tblocks a xs).2

/-- A hash query of `core₀` as chain queries. -/
def hashCh : QueryImpl (publicHashSpec core₀) (OracleComp ASpec)
  | .thash pk a xs => out16 <$> chQ (thBlocks pk a xs)
  | .hmsg R pk root M => do
      let s ← chQ (iblocksH R pk root M)
      let s' ← chQ (oblocksH R pk s)
      return dig30 s'

/-- The interface of the resource-explicit open program. -/
abbrev USpec := RSpec (gI P₀) Unit (Bytes 16) (publicHashSpec core₀)

/-- **The interpretation of the resource-explicit open program in the fine ITSR game.** -/
noncomputable def outerImpl : QueryImpl USpec (OracleComp ASpec)
  | .inl n => (liftM (ASpec.query (.inl n)) : OracleComp ASpec _)
  | .inr (.inl (.inl x)) => (liftM (ASpec.query (.inr (.inr x))) : OracleComp ASpec _)
  | .inr (.inl (.inr q)) => (liftM (ASpec.query (.inr (.inl (.inl q)))) : OracleComp ASpec _)
  | .inr (.inr (.inl _)) => (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp ASpec _)
  | .inr (.inr (.inr h)) => hashCh h

/-- **The realising program**: the open ITSR program of the forger's typed port program, secrets
drawn lazily, interpreted by `outerImpl`. -/
noncomputable def itsrA (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (d : ProbComp (Bytes 16)) : OracleComp ASpec (Bytes 16 × X128) :=
  simulateQ outerImpl
    (lazyRes (itsrOpenP (prims := P₀) (oR₀ oR) d (typedP codec₀ S.main)))

/-! ## Correctness -/

theorem instImplF_liftM (g : CF St Blk) {β : Type} (ob : ProbComp β) :
    simulateQ (instImplF IV128 g) (liftM ob : OracleComp ASpec β) = liftM ob := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    congr 1

theorem instImplF_chQ (g : CF St Blk) (bs : List Blk) :
    simulateQ (instImplF IV128 g) (chQ bs) = pure (mdFold g IV128 bs) := by
  unfold chQ
  rw [simulateQ_spec_query]
  rfl

/-- **The chains compute the hash functions over the table.** -/
theorem hashCh_inst (g : CF St Blk) (h : (publicHashSpec core₀).Domain) :
    simulateQ (instImplF IV128 g) (hashCh h) =
      pure (f := OracleComp (unifSpec + ITSRTargetSpec X128 (Bytes 16)))
        (α := (publicHashSpec core₀).Range h) (implTH (thG g) (hmG g) h) := by
  cases h with
  | thash pk a xs =>
    show simulateQ (instImplF IV128 g) (out16 <$> chQ (thBlocks pk a xs)) = _
    rw [simulateQ_map, instImplF_chQ, map_pure]
    show _ = pure (thG g pk a xs)
    exact (congrArg pure (thG_shape g pk a xs)).symm
  | hmsg R pk root M =>
    show simulateQ (instImplF IV128 g) (do
      let s ← chQ (iblocksH R pk root M)
      let s' ← chQ (oblocksH R pk s)
      return dig30 s') = _
    simp only [simulateQ_bind, instImplF_chQ, pure_bind, simulateQ_pure]
    show _ = pure (hmG g R pk root M)
    exact (congrArg pure (hmG_shape g R pk root M)).symm

/-- The open port program does not depend on `Thash`, `H_msg` (definitional, checked by the
kernel). -/
theorem itsrOpenP_TH (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) (S : ForgerI)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (d : ProbComp (Bytes 16)) :
    itsrOpenP (prims := R₀ T H) (oR₀ oR) d (typedP codec₀ S.main) =
      itsrOpenP (prims := P₀) (oR₀ oR) d (typedP codec₀ S.main) := by
  krfl

/-- The steps of the two interpretations agree. -/
theorem outer_step (g : CF St Blk) (hI : QueryImpl (publicHashSpec core₀) Id)
    (hH : ∀ h, simulateQ (instImplF IV128 g) (hashCh h) =
      pure (f := OracleComp (unifSpec + ITSRTargetSpec X128 (Bytes 16)))
        (α := (publicHashSpec core₀).Range h) (hI h))
    (t : USpec.Domain) :
    simulateQ (interp hI) (portAns g t) = simulateQ (instImplF IV128 g) (outerImpl t) := by
  rcases t with n | (x | q) | u | h
  · simp only [portAns, outerImpl, simulateQ_spec_query]
    rfl
  · simp only [portAns, outerImpl, simulateQ_spec_query]
    rfl
  · simp only [portAns, outerImpl, simulateQ_pure, simulateQ_spec_query]
    rfl
  · simp only [portAns, outerImpl, simulateQ_spec_query, instImplF_liftM]
    rfl
  · simp only [portAns, outerImpl, simulateQ_spec_query, hH]
    rfl

/-- **Correctness at a table**, for any `Thash`, `H_msg` that the chains compute at `g`: the lazy
ITSR adversary over `R₀ T H` built from the forger with its compression queries answered by `g`
is the realising program instantiated at `g`. -/
theorem itsrA_main_eq_gen (g : CF St Blk) (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30)
    (hH : ∀ h, simulateQ (instImplF IV128 g) (hashCh h) =
      pure (f := OracleComp (unifSpec + ITSRTargetSpec X128 (Bytes 16)))
        (α := (publicHashSpec core₀).Range h) (implTH T H h))
    (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (d : ProbComp (Bytes 16)) :
    (Lazy.bItsrL (bytesToTypedS (prims := R₀ T H) (codec := codec₀) (optRand := oR₀ oR)
      (pkSeedDist := d) ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary).main =
      simulateQ (instImplF IV128 g) (itsrA S oR d) := by
  have hB : (bytesToTypedS (prims := R₀ T H) (codec := codec₀) (optRand := oR₀ oR)
      (pkSeedDist := d) ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary =
      (⟨fun pk => simulateQ (instImpl g) (typedP (prims := R₀ T H) codec₀ S.main pk)⟩ :
        Forger Link.vp (R₀ T H) (oR₀ oR) d) := by
    have e : (bytesToTypedS (prims := R₀ T H) (codec := codec₀) (optRand := oR₀ oR)
        (pkSeedDist := d) ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary.main =
        fun pk => simulateQ (instImpl g) (typedP (prims := R₀ T H) codec₀ S.main pk) :=
      funext fun pk => (typedP_inst (prims := R₀ T H) codec₀ (oR₀ oR) d g S.main pk).symm
    rw [← e]
  show lazyRun (PublicHash.impl (R₀ T H)) (itsrOpen _) = _
  rw [hB]
  have hf := itsrOpenP_fusion (prims := R₀ T H) (oR₀ oR) d g (typedP codec₀ S.main)
  refine (congrArg (lazyRun (PublicHash.impl (R₀ T H))) hf.symm).trans ?_
  rw [lazyRun, lazyRes_portAns, impl_R₀]
  refine (simulateQ_comm_of_step (interp (implTH T H)) (portAns g) (instImplF IV128 g) outerImpl
    (outer_step g (implTH T H) hH) _).trans ?_
  unfold itsrA
  rw [itsrOpenP_TH T H S oR d]
  krfl

/-- The forger at the table `g` over `R₀ (thG g) (hmG g)` (EUF wrapper). -/
noncomputable abbrev forgerE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (d : ProbComp (Bytes 16)) (g : CF St Blk) : Forger Link.vp (R₀ (thG g) (hmG g)) (oR₀ oR) d :=
  (bytesToTypedS (prims := R₀ (thG g) (hmG g)) (codec := codec₀) (optRand := oR₀ oR)
    (pkSeedDist := d) ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary

theorem itsrA_main_eq (g : CF St Blk) (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (d : ProbComp (Bytes 16)) :
    (Lazy.bItsrL (forgerE S oR d g)).main = simulateQ (instImplF IV128 g) (itsrA S oR d) :=
  itsrA_main_eq_gen g (thG g) (hmG g) (hashCh_inst g) S oR d

/-- The Reduction's ITSR adversary from the EUF wrapper of the forger at `g` is the one over
`R₀ (thG g) (hmG g)` (transport of `PRF`, `PRF_msg`, `Ideal.Transport.bItsrL_setPrf`). -/
theorem transportE (g : CF St Blk) (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (d : ProbComp (Bytes 16)) :
    Lazy.bItsrL (S.typedE (optRandU oR) d g) = Lazy.bItsrL (forgerE S oR d g) :=
  bItsrL_setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (oR₀ oR) (optRandU oR g)
    (fun _ => rfl) d (fun pk => simulateQ (instImpl g) (S.main pk))

/-- The same from the SUF wrapper. -/
theorem transportS (g : CF St Blk) (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (d : ProbComp (Bytes 16)) :
    Lazy.bItsrL (S.typedS (optRandU oR) d g) = Lazy.bItsrL (forgerE S oR d g) :=
  bItsrL_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (oR₀ oR) (optRandU oR g)
    (fun _ => rfl) d (fun pk => simulateQ (instImpl g) (S.main pk))

/-- **Equal advantages (EUF wrapper).** -/
theorem itsrA_adv_eqE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (d : ProbComp (Bytes 16)) (g : CF St Blk) :
    KeyedHash.ITSRAdvantage (Lazy.bItsrL (S.typedE (optRandU oR) d g)) =
      KeyedHash.ITSRAdvantage (instItsrF (itsrA S oR d) g) := by
  rw [transportE]
  show KeyedHash.ITSRAdvantage (⟨(Lazy.bItsrL (forgerE S oR d g)).main⟩ :
    KeyedHash.ITSRAdversary (itsrProblem Link.vp (primsG (liftC g)))) = _
  rw [itsrA_main_eq]
  rfl

/-- **Equal advantages (SUF wrapper).** -/
theorem itsrA_adv_eqS (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (d : ProbComp (Bytes 16)) (g : CF St Blk) :
    KeyedHash.ITSRAdvantage (Lazy.bItsrL (S.typedS (optRandU oR) d g)) =
      KeyedHash.ITSRAdvantage (instItsrF (itsrA S oR d) g) := by
  rw [transportS]
  show KeyedHash.ITSRAdvantage (⟨(Lazy.bItsrL (forgerE S oR d g)).main⟩ :
    KeyedHash.ITSRAdversary (itsrProblem Link.vp (primsG (liftC g)))) = _
  rw [itsrA_main_eq]
  rfl

end Ideal.Realize.Itsr

#print axioms Ideal.Realize.Itsr.hashCh_inst
#print axioms Ideal.Realize.Itsr.itsrA_main_eq_gen
#print axioms Ideal.Realize.Itsr.itsrA_adv_eqE
#print axioms Ideal.Realize.Itsr.itsrA_adv_eqS

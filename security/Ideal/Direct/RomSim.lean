import Ideal.Direct.Rooted
import Ideal.Direct.Entry
import Ideal.Sha.HmacShape
import Link.Security
import Ideal.Realize.WotsReal

/-!
# The Merkle–Damgård simulator of the ROM route (`status/DIRECT.md` §10)

The route of §9.3/§10: a compression-model forger `S` (`ForgerI`) is turned into an adversary
`simAdv S oR` against VCVio's three-oracle scheme
`romScheme core₀ (Equiv.refl _) (optRandR oR) pkSeedDist` (`Thash`, `H_msg`, `PRF_msg` random
oracles; `PRF` = `F` at secret-key addresses; `core₀` the repository's table-independent reference
core of SLH-DSA-SHA2-128s), so that VCVio's `strongUnforgeableAdvantage_romScheme_le_securityBound`
applies to it (the theorem `Link.security_128s` is, at `Link.prims.core`).

* `simStep pk`: the simulator's answer to one compression query, on its own table `T`
  (`(hS St Blk).QueryCache`).  A cached cell is answered from `T`.  A fresh cell is answered by a
  fresh 256-bit value `u`, except when it is the final cell of a `T`-rooted chain of a
  **relevant** query `t` (`relQ pk T q = some t`): then by `overlay t y u`, the oracle answer
  `y ← O(t)` in the first 16 (`Thash`, `PRF_msg`) or 30 (`H_msg`) bytes and `u` in the rest.
  Rootedness is dynamic: with respect to the current table (`Rooted.mdC`).
* Relevant (`IsRel`): `Thash(PK.seed, key, xs)` with `|xs| = arityOf key`; `H_msg(R, PK.seed,
  PK.root, M)` (outer final cell); `PRF_msg(k, o, M)` for every key `k` (outer HMAC final cell).
  `relQ` picks one relevant parse if there is one (`Classical.choice`); under no 256-bit
  coincidence there is at most one (`isThL_unique`, `isHmF_unique`), which only the (future) hop
  proof needs.
* `simImpl pk`: coins forwarded, compression queries by `simStep`, a signing query by one typed
  signing query whose answer is encoded (`encodeSignature`).
* `simAdv S oR`: run `S` on the encoded public key under `simImpl` from the empty table and parse
  its output signature (as `Coded.readForgery`, with the fallback `constSig 0^16`).
* **`simAdv_romQueryBound`**: if `S` makes at most `qf` compression and `qs` signing queries,
  `simAdv S oR` makes at most `qf` hash queries and `qs` signing queries (VCVio's
  `RomQueryBound`): one oracle query per fresh relevant final cell, none otherwise.
* **`simAdv_suf_le`**, **`simAdv_euf_le`**: VCVio's bound for the simulator,
  `≤ securityBound vp.params (256 ^ 16) 2 1 qf qs`; its hypotheses at `core₀` are
  `byteLaws₀`, `keyDiscipline₀` (from `keyDiscipline_sha2Primitives`), `|Y| ≤ |SK.prf|`, `e = refl`.

What this file does NOT prove: the hop, i.e. that `sufI` is at most the ROM advantage of
`simAdv S oR` plus the error `ε_hop` of §10.1.  That statement is `Rom.MDHop` in
`Direct/RomCompose.lean`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Concrete SLHDSA.Security SignatureAlg ENNReal

namespace Ideal.Direct.Rom

open Ideal.Realize

set_option linter.unusedSectionVars false

/-! ## The ROM interface at SLH-DSA-SHA2-128s -/

/-- The primitive context of the ROM scheme: the repository's table-independent reference core
`core₀` (`Realize/Chain.lean`: the carriers, `adrsToKey = sha2AdrsKey` and `yToBytes = id` of the
128s bundle; `romScheme` reads nothing else).  `Link.prims.core` would do for VCVio's theorem
(`Link.security_128s`), but the open programs of the realisers, which the hop has to be
compared with, are written over `core₀`, and comparing a `core₀`-indexed type with a
`Link.prims.core`-indexed one makes the kernel evaluate SHA-256 (`Chain.lean`'s note). -/
abbrev Cr : CorePrimitives Link.vp.params := core₀

/-- The typed signature. -/
abbrev SigC : Type := GeneralScheme.SignatureCore Link.vp Cr

/-- The ROM scheme's base interface: coins and the three oracles. -/
abbrev RS := unifSpec + hashSpec Cr

/-- The ROM adversary's interface: the base interface and the typed signing oracle. -/
abbrev BSpec := RS + (List Byte →ₒ SigC)

/-- `opt_rand` of the ROM scheme: the compression model's `optRandU oR`, which does not depend on
the table. -/
def optRandR (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore Cr) :
    ProbComp Cr.Y :=
  oR pk.pkSeed pk.pkRoot

/-- The ROM scheme of the route. -/
noncomputable abbrev romS (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :=
  romScheme (vp := Link.vp) Cr (Equiv.refl _) (optRandR oR) pkSeedDist

/-! ## Relevant queries -/

/-- The arity of the tweakable hash at an address key (`ADRSc`: layer, tree, **type** at byte 9,
then key pair, chain / tree height at bytes 14..17, hash / tree index): `F` (1) at WOTS hash,
FORS leaf and both PRF types, `H` (2) at tree nodes and inner FORS nodes, `T_len` (35) at
WOTS_PK, `T_k` (14) at FORS_ROOTS; `0` (never relevant) otherwise. -/
def arityOf (key : Bytes 22) : ℕ :=
  match key[9].toNat with
  | 0 => 1
  | 1 => 35
  | 2 => 2
  | 3 => if key[14] = 0 ∧ key[15] = 0 ∧ key[16] = 0 ∧ key[17] = 0 then 1 else 2
  | 4 => 14
  | 5 => 1
  | 6 => 1
  | _ => 0

/-- The cell `q` is the final cell, in the table `T`, of the relevant query `t` at the public key
`pk`.  `Thash`: `Rooted.IsThL` at the public seed with the right arity.  `H_msg`: the outer final
cell (`Rooted.IsHmF`) whose inner digest is the `T`-value of the inner chain of
`R ‖ PK.seed ‖ PK.root ‖ M`.  `PRF_msg`: the outer HMAC cell `(T(IV, okey k), oblock s)` with `s`
the `T`-value of the inner chain `ikey k`, `iblocks o M`. -/
def IsRel (pk : PublicKeyCore Cr) (T : (hS St Blk).QueryCache) (q : St × Blk) :
    (hashSpec Cr).Domain → Prop
  | .inl (.thash ps key xs) => ps = pk.pkSeed ∧ xs.length = arityOf key ∧ IsThL ps T q key xs
  | .inl (.hmsg R ps pr M) => ps = pk.pkSeed ∧ pr = pk.pkRoot ∧
      ∃ s, IsHmF T q R ps s ∧ mdC T IV128 (iblocksH R ps pr M) = some s
  | .inr ⟨k, o, M⟩ => ∃ s, mdC T IV128 [okey k] = some q.1 ∧ q.2 = oblock s ∧
      mdC T IV128 (ikey k :: iblocks o M) = some s

open Classical in
/-- The relevant query whose final cell `q` is, if any (a choice among the parses; there is at
most one under no 256-bit coincidence). -/
noncomputable def relQ (pk : PublicKeyCore Cr) (T : (hS St Blk).QueryCache) (q : St × Blk) :
    Option (hashSpec Cr).Domain :=
  if h : ∃ t, IsRel pk T q t then some (Classical.choose h) else none

theorem relQ_spec {pk : PublicKeyCore Cr} {T : (hS St Blk).QueryCache} {q : St × Blk}
    {t : (hashSpec Cr).Domain} (h : relQ pk T q = some t) : IsRel pk T q t := by
  unfold relQ at h
  split_ifs at h with hex
  · cases h; exact Classical.choose_spec hex

/-- The number of leading bytes of a cell value an oracle answer fixes: 30 for `H_msg`, 16 for
`Thash` and `PRF_msg`. -/
def ansLen : (hashSpec Cr).Domain → ℕ
  | .inl (.hmsg _ _ _ _) => 30
  | _ => 16

/-- The oracle answer as a list of bytes. -/
def ansBytes : (t : (hashSpec Cr).Domain) → (hashSpec Cr).Range t → List UInt8
  | .inl (.thash _ _ _), y => y.toList
  | .inl (.hmsg _ _ _ _), y => y.toList
  | .inr _, y => y.toList

/-- The cell value assembled from an oracle answer `y` and a fresh value `u`: `y` in the leading
bytes, `u` in the rest. -/
def overlay (t : (hashSpec Cr).Domain) (y : (hashSpec Cr).Range t) (u : St) : St :=
  Vector.ofFn fun i : Fin 32 => ((ansBytes t y).take (ansLen t) ++ u.toList.drop (ansLen t)).getD i 0

/-! ## The simulator -/

/-- A query to the hash oracles, as a query of the adversary's interface. -/
def hq (t : (hashSpec Cr).Domain) : OracleComp BSpec ((hashSpec Cr).Range t) :=
  (query (spec := BSpec) (.inl (.inr t)) : OracleComp BSpec _)

/-- The adversary's coins. -/
def coinI : QueryImpl unifSpec (OracleComp BSpec) := fun n =>
  (query (spec := BSpec) (.inl (.inl n)) : OracleComp BSpec _)

/-- A fresh 256-bit value, drawn by the adversary's coins. -/
noncomputable def freshSt : OracleComp BSpec St :=
  simulateQ coinI ($ᵗ St : ProbComp St)

/-- **The simulator's answer to one compression query.** -/
noncomputable def simStep (pk : PublicKeyCore Cr) (q : St × Blk) :
    StateT (hS St Blk).QueryCache (OracleComp BSpec) St := fun T =>
  match T q with
  | some v => pure (v, T)
  | none => do
    let u ← freshSt
    match relQ pk T q with
    | none => pure (u, T.cacheQuery q u)
    | some t => do
      let y ← hq t
      let v := overlay t y u
      pure (v, T.cacheQuery q v)

/-- **The simulator**: coins forwarded, compression queries by `simStep`, a signing query by one
typed signing query, its answer encoded. -/
noncomputable def simImpl (pk : PublicKeyCore Cr) :
    QueryImpl (FSpecP (List Byte)) (StateT (hS St Blk).QueryCache (OracleComp BSpec))
  | .inl n => liftM (query (spec := BSpec) (.inl (.inl n)) : OracleComp BSpec _)
  | .inr (.inl q) => simStep pk q
  | .inr (.inr m) => liftM (encodeSignature Link.vp Ideal.Realize.Wots.codec₀ <$>
      (query (spec := BSpec) (.inr m) : OracleComp BSpec SigC))

/-- The forger's output with its signature bytes parsed (fallback `constSig 0`, which loses
whenever the bytes do not parse). -/
def readOut (z : List Byte × List Byte) : List Byte × SigC :=
  (z.1, ((decodeSignature Link.vp Ideal.Realize.Wots.codec₀ z.2).toOption).getD
    (Reduction.constSig (vp := Link.vp) (prims := R₀ dT dH) (Vector.replicate 16 0)))

/-- **The ROM adversary built from a compression-model forger.** -/
noncomputable def simAdv (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : StrongUnforgeableAdversary (romS oR pkSeedDist) where
  main pk := readOut <$>
    (simulateQ (simImpl pk) (S.main (encodePublicKey Ideal.Realize.Wots.codec₀ pk))).run' ∅

/-- The same program as an EUF adversary. -/
noncomputable def simAdvE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : UnforgeableAdversary (romS oR pkSeedDist) :=
  (simAdv S oR pkSeedDist).toUnforgeableAdversary

/-! ## Query budget -/

section Budget

variable (pk : PublicKeyCore Cr)

/-- A hash query of the adversary. -/
abbrev isH : BSpec.Domain → Prop := IsHashQuery (hs := hashSpec Cr) (M := List Byte) (S := SigC)

/-- A signing query of the adversary. -/
abbrev isSg : BSpec.Domain → Prop := IsSignQuery (hs := hashSpec Cr) (M := List Byte) (S := SigC)

instance : DecidablePred isH := inferInstanceAs (DecidablePred (IsHashQuery (hs := hashSpec Cr)
  (M := List Byte) (S := SigC)))
instance : DecidablePred isSg := inferInstanceAs (DecidablePred (IsSignQuery (hs := hashSpec Cr)
  (M := List Byte) (S := SigC)))

theorem qb_none {α : Type} {ι : Type} {spec : OracleSpec ι} (oa : OracleComp spec α) :
    IsQueryBoundP oa (fun _ => False) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl id, fun u => by simp only [ite_false]; exact ih u⟩

/-- The coins make neither hash nor signing queries. -/
theorem freshSt_qb (P : BSpec.Domain → Prop) [DecidablePred P]
    (hP : ∀ n, ¬ P (.inl (.inl n))) : IsQueryBoundP freshSt P 0 :=
  qb_simulateQ_zero (p := fun _ => False) (fun n _ =>
      (isQueryBoundP_query_iff (spec := BSpec) (p := P) (.inl (.inl n)) 0).2 fun h => absurd h (hP n))
    (qb_none _)

theorem hq_qb_hash (t : (hashSpec Cr).Domain) : IsQueryBoundP (hq t) isH 1 := by
  simp [hq]

theorem hq_qb_sign (t : (hashSpec Cr).Domain) : IsQueryBoundP (hq t) isSg 0 := by
  simp [hq, isSg, IsSignQuery]

/-- One compression step makes at most one hash query and no signing query. -/
theorem simStep_qb (q : St × Blk) (T : (hS St Blk).QueryCache) (P : BSpec.Domain → Prop)
    [DecidablePred P] (hP : ∀ n, ¬ P (.inl (.inl n))) (c : ℕ)
    (hc : ∀ t, IsQueryBoundP (hq t) P c) :
    IsQueryBoundP ((simStep pk q).run T) P c := by
  unfold simStep
  change IsQueryBoundP (match T q with
    | some v => pure (v, T)
    | none => _) P c
  rcases T q with _ | v
  · simp only
    have h := isQueryBoundP_bind (n := 0) (m := c) (freshSt_qb P hP) (ob := fun u =>
      match relQ pk T q with
      | none => pure (u, T.cacheQuery q u)
      | some t => do
        let y ← hq t
        let v := overlay t y u
        pure (v, T.cacheQuery q v)) fun u _ => by
      rcases relQ pk T q with _ | t
      · simp
      · show IsQueryBoundP (hq t >>= fun y => pure (overlay t y u, T.cacheQuery q (overlay t y u))) P c
        simpa using isQueryBoundP_bind (n := c) (m := 0) (hc t)
          (ob := fun y => (pure (overlay t y u, T.cacheQuery q (overlay t y u)) :
            OracleComp BSpec (St × (hS St Blk).QueryCache))) fun _ _ => isQueryBoundP_pure _ _ _
    simpa using h
  · simp

/-- One step of the simulator: a compression query costs at most what one oracle query costs, a
signing query what one signing query costs, coins nothing. -/
theorem simImpl_qb (t : (FSpecP (List Byte)).Domain) (T : (hS St Blk).QueryCache)
    (P : BSpec.Domain → Prop) [DecidablePred P] (hP : ∀ n, ¬ P (.inl (.inl n))) (c c' : ℕ)
    (hc : ∀ t, IsQueryBoundP (hq t) P c)
    (hsig : ∀ m, IsQueryBoundP (query (spec := BSpec) (.inr m) : OracleComp BSpec SigC) P c') :
    IsQueryBoundP ((simImpl pk t).run T) P
      (if isPortQ t = true then c else if isSignQ t = true then c' else 0) := by
  rcases t with n | q | m
  · simp only [isPortQ, isSignQ, Bool.false_eq_true, ite_false]
    show IsQueryBoundP ((liftM (query (spec := BSpec) (.inl (.inl n)) : OracleComp BSpec _) :
      StateT (hS St Blk).QueryCache (OracleComp BSpec) _).run T) P 0
    simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_lift]
    exact isQueryBoundP_bind (n := 0) (m := 0)
      ((isQueryBoundP_query_iff (spec := BSpec) (p := P) (.inl (.inl n)) 0).2 fun h => absurd h (hP n))
      fun _ _ => isQueryBoundP_pure _ _ _
  · simp only [isPortQ, ite_true]
    exact simStep_qb pk q T P hP c hc
  · simp only [isPortQ, isSignQ, Bool.false_eq_true, ite_false, ite_true]
    show IsQueryBoundP ((liftM (encodeSignature Link.vp Ideal.Realize.Wots.codec₀ <$>
      (query (spec := BSpec) (.inr m) : OracleComp BSpec SigC)) :
      StateT (hS St Blk).QueryCache (OracleComp BSpec) _).run T) P c'
    simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_lift]
    simpa using isQueryBoundP_bind (n := c') (m := 0)
      ((isQueryBoundP_map_iff _ (encodeSignature Link.vp Ideal.Realize.Wots.codec₀) _).2 (hsig m))
      (ob := fun a => (pure (a, T) : OracleComp BSpec (List Byte × (hS St Blk).QueryCache)))
      fun _ _ => isQueryBoundP_pure _ _ _

/-- **The simulator's budget (VCVio's `RomQueryBound`)**: at most `qf` hash queries (one per
compression query of `S`) and `qs` signing queries. -/
theorem simAdv_romQueryBound (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) {qf qs : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) :
    (simAdv S oR pkSeedDist).RomQueryBound qf qs := by
  intro pk
  have hrun : ∀ (P : BSpec.Domain → Prop) [DecidablePred P] (p : (FSpecP (List Byte)).Domain → Bool)
      (n : ℕ), IsQueryBoundP (S.main (encodePublicKey Ideal.Realize.Wots.codec₀ pk)) (fun i => p i = true) n →
      (∀ t, p t = true → ∀ T, IsQueryBoundP ((simImpl pk t).run T) P 1) →
      (∀ t, p t = false → ∀ T, IsQueryBoundP ((simImpl pk t).run T) P 0) →
      IsQueryBoundP ((simAdv S oR pkSeedDist).main pk) P n := by
    intro P _ p n h h1 h0
    have := IsQueryBoundP.simulateQ_run_of_step (impl := simImpl pk) (q := P) h
      (fun t ht T => h1 t ht T) (fun t ht T => h0 t (by simpa using ht) T) ∅
    show IsQueryBoundP (readOut <$> (Prod.fst <$> _)) P n
    exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_map_iff _ _ _).2 this)
  have hH : ∀ m, IsQueryBoundP (query (spec := BSpec) (.inr m) : OracleComp BSpec SigC) isH 0 :=
    fun m => (isQueryBoundP_query_iff (spec := BSpec) (p := isH) (.inr m) 0).2 fun h => h.elim
  have hS' : ∀ m, IsQueryBoundP (query (spec := BSpec) (.inr m) : OracleComp BSpec SigC) isSg 1 :=
    fun m => (isQueryBoundP_query_iff (spec := BSpec) (p := isSg) (.inr m) 1).2 fun _ => Nat.one_pos
  have hstepH : ∀ t T, IsQueryBoundP ((simImpl pk t).run T) isH (if isPortQ t = true then 1 else 0) := by
    intro t T
    have := simImpl_qb pk t T isH (fun n h => h) 1 0 hq_qb_hash hH
    convert this using 1
    rcases t with n | q | m <;> rfl
  have hstepS : ∀ t T, IsQueryBoundP ((simImpl pk t).run T) isSg (if isSignQ t = true then 1 else 0) := by
    intro t T
    have := simImpl_qb pk t T isSg (fun n h => h) 0 1 hq_qb_sign hS'
    convert this using 1
    rcases t with n | q | m <;> rfl
  refine ⟨hrun isH (fun i => isPortQ i) qf (hqf _) (fun t ht T => ?_) (fun t ht T => ?_),
    hrun isSg (fun i => isSignQ i) qs (hqs _) (fun t ht T => ?_) (fun t ht T => ?_)⟩
  · simpa only [ht, ite_true] using hstepH t T
  · simpa only [ht, Bool.false_eq_true, ite_false] using hstepH t T
  · simpa only [ht, ite_true] using hstepS t T
  · simpa only [ht, Bool.false_eq_true, ite_false] using hstepS t T

end Budget

/-! ## VCVio's bound for the simulator -/

/-- The hypotheses of VCVio's theorem at `core₀` (as for the FIPS SHA-2 bundle: they read only
`yToBytes`, `adrsToKey` and the parameter set). -/
theorem byteLaws₀ : Cr.ByteLaws := ⟨fun _ _ h => h⟩

theorem keyDiscipline₀ : Cr.KeyDiscipline Link.vp :=
  ⟨(Concrete.keyDiscipline_sha2Primitives Link.vp (fipsApprovedAddressBounds Link.S128)).keyInjective,
    (Concrete.keyDiscipline_sha2Primitives Link.vp (fipsApprovedAddressBounds Link.S128)).canonicalAddressBounds,
    (Concrete.keyDiscipline_sha2Primitives Link.vp (fipsApprovedAddressBounds Link.S128)).keySeparated⟩

theorem natCard₀ : Nat.card Cr.Y = 256 ^ 16 :=
  Concrete.natCard_sha2Primitives_y Link.vp.params

/-- **VCVio's SUF-CMA bound for the simulator** (`strongUnforgeableAdvantage_romScheme_le_securityBound`
at `core₀`; the same theorem as `Link.security_128s`, at the reference core). -/
theorem simAdv_suf_le (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) {qf qs : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr)) (simAdv S oR pkSeedDist) ≤
      securityBound Link.vp.params (256 ^ 16) 2 1 qf qs := by
  rw [← natCard₀]
  exact strongUnforgeableAdvantage_romScheme_le_securityBound byteLaws₀ keyDiscipline₀ le_rfl
    (Equiv.refl _) (optRandR oR) pkSeedDist (simAdv S oR pkSeedDist)
    (simAdv_romQueryBound S oR pkSeedDist hqf hqs)

/-- **VCVio's EUF-CMA bound for the simulator.** -/
theorem simAdv_euf_le (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) {qf qs : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr)) (simAdvE S oR pkSeedDist) ≤
      securityBound Link.vp.params (256 ^ 16) 2 1 qf qs := by
  rw [← natCard₀]
  exact unforgeableAdvantage_romScheme_le Cr (securityTarget_two_one byteLaws₀ keyDiscipline₀ le_rfl
    (Equiv.refl _) (optRandR oR)) pkSeedDist (simAdvE S oR pkSeedDist)
    (simAdv_romQueryBound S oR pkSeedDist hqf hqs)

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.simAdv_romQueryBound
#print axioms Ideal.Direct.Rom.simAdv_suf_le
#print axioms Ideal.Direct.Rom.simAdv_euf_le

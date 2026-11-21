import Ideal.Realize.ItsrReal

/-!
# Queries of the ITSR realiser `itsrA`

From the counts of the open port program (`Ideal/Realize/ItsrCount.lean`), through the lazy
cache (`lazyRes_predR`: queries that are not secret reads pass one for one) and through
`outerImpl` (one raw query per port query, one target query per target query, one chain query
per `Thash` query, two per `H_msg` query):

* `itsrA_raw`: at most `qf` raw compression queries (hence `itsrA_rawP`: at most `qf` with block
  `cB`);
* `itsrA_tgt`: at most `qs` target queries;
* `itsrA_chain`: at most `keygenHashes + qs·signHashes + qs` chain queries;
* **`itsrA_chainP`: at most `2·qs` chain queries whose second block is `cB`** — only the two
  chains of each `H_msg` evaluation can have second block `cB`; every `Thash` chain has a second
  block different from `cB` (`thBlocks_secondP`, from `Ideal/Realize/ItsrWalk.lean`);
* `itsrA_chainLen`: every chain query has at most `itsrLc ℓ` blocks;
* `itsrA_tgtOK`, `itsrA_out`: target messages and the returned message have at most `ℓ` bytes.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security KeyedHash

namespace Ideal.Realize.Itsr

open Reduction Reduction.Lazy Ideal.Realize Ideal.Itsr

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Predicates that ignore secret reads, through the lazy cache -/

section PredR

variable {ι κ D V : Type} {G : OracleSpec ι} {hspec : OracleSpec κ} {α : Type}

/-- A query predicate given by a predicate on game queries and one on hash queries (uniform
bits and secret reads never satisfy it). -/
def predR (pg : ι → Bool) (ph : κ → Bool) : ℕ ⊕ (ι ⊕ (D ⊕ κ)) → Bool
  | .inl _ => false
  | .inr (.inl x) => pg x
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr h)) => ph h

/-- **Game and hash queries pass through the lazy cache one for one.** -/
theorem lazyRes_predR [DecidableEq D] (pg : ι → Bool) (ph : κ → Bool)
    (P : OracleComp (RSpec G D V hspec) α) (n : ℕ)
    (h : IsQueryBoundP P (fun t => predR (D := D) pg ph t = true) n) :
    IsQueryBoundP (lazyRes P) (fun t => predR (D := Unit) pg ph t = true) n := by
  unfold lazyRes
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht s => ?_) (fun t ht s => ?_) []
  · rcases t with n | x | d | q
    · simp [predR] at ht
    · simp [lazyImplR, predR]
    · simp [predR] at ht
    · simp [lazyImplR, predR]
  · rcases t with n | x | d | q
    · simp [lazyImplR, predR]
    · simp only [predR] at ht
      simp [lazyImplR, predR, ht]
    · rcases hc : s.lookup d with _ | v
      · rw [lazyImplR_sec_run_miss d s hc]
        simp [predR]
      · rw [lazyImplR_sec_run_hit d s v hc]
        simp
    · simp only [predR] at ht
      simp [lazyImplR, predR, ht]

/-- No such query in `lazyRes P`, as `AllQueriesSatisfy`. -/
theorem lazyRes_predR_all [DecidableEq D] (pg : ι → Bool) (ph : κ → Bool)
    (P : OracleComp (RSpec G D V hspec) α)
    (h : IsQueryBoundP P (fun t => predR (D := D) pg ph t = true) 0) :
    AllQueriesSatisfy (lazyRes P) (fun t => ¬ predR (D := Unit) pg ph t = true) := by
  rw [← isQueryBoundP_zero_iff]
  simpa using lazyRes_predR pg ph P 0 h

end PredR

/-! ## The predicates used -/

/-- Game queries of the port program: target (`inl`) or port (`inr`). -/
abbrev GI := ItsrIn P₀ ⊕ (St × Blk)

/-- Byte 9 of an address key. -/
def key9 (key : Bytes 22) : Byte := key[9]

/-- An `H_msg` query. -/
def isHm : PublicHashQuery core₀.PkSeed core₀.AdrsKey core₀.Y → Bool
  | .hmsg _ _ _ _ => true
  | _ => false

/-- A target query on a message of more than `ℓ` bytes. -/
def longTgt (ℓ : ℕ) : GI → Bool
  | .inl x => decide (ℓ < x.2.2.length)
  | .inr _ => false

/-- A `Thash` query on other than one or two values whose key has byte 9 zero. -/
def badKeyH : PublicHashQuery core₀.PkSeed core₀.AdrsKey core₀.Y → Bool
  | .thash _ key xs => !(decide (xs.length = 1) || decide (xs.length = 2)) && !(decide (key9 key ≠ 0))
  | _ => false

/-- A `Thash` query on more than `B` values or an `H_msg` query on more than `ℓ` bytes. -/
def badH (B ℓ : ℕ) : PublicHashQuery core₀.PkSeed core₀.AdrsKey core₀.Y → Bool
  | .thash _ _ xs => decide (B < xs.length)
  | .hmsg _ _ _ M => decide (ℓ < M.length)

/-- `Thash` and `H_msg` queries of the resource-explicit program. -/
def pHash : USpec.Domain → Bool := predR (D := Unit) (fun _ : GI => false) (fun _ => true)
/-- `H_msg` queries of the resource-explicit program. -/
def pHm : USpec.Domain → Bool := predR (D := Unit) (fun _ : GI => false) isHm
/-- Forbidden `Thash` queries of the resource-explicit program. -/
def pBadKey : USpec.Domain → Bool := predR (D := Unit) (fun _ : GI => false) badKeyH

/-! ## The steps of `outerImpl` -/

theorem qA_np {q : ASpec.Domain → Prop} [DecidablePred q] {t : ASpec.Domain} (ht : ¬ q t) :
    IsQueryBoundP (liftM (ASpec.query t) : OracleComp ASpec _) q 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h ht

theorem qA_one (q : ASpec.Domain → Prop) [DecidablePred q] (t : ASpec.Domain) :
    IsQueryBoundP (liftM (ASpec.query t) : OracleComp ASpec _) q 1 :=
  (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos

theorem liftA_np {q : ASpec.Domain → Prop} [DecidablePred q] (hq : ∀ n, ¬ q (.inl n)) {β : Type}
    (ob : ProbComp β) : IsQueryBoundP (liftM ob : OracleComp ASpec β) q 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
      rcases t with n | t
      · exact absurd ht (hq n)
      · rfl)
    (isQueryBoundP_liftM_isRight (hs := aS St Blk + ITSRTargetSpec X128 (Bytes 16)) ob)

/-- A hash query makes no query outside the chain queries. -/
theorem hashCh_np {q : ASpec.Domain → Prop} [DecidablePred q]
    (hq : ∀ bs, ¬ q (.inr (.inl (.inr bs)))) (h : (publicHashSpec core₀).Domain) :
    IsQueryBoundP (hashCh h) q 0 := by
  cases h with
  | thash pk a xs =>
    show IsQueryBoundP (out16 <$> chQ (thBlocks pk a xs)) _ _
    rw [isQueryBoundP_map_iff]
    exact qA_np (hq _)
  | hmsg R pk root M =>
    show IsQueryBoundP (do
      let s ← chQ (iblocksH R pk root M)
      let s' ← chQ (oblocksH R pk s)
      return dig30 s') _ _
    exact isQueryBoundP_bind_zero _ _ (qA_np (hq _)) fun s =>
      isQueryBoundP_bind_zero _ _ (qA_np (hq _)) fun s' => isQueryBoundP_pure _ _ _

/-- A `Thash` query: one chain query. -/
theorem hashCh_thash (q : ASpec.Domain → Prop) [DecidablePred q] (pk : Bytes 16) (a : Bytes 22)
    (xs : List (Bytes 16)) (c : ℕ)
    (h : IsQueryBoundP (chQ (thBlocks pk a xs)) q c) :
    IsQueryBoundP (hashCh (.thash pk a xs)) q c := by
  show IsQueryBoundP (out16 <$> chQ (thBlocks pk a xs)) _ _
  rw [isQueryBoundP_map_iff]
  exact h

/-- An `H_msg` query: two chain queries. -/
theorem hashCh_hmsg (q : ASpec.Domain → Prop) [DecidablePred q] (R pk root : Bytes 16)
    (M : List Byte) : IsQueryBoundP (hashCh (.hmsg R pk root M)) q 2 := by
  show IsQueryBoundP (do
    let s ← chQ (iblocksH R pk root M)
    let s' ← chQ (oblocksH R pk s)
    return dig30 s') _ _
  exact (isQueryBoundP_bind (qA_one q _) fun s _ =>
    isQueryBoundP_bind (m := 0) (qA_one q _) fun s' _ => isQueryBoundP_pure _ _ _).mono
      (by omega)

/-- Every `Thash` chain of a query that is not `badKeyH` has a second block other than `cB`. -/
theorem thBlocks_secondP (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16))
    (h : badKeyH (.thash pk a xs) = false) : secondP P128 (thBlocks pk a xs) = false := by
  simp only [thBlocks, secondP, P128, decide_eq_false_iff_not]
  by_cases h1 : xs.length = 1
  · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp h1
    exact tblocks_one_ne_cB' a x
  · by_cases h2 : xs.length = 2
    · obtain ⟨l, r, rfl⟩ := List.length_eq_two.mp h2
      exact tblocks_two_ne_cB a l r
    · simp [badKeyH, key9] at h
      exact tblocks_ne_cB_of_key9 a xs (of_decide_eq_true (h h1 h2))

/-- The number of blocks of the chain of `Thash(pk, a, xs)`. -/
theorem thBlocks_length (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    (thBlocks pk a xs).length = thashCost xs.length := by
  simp only [thBlocks, List.length_cons, tblocks_snd_length, thashCost]
  omega

/-! ## The counts of the realiser -/

section Counts

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (d : ProbComp (Bytes 16))
  {qf qs ℓ : ℕ}

/-- The open program inside the realiser. -/
noncomputable abbrev openA : OracleComp (OSpec P₀ (gI P₀)) (Bytes 16 × X128) :=
  itsrOpenP (prims := P₀) (oR₀ oR) d (typedP codec₀ S.main)

theorem itsrA_eq : itsrA S oR d = simulateQ outerImpl (lazyRes (openA S oR d)) := rfl

/-! ### From the counts of the open program to `predR` form -/

theorem conv_port (t : IdxI P₀) (ht : predR (D := SecIdx) (fun x : GI => x.isRight)
    (fun _ => false) t = true) : isPortI t = true := by
  rcases t with n | (x | q) | d | h <;> simp_all [predR, isPortI]

theorem conv_tgt (t : IdxI P₀) (ht : predR (D := SecIdx) (fun x : GI => x.isLeft)
    (fun _ => false) t = true) : isTgtI t = true := by
  rcases t with n | (x | q) | d | h <;> simp_all [predR, isTgtI]

theorem conv_hash (t : IdxI P₀) (ht : predR (D := SecIdx) (fun _ : GI => false)
    (fun _ => true) t = true) : Lazy.kind t = .hash := by
  rcases t with n | (x | q) | d | h <;> simp_all [predR, Lazy.kind]

theorem conv_hm (t : IdxI P₀) (ht : predR (D := SecIdx) (fun _ : GI => false) isHm t = true) :
    isHmsgIdx t = true := by
  rcases t with n | (x | q) | d | h
  · simp [predR] at ht
  · simp [predR] at ht
  · simp [predR] at ht
  · simp [predR] at ht
  · cases h
    · simp [predR, isHm] at ht
    · rfl

theorem conv_badKey (t : IdxI P₀) (ht : predR (D := SecIdx) (fun _ : GI => false) badKeyH t = true) :
    isBadKeyI (prims := P₀) (fun key : Bytes 22 => decide (key9 key ≠ 0)) t = true := by
  rcases t with n | (x | q) | d | h
  · simp [predR] at ht
  · simp [predR] at ht
  · simp [predR] at ht
  · simp [predR] at ht
  · cases h
    · simp only [predR, badKeyH] at ht
      simp only [isBadKeyI]
      exact ht
    · simp [predR, badKeyH] at ht

theorem conv_bad (B ℓ : ℕ) (t : IdxI P₀)
    (ht : predR (D := SecIdx) (fun _ : GI => false) (badH B ℓ) t = true) :
    isBadIdx B ℓ t = true := by
  rcases t with n | (x | q) | d | h
  · simp [predR] at ht
  · simp [predR] at ht
  · simp [predR] at ht
  · simp [predR] at ht
  · cases h
    · simp only [predR, badH] at ht
      exact ht
    · simp only [predR, badH] at ht
      exact ht

theorem conv_longTgt (ℓ : ℕ) (t : IdxI P₀)
    (ht : predR (D := SecIdx) (longTgt ℓ) (fun _ => false) t = true) :
    isLongTgtI ℓ t = true := by
  rcases t with n | (x | q) | d | h <;> simp_all [predR, longTgt, isLongTgtI]

/-- The typed counts from the byte-level ones. -/
theorem typed_port
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) :
    ∀ pk, IsQueryBoundP (typedP (prims := P₀) codec₀ S.main pk)
      (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qf :=
  fun pk => typedP_bound (prims := P₀) codec₀ (fun i => isPortQ (S := List Byte) i)
    (fun i => isPortQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk qf (hqf _)

theorem typed_sign
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) :
    ∀ pk, IsQueryBoundP (typedP (prims := P₀) codec₀ S.main pk)
      (fun i => isSignQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i = true) qs :=
  fun pk => typedP_bound (prims := P₀) codec₀ (fun i => isSignQ (S := List Byte) i)
    (fun i => isSignQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) i)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk qs (hqs _)

theorem typed_long
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) :
    ∀ pk, IsQueryBoundP (typedP (prims := P₀) codec₀ S.main pk)
      (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) ℓ i = true) 0 :=
  fun pk => typedP_bound (prims := P₀) codec₀ (fun i => isLongQ (S := List Byte) ℓ i)
    (fun i => isLongQ (S := GeneralScheme.SignatureCore Link.vp P₀.core) ℓ i)
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) S.main pk 0 (hlong _)

theorem typed_out (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    ∀ pk, ∀ z ∈ support (typedP (prims := P₀) codec₀ S.main pk), z.1.length ≤ ℓ := by
  intro pk z hz
  obtain ⟨out, hout', he⟩ := typedP_out (prims := P₀) codec₀ S.main pk z hz
  rw [he]
  exact hout _ out hout'

/-- **Raw compression queries: at most `qf`** (the forger's own). -/
theorem itsrA_raw
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) :
    IsQueryBoundP (itsrA S oR d)
      (fun i => rawB (X := X128) (fun _ : St × Blk => true) i = true) qf := by
  have h0 := itsrOpenP_port (oR₀ oR) d (typedP (prims := P₀) codec₀ S.main) (typed_port S hqf)
  have h1 : IsQueryBoundP (openA S oR d)
      (fun t => predR (D := SecIdx) (fun x : GI => x.isRight) (fun _ => false) t = true) qf :=
    IsQueryBoundP.of_imp conv_port h0
  have h2 := lazyRes_predR _ _ _ _ h1
  rw [itsrA_eq]
  refine IsQueryBoundP.simulateQ_of_step h2 (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | (x | q) | u | h
    · simp [predR] at ht
    · simp [predR] at ht
    · exact qA_one _ _
    · simp [predR] at ht
    · simp [predR] at ht
  · rcases t with n | (x | q) | u | h
    · exact qA_np (by simp [rawB])
    · exact qA_np (by simp [rawB])
    · simp [predR] at ht
    · exact liftA_np (fun n => by simp [rawB]) _
    · exact hashCh_np (fun bs => by simp [rawB]) h

/-- Raw compression queries with block `cB`: at most `qf`. -/
theorem itsrA_rawP
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) :
    IsQueryBoundP (itsrA S oR d)
      (fun i => rawB (X := X128) (fun t : St × Blk => P128 t.2) i = true) qf :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with n | ((q | bs) | x) <;> simp_all [rawB]) (itsrA_raw S oR d hqf)

/-- **Target queries: at most `qs`.** -/
theorem itsrA_tgt
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) :
    IsQueryBoundP (itsrA S oR d)
      (fun i => isTgtF (St := St) (Blk := Blk) (X := X128) i = true) qs := by
  have h0 := itsrOpenP_tgt (oR₀ oR) d (typedP (prims := P₀) codec₀ S.main) (typed_sign S hqs)
  have h1 : IsQueryBoundP (openA S oR d)
      (fun t => predR (D := SecIdx) (fun x : GI => x.isLeft) (fun _ => false) t = true) qs :=
    IsQueryBoundP.of_imp conv_tgt h0
  have h2 := lazyRes_predR _ _ _ _ h1
  rw [itsrA_eq]
  refine IsQueryBoundP.simulateQ_of_step h2 (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | (x | q) | u | h
    · simp [predR] at ht
    · exact qA_one _ _
    · simp [predR] at ht
    · simp [predR] at ht
    · simp [predR] at ht
  · rcases t with n | (x | q) | u | h
    · exact qA_np (by simp [isTgtF])
    · simp [predR] at ht
    · exact qA_np (by simp [isTgtF])
    · exact liftA_np (fun n => by simp [isTgtF]) _
    · exact hashCh_np (fun bs => by simp [isTgtF]) h

/-- **Chain queries: at most `keygenHashes + qs·signHashes + qs`** (one per `Thash` query, two
per `H_msg` query; at most `qs` `H_msg` queries). -/
theorem itsrA_chain
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) :
    IsQueryBoundP (itsrA S oR d)
      (fun i => chB (St := St) (X := X128) (fun _ : List Blk => true) i = true)
      (Lazy.keygenHashes Link.vp + qs * Lazy.signHashes Link.vp + qs) := by
  have hh := itsrOpenP_hashes (oR₀ oR) d (typedP (prims := P₀) codec₀ S.main) (typed_sign S hqs)
  have hm := itsrOpenP_hmsg (oR₀ oR) d (typedP (prims := P₀) codec₀ S.main) (typed_sign S hqs)
  have h1 : IsQueryBoundP (openA S oR d)
      (fun t => predR (D := SecIdx) (fun _ : GI => false) (fun _ => true) t = true)
      (Lazy.keygenHashes Link.vp + qs * Lazy.signHashes Link.vp) :=
    IsQueryBoundP.of_imp conv_hash hh
  have h2 : IsQueryBoundP (openA S oR d)
      (fun t => predR (D := SecIdx) (fun _ : GI => false) isHm t = true) qs :=
    IsQueryBoundP.of_imp conv_hm hm
  have := qb_simulateQ_classes (p₀ := fun _ => False)
    (p₁ := fun t => pHash t = true) (p₂ := fun t => pHm t = true)
    (p₃ := fun _ => False)
    (q := fun i => chB (St := St) (X := X128) (fun _ : List Blk => true) i = true)
    (impl := outerImpl) 1 1 0 (fun t _ => ?_) (isQueryBoundP_false _ _)
    (lazyRes_predR _ _ _ _ h1) (lazyRes_predR _ _ _ _ h2) (isQueryBoundP_false _ 0)
  · rw [itsrA_eq]
    exact this.mono (by omega)
  · rcases t with n | (x | q) | u | (⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩)
    · exact (qA_np (by simp [chB])).mono (Nat.zero_le _)
    · exact (qA_np (by simp [chB])).mono (Nat.zero_le _)
    · exact (qA_np (by simp [chB])).mono (Nat.zero_le _)
    · exact (liftA_np (fun n => by simp [chB]) _).mono (Nat.zero_le _)
    · exact (hashCh_thash _ pk a xs 1 (qA_one _ _)).mono (by simp [pHash, pHm, predR, isHm])
    · exact (hashCh_hmsg _ R pk root M).mono (by simp [pHash, pHm, predR, isHm])

/-- **Chain queries whose second block is `cB`: at most `2·qs`** (only the two chains of each
`H_msg` evaluation; no `Thash` chain has second block `cB`). -/
theorem itsrA_chainP
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) :
    IsQueryBoundP (itsrA S oR d)
      (fun i => chB (St := St) (X := X128) (secondP P128) i = true) (2 * qs) := by
  have hm := itsrOpenP_hmsg (oR₀ oR) d (typedP (prims := P₀) codec₀ S.main) (typed_sign S hqs)
  have hk := itsrOpenP_badKey (oR₀ oR) d (typedP (prims := P₀) codec₀ S.main)
    (fun key : Bytes 22 => decide (key9 key ≠ 0)) (fun b => decide_eq_true (key9_wotsPk b))
    (fun b => decide_eq_true (key9_forsPk b))
  have h2 : IsQueryBoundP (openA S oR d)
      (fun t => predR (D := SecIdx) (fun _ : GI => false) isHm t = true) qs :=
    IsQueryBoundP.of_imp conv_hm hm
  have h0 : IsQueryBoundP (openA S oR d)
      (fun t => predR (D := SecIdx) (fun _ : GI => false) badKeyH t = true) 0 :=
    IsQueryBoundP.of_imp conv_badKey hk
  have := qb_simulateQ_classes
    (p₀ := fun t => pBadKey t = true) (p₁ := fun t => pHm t = true)
    (p₂ := fun _ => False) (p₃ := fun _ => False)
    (q := fun i => chB (St := St) (X := X128) (secondP P128) i = true)
    (impl := outerImpl) 2 0 0 (fun t ht => ?_) (lazyRes_predR _ _ _ _ h0)
    (lazyRes_predR _ _ _ _ h2) (isQueryBoundP_false _ 0) (isQueryBoundP_false _ 0)
  · rw [itsrA_eq]
    exact this.mono (by omega)
  · rcases t with n | (x | q) | u | (⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩)
    · exact (qA_np (by simp [chB])).mono (Nat.zero_le _)
    · exact (qA_np (by simp [chB])).mono (Nat.zero_le _)
    · exact (qA_np (by simp [chB])).mono (Nat.zero_le _)
    · exact (liftA_np (fun n => by simp [chB]) _).mono (Nat.zero_le _)
    · have hb : badKeyH (.thash pk a xs) = false := by
        have h' : ¬ badKeyH (.thash pk a xs) = true := ht
        simpa using h'
      exact (hashCh_thash _ pk a xs 0 (qA_np (by simp [chB, thBlocks_secondP pk a xs hb]))).mono
        (Nat.zero_le _)
    · exact (hashCh_hmsg _ R pk root M).mono (by simp [pHash, pHm, predR, isHm])

/-- The maximal number of values of a tweakable-hash call: `max 2 (max len k)`. -/
def thMax : ℕ := max 2 (max Link.vp.params.len Link.vp.params.k)

theorem okLen_le (xs : List (Bytes 16)) (h : OkLen Link.vp xs) : xs.length ≤ thMax := by
  unfold OkLen at h
  unfold thMax
  omega

/-- **The block bound of the chain queries**: the longer of the longest `Thash` chain and the
inner `H_msg` chain of an `ℓ`-byte message. -/
def itsrLc (ℓ : ℕ) : ℕ := max (thashCost thMax) ((ℓ + 56) / 64 + 1)

/-- **Every chain query has at most `itsrLc ℓ` blocks.** -/
theorem itsrA_chainLen
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) :
    AllQueriesSatisfy (itsrA S oR d)
      (chOK (St := St) (X := X128) fun bs : List Blk => bs.length ≤ itsrLc ℓ) := by
  have hb := itsrOpenP_bad (oR₀ oR) d (typedP (prims := P₀) codec₀ S.main) thMax okLen_le
    (typed_long S hlong)
  have h0 : IsQueryBoundP (openA S oR d)
      (fun t => predR (D := SecIdx) (fun _ : GI => false) (badH thMax ℓ) t = true) 0 :=
    IsQueryBoundP.of_imp (conv_bad thMax ℓ) hb
  classical
  rw [itsrA_eq]
  refine AllQueriesSatisfy.simulateQ (lazyRes_predR_all _ _ _ h0) fun t ht => ?_
  rcases t with n | (x | q) | u | (⟨pk, a, xs⟩ | ⟨R, pk, root, M⟩)
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · rw [← isQueryBoundP_zero_iff]
    exact liftA_np (fun n => by simp [chOK]) _
  · have hx : xs.length ≤ thMax := by simpa [predR, badH] using ht
    show AllQueriesSatisfy (out16 <$> chQ (thBlocks pk a xs)) _
    rw [← isQueryBoundP_zero_iff, isQueryBoundP_map_iff, isQueryBoundP_zero_iff]
    refine (allQueriesSatisfy_query_iff _ _).2 ?_
    refine (le_of_eq (thBlocks_length pk a xs)).trans ?_
    exact le_trans (thashCost_mono hx) (le_max_left _ _)
  · have hM : M.length ≤ ℓ := by simpa [predR, badH] using ht
    show AllQueriesSatisfy (do
      let s ← chQ (iblocksH R pk root M)
      let s' ← chQ (oblocksH R pk s)
      return dig30 s') _
    refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 ?_) fun s =>
      allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 ?_) fun s' =>
        allQueriesSatisfy_pure _ _
    · refine (le_of_eq (iblocksH_length R pk root M)).trans ?_
      refine le_trans ?_ (le_max_right _ _)
      have := Nat.div_le_div_right (c := 64) (Nat.add_le_add_right hM 56)
      omega
    · refine (le_of_eq (oblocksH_length R pk s)).trans ?_
      refine le_trans ?_ (le_max_left _ _)
      unfold thashCost
      omega

/-- **Every target query is on a message of at most `ℓ` bytes.** -/
theorem itsrA_tgtOK
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) :
    AllQueriesSatisfy (itsrA S oR d) (tgtOKF (St := St) (Blk := Blk) (msgLe ℓ)) := by
  have hb := itsrOpenP_longTgt (oR₀ oR) d (typedP (prims := P₀) codec₀ S.main)
    (typed_long S hlong)
  have h0 : IsQueryBoundP (openA S oR d)
      (fun t => predR (D := SecIdx) (longTgt ℓ) (fun _ => false) t = true) 0 :=
    IsQueryBoundP.of_imp (conv_longTgt ℓ) hb
  classical
  rw [itsrA_eq]
  refine AllQueriesSatisfy.simulateQ (lazyRes_predR_all _ _ _ h0) fun t ht => ?_
  rcases t with n | (x | q) | u | h
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · have hx : x.2.2.length ≤ ℓ := by simpa [predR, longTgt] using ht
    exact (allQueriesSatisfy_query_iff _ _).2 fun k => hx
  · exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · rw [← isQueryBoundP_zero_iff]
    exact liftA_np (fun n => by simp [tgtOKF]) _
  · rw [← isQueryBoundP_zero_iff]
    exact hashCh_np (fun bs => by simp [tgtOKF]) h

/-- **The returned message has at most `ℓ` bytes.** -/
theorem itsrA_out (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    ∀ kx ∈ support (itsrA S oR d), msgLe ℓ kx := by
  intro kx hkx
  rw [itsrA_eq] at hkx
  have h1 := support_simulateQ_subset _ _ hkx
  unfold lazyRes at h1
  have h2 := support_simulateQ_run'_subset _ _ _ h1
  exact itsrOpenP_out (oR₀ oR) d (typedP (prims := P₀) codec₀ S.main) (typed_out S hout) kx h2

end Counts

end Ideal.Realize.Itsr

#print axioms Ideal.Realize.Itsr.thBlocks_secondP
#print axioms Ideal.Realize.Itsr.itsrA_raw
#print axioms Ideal.Realize.Itsr.itsrA_rawP
#print axioms Ideal.Realize.Itsr.itsrA_tgt
#print axioms Ideal.Realize.Itsr.itsrA_chain
#print axioms Ideal.Realize.Itsr.itsrA_chainP
#print axioms Ideal.Realize.Itsr.itsrA_chainLen
#print axioms Ideal.Realize.Itsr.itsrA_tgtOK
#print axioms Ideal.Realize.Itsr.itsrA_out

import Reduction.TcrSplitFinal

/-!
# `VerifyAritySound`: verification and the honest structure agree on arities

`Reduction.VerifyAritySound vp prims` (the named hypothesis of `Reduction/TcrSplitFinal.lean`) is
proved here, for every parameter set and primitive bundle, from `Structural vp prims` alone
(which is already its premise).  No extra hypothesis is needed: in particular the four arities
`1, 2, len, k` need **not** be pairwise distinct.

Idea.  The arity of a tweakable-hash call is a function `arityOf vp` of the *address* it is made
at (type word, and for `FORS_TREE` whether the height word is `0`):

* every call of the honest structure is made at an address `a` of the explicit list `mf_all vp`
  with an input of length `arityOf vp a` (`honestCalls_arity`, an ordered trace as in the `mf_*`
  block of `TCR.lean`, now recording `(tweak, arity)`);
* every call of the verification of an **arbitrary** signature is made at an address `a` of
  `mf_all vp` with an input of length `arityOf vp a` (`verifyCalls_arity`; signatures have their
  FIPS shapes in their types, the digest parts are in range by their types, and the chain steps
  of verification stay below `w - 1`);
* `mf_all vp` is a permutation of the ledger `constructionAddresses vp`, whose members satisfy
  `AddressFacts`, on which the tweak encoding is injective (`Structural.keyInj`).

Hence equal tweaks give equal addresses and equal arities, and `arityOf` only takes the values
`1, 2, len, k`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-! ## The arity of an address -/

/-- The arity of the tweakable-hash call made at address `a`: `F` (1) at `WOTS_HASH` and at
height-`0` `FORS_TREE` addresses, `T_len` at `WOTS_PK`, `H` (2) at `TREE` and at `FORS_TREE`
addresses of positive height, `T_k` at `FORS_ROOTS`. -/
def arityOf (vp : ValidatedParams) (a : Adrs) : ℕ :=
  if a.type = 0 then 1
  else if a.type = 1 then vp.params.len
  else if a.type = 2 then 2
  else if a.type = 3 then (if a.word2 = 0 then 1 else 2)
  else vp.params.k

theorem arityOf_mem_arities (a : Adrs) : ∃ i : Fin 4, arityOf vp a = arities vp i := by
  unfold arityOf
  split_ifs
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩

theorem arityOf_chain (adrs : Adrs) (i j : ℕ) :
    arityOf vp ((wotsChainAdrs adrs i).setHashAddress j) = 1 := rfl

theorem arityOf_wotsPk (adrs : Adrs) : arityOf vp (wotsPkAdrs adrs) = vp.params.len := rfl

theorem arityOf_xmssNode (adrs : Adrs) (z t : ℕ) : arityOf vp (xmssNodeAdrs adrs z t) = 2 := rfl

theorem arityOf_forsLeaf (adrs : Adrs) (t : ℕ) : arityOf vp (forsNodeAdrs adrs 0 t) = 1 := rfl

theorem arityOf_forsNode (adrs : Adrs) (z t : ℕ) :
    arityOf vp (forsNodeAdrs adrs (z + 1) t) = 2 := by
  simp [arityOf, forsNodeAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.setTreeHeight,
    Adrs.setTreeIndex, AddrType.toCode]

theorem arityOf_forsPk (adrs : Adrs) : arityOf vp (forsPkAdrs adrs) = vp.params.k := rfl

/-- A call `c` is made at an address of `S` with the arity of that address. -/
def ArGood (vp : ValidatedParams) (prims : Primitives vp.params) (S : List Adrs)
    (c : prims.AdrsKey × List prims.Y) : Prop :=
  ∃ a ∈ S, c.1 = prims.adrsToKey a ∧ c.2.length = arityOf vp a

theorem ArGood.mono {S S' : List Adrs} {c : prims.AdrsKey × List prims.Y}
    (h : ArGood vp prims S c) (hS : ∀ a ∈ S, a ∈ S') : ArGood vp prims S' c := by
  obtain ⟨a, ha, h1, h2⟩ := h
  exact ⟨a, hS a ha, h1, h2⟩

/-! ## The honest structure: ordered trace of `(tweak, arity)` -/

/-- Running `x` appends to the log exactly calls whose `π`-projections are `L.map f`. -/
def ar_Tr {C K A α : Type} (π : C → K) (f : A → K) (x : StateM (List C) α) (L : List A) : Prop :=
  ∀ s, ((x.run s).2.map π) = s.map π ++ L.map f

section tr
variable {C K A : Type} {π : C → K} {f : A → K}

theorem ar_Tr_pure {α : Type} (a : α) : ar_Tr π f (pure a : StateM (List C) α) [] := by
  intro s; show List.map π s = _; simp

theorem ar_Tr_bind {α β : Type} {x : StateM (List C) α} {g : α → StateM (List C) β}
    {L₁ L₂ : List A} (hx : ar_Tr π f x L₁) (hg : ∀ a, ar_Tr π f (g a) L₂) :
    ar_Tr π f (x >>= g) (L₁ ++ L₂) := by
  intro s
  have h : (x >>= g).run s = (g (x.run s).1).run (x.run s).2 := rfl
  rw [h, hg, hx]; simp

theorem ar_Tr_cast {α : Type} {x : StateM (List C) α} {L L' : List A}
    (hx : ar_Tr π f x L) (h : L = L') : ar_Tr π f x L' := h ▸ hx

theorem ar_Tr_ofFnM {α : Type} : ∀ {n : ℕ} (g : Fin n → StateM (List C) α)
    (L : Fin n → List A), (∀ i, ar_Tr π f (g i) (L i)) →
    ar_Tr π f (Vector.ofFnM g) ((List.finRange n).flatMap L)
  | 0, g, L, _ => by
      rw [Vector.ofFnM_zero]; exact ar_Tr_cast (ar_Tr_pure _) (by simp)
  | n + 1, g, L, h => by
      rw [Vector.ofFnM_succ]
      refine ar_Tr_cast (ar_Tr_bind (ar_Tr_ofFnM (fun i => g i.castSucc) (fun i => L i.castSucc)
        (fun i => h _)) (fun xs => ar_Tr_bind (h (Fin.last n)) (fun x => ar_Tr_pure _))) ?_
      rw [List.finRange_succ_last]
      simp [List.flatMap_map]

theorem ar_Tr_forM {β : Type} (g : β → StateM (List C) PUnit) (L : β → List A)
    (h : ∀ b, ar_Tr π f (g b) (L b)) : ∀ l : List β, ar_Tr π f (l.forM g) (l.flatMap L)
  | [] => by
      exact ar_Tr_cast (ar_Tr_pure _) (by simp)
  | b :: l => by
      show ar_Tr π f (g b >>= fun _ => l.forM g) _
      exact ar_Tr_cast (ar_Tr_bind (h b) (fun _ => ar_Tr_forM g L h l)) (by simp)

/-- As `mf_Tr_merkle`, but the node callback is only inspected at positive heights. -/
theorem ar_Tr_merkle {Y : Type} (leafM : ℕ → StateM (List C) Y)
    (nodeHash : ℕ → ℕ → Y → Y → StateM (List C) Y) (leaf : ℕ → List A) (node : ℕ → ℕ → A)
    (hl : ∀ t, ar_Tr π f (leafM t) (leaf t))
    (hn : ∀ h i l r, ar_Tr π f (nodeHash (h + 1) i l r) [node (h + 1) i]) :
    ∀ z t, ar_Tr π f (PerfectMerkleTree.merkleRootM leafM nodeHash z t) (mf_M leaf node z t)
  | 0, t => hl t
  | z + 1, t => by
      rw [PerfectMerkleTree.merkleRootM, mf_M]
      exact ar_Tr_bind (ar_Tr_merkle leafM nodeHash leaf node hl hn z _) fun _ =>
        ar_Tr_bind (ar_Tr_merkle leafM nodeHash leaf node hl hn z _) fun _ => hn _ _ _ _

end tr

/-- `(tweak, arity)` of a logged call. -/
def arPi (prims : Primitives vp.params) (c : prims.AdrsKey × List prims.Y) : prims.AdrsKey × ℕ :=
  (c.1, c.2.length)

/-- `(tweak, arity)` of an address. -/
def arF (vp : ValidatedParams) (prims : Primitives vp.params) (a : Adrs) : prims.AdrsKey × ℕ :=
  (prims.adrsToKey a, arityOf vp a)

theorem ar_Tr_logTh (pk : prims.PkSeed) (a : Adrs) (xs : List prims.Y)
    (h : xs.length = arityOf vp a) :
    ar_Tr (arPi prims) (arF vp prims) (logTh pk (prims.adrsToKey a) xs) [a] := by
  intro s
  show List.map (arPi prims) (s ++ [(prims.adrsToKey a, xs)]) = _
  simp [arPi, arF, h]

theorem ar_Tr_chain (pk : prims.PkSeed) (adrs : Adrs) (i : ℕ) (x : prims.Y) : ∀ s : ℕ,
    ar_Tr (arPi prims) (arF vp prims)
      (chainWith (fun a x => logTh (prims := prims) pk (prims.adrsToKey a) [x])
        (wotsChainAdrs adrs i) x 0 s)
      ((List.range s).map fun j => (wotsChainAdrs adrs i).setHashAddress j)
  | 0 => by rw [chainWith_zero]; exact ar_Tr_cast (ar_Tr_pure _) (by simp)
  | s + 1 => by
      rw [chainWith_succ]
      refine ar_Tr_cast (ar_Tr_bind (ar_Tr_chain pk adrs i x s) fun _ =>
        ar_Tr_logTh pk _ _ (arityOf_chain adrs i _).symm) ?_
      simp [List.range_succ]

theorem ar_Tr_wots (tbl : SecretTable vp prims) (pk : prims.PkSeed) (adrs : Adrs) :
    ar_Tr (arPi prims) (arF vp prims)
      (wotsPkGenWithSecret prims.core (fun a x => logTh (prims := prims) pk (prims.adrsToKey a) [x])
        (fun a xs => logTh pk (prims.adrsToKey a) xs)
        (fun a => pure (secretOf vp prims tbl a)) adrs)
      (mf_wotsL vp adrs) := by
  rw [wotsPkGenWithSecret, wotsPkGenTopsWithSecret, mf_wotsL]
  refine ar_Tr_bind (ar_Tr_ofFnM _ _ fun i => ?_) fun tops =>
    ar_Tr_logTh pk _ _ (Vector.length_toList.trans (arityOf_wotsPk adrs).symm)
  exact ar_Tr_cast (ar_Tr_bind (ar_Tr_pure _) fun x => ar_Tr_chain pk _ _ x _) (by simp)

theorem ar_Tr_xmss (tbl : SecretTable vp prims) (pk : prims.PkSeed) (adrs : Adrs) :
    ar_Tr (arPi prims) (arF vp prims)
      (xmssRootWithSecret prims.core (fun a x => logTh (prims := prims) pk (prims.adrsToKey a) [x])
        (fun a xs => logTh pk (prims.adrsToKey a) xs)
        (fun a l r => logTh pk (prims.adrsToKey a) [l, r])
        (fun a => pure (secretOf vp prims tbl a)) adrs)
      (mf_xmssL vp adrs) := by
  rw [xmssRootWithSecret, xmssNodeWithSecret, mf_xmssL]
  refine ar_Tr_merkle _ _ (fun t => mf_wotsL vp (wotsLeafAdrs adrs t)) (xmssNodeAdrs adrs)
    (fun t => ?_) (fun h i l r => ?_) _ _
  · unfold xmssLeafWithSecret; exact ar_Tr_wots tbl pk _
  · unfold xmssNodeHashWith; exact ar_Tr_logTh pk _ _ (arityOf_xmssNode adrs _ _).symm

theorem ar_Tr_fors (tbl : SecretTable vp prims) (pk : prims.PkSeed) (adrs : Adrs) :
    ar_Tr (arPi prims) (arF vp prims)
      (forsPkGenWithSecret prims.core (fun a x => logTh (prims := prims) pk (prims.adrsToKey a) [x])
        (fun a l r => logTh pk (prims.adrsToKey a) [l, r])
        (fun a xs => logTh pk (prims.adrsToKey a) xs)
        (fun a => pure (secretOf vp prims tbl a)) adrs)
      (mf_forsL vp adrs) := by
  rw [forsPkGenWithSecret, mf_forsL]
  refine ar_Tr_bind (ar_Tr_ofFnM _ _ fun i => ?_) fun roots =>
    ar_Tr_logTh pk _ _ (Vector.length_toList.trans (arityOf_forsPk adrs).symm)
  rw [forsRootWithSecret]
  refine ar_Tr_merkle _ _ (fun t => [forsNodeAdrs adrs 0 t]) (forsNodeAdrs adrs)
    (fun t => ?_) (fun h i l r => ?_) _ _
  · unfold forsLeafWithSecret
    exact ar_Tr_cast (ar_Tr_bind (ar_Tr_pure _) fun x =>
      ar_Tr_logTh pk _ _ (arityOf_forsLeaf adrs t).symm) (by simp)
  · unfold forsNodeHashWith; exact ar_Tr_logTh pk _ _ (arityOf_forsNode adrs _ _).symm

theorem ar_Tr_all (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    ar_Tr (arPi prims) (arF vp prims)
      (structureVia (vp := vp) (logTh pk) (fun a => pure (secretOf vp prims tbl a)))
      (mf_all vp) := by
  rw [structureVia, mf_all]
  refine ar_Tr_bind (ar_Tr_forM _ _ (fun bp => ?_) _) fun _ => ar_Tr_forM _ _ (fun c => ?_) _
  · exact ar_Tr_cast (ar_Tr_bind (ar_Tr_fors tbl pk _) fun _ => ar_Tr_pure _) (by simp)
  · exact ar_Tr_cast (ar_Tr_bind (ar_Tr_xmss tbl pk _) fun _ => ar_Tr_pure _) (by simp)

/-- **Honest structure.**  The `(tweak, arity)` list of the honest calls is the image of the
explicit address list `mf_all vp`, in order. -/
theorem honestCalls_map_arity (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    (honestCalls tbl pk).map (arPi prims) = (mf_all vp).map (arF vp prims) := by
  have h := ar_Tr_all tbl pk []
  simpa [honestCalls] using h

theorem honestCalls_arity (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    ∀ t ∈ honestCalls tbl pk, ArGood vp prims (mf_all vp) t := by
  intro t ht
  have h : arPi prims t ∈ (mf_all vp).map (arF vp prims) := by
    rw [← honestCalls_map_arity tbl pk]; exact List.mem_map_of_mem ht
  obtain ⟨a, ha, hat⟩ := List.mem_map.mp h
  exact ⟨a, ha, (congrArg Prod.fst hat).symm, (congrArg Prod.snd hat).symm⟩

/-! ## Verification of an arbitrary signature (writer monad of `TCR.lean`) -/

section Verify

open sub_W

theorem ar_calls_wTh (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    calls (sub_wTh pk key xs) = [(key, xs)] := rfl

/-- Calls of a chain segment are `F` calls at hash addresses below `a + n`. -/
theorem ar_mem_chain (pk : prims.PkSeed) (adrs : Adrs) (a : ℕ) : ∀ (n : ℕ) (x : prims.Y),
    ∀ c ∈ calls (chainWith (fun a x => sub_wTh pk (prims.adrsToKey a) [x]) adrs x a n),
      ∃ j, j < a + n ∧ ∃ y : prims.Y, c = (prims.adrsToKey (adrs.setHashAddress j), [y])
  | 0, x => by
      intro c hc
      rw [chainWith_zero] at hc
      exact absurd hc List.not_mem_nil
  | n + 1, x => by
      intro c hc
      rw [chainWith_succ, calls_bind, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨j, hj, y, rfl⟩ := ar_mem_chain pk adrs a n x c hc
        exact ⟨j, by omega, y, rfl⟩
      · rw [ar_calls_wTh, List.mem_singleton] at hc
        exact ⟨a + n, by omega, _, hc⟩

open PerfectMerkleTree in
/-- Calls of a climb along `auth` are node calls at heights `1 … auth.length`, at the ancestors
of `idx`. -/
theorem ar_mem_climb {C Y : Type} (node : ℕ → ℕ → Y → Y → sub_W C Y) (idx : ℕ) (x : Y) :
    ∀ (auth : List Y), ∀ c ∈ calls (climbM node idx x auth),
      ∃ h, h < auth.length ∧ ∃ l r, c ∈ calls (node (h + 1) (idx / 2 ^ (h + 1)) l r) := by
  intro auth
  induction auth using List.reverseRecOn with
  | nil =>
    intro c hc
    rw [climbM_nil] at hc
    exact absurd hc List.not_mem_nil
  | append_singleton auth a ih =>
    intro c hc
    rw [climbM_concat, calls_bind, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨h, hh, l, r, hlr⟩ := ih c hc
      exact ⟨h, by rw [List.length_append]; exact Nat.lt_add_right _ hh, l, r, hlr⟩
    · refine ⟨auth.length, by simp, ?_⟩
      split_ifs at hc
      · exact ⟨_, _, hc⟩
      · exact ⟨_, _, hc⟩

theorem ar_wots (pk : prims.PkSeed) (sig : WotsSig vp.params prims.core) (msg : prims.Y)
    (adrs : Adrs) :
    ∀ c ∈ calls (wotsPkFromSigWith prims.core
        (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
        (fun a xs => sub_wTh pk (prims.adrsToKey a) xs) sig msg adrs),
      ArGood vp prims (mf_wotsL vp adrs) c := by
  intro c hc
  unfold wotsPkFromSigWith at hc
  rw [calls_bind, List.mem_append] at hc
  rcases hc with hc | hc
  · unfold wotsPkFromSigTopsWith at hc
    rw [mem_calls_ofFnM] at hc
    obtain ⟨i, hi⟩ := hc
    obtain ⟨j, hj, y, rfl⟩ := ar_mem_chain pk _ _ _ _ c hi
    have hle := chainStepsCore_le prims.core msg i.val
    refine ⟨_, ?_, rfl, (arityOf_chain adrs i.val j).symm⟩
    unfold mf_wotsL
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩⟩)
  · rw [ar_calls_wTh, List.mem_singleton] at hc
    subst hc
    refine ⟨_, ?_, rfl, Vector.length_toList.trans (arityOf_wotsPk adrs).symm⟩
    unfold mf_wotsL
    exact List.mem_append_right _ (List.mem_singleton_self _)

theorem ar_xmss (pk : prims.PkSeed) (idx : ℕ) (hidx : idx < 2 ^ vp.params.hp)
    (sig : XmssSig vp.params prims.core) (msg : prims.Y) (adrs : Adrs) :
    ∀ c ∈ calls (xmssPkFromSigWith prims.core
        (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
        (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
        (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r]) idx sig msg adrs),
      ArGood vp prims (mf_xmssL vp adrs) c := by
  intro c hc
  unfold xmssPkFromSigWith at hc
  rw [calls_bind, List.mem_append] at hc
  rcases hc with hc | hc
  · refine (ar_wots pk _ _ _ c hc).mono fun a ha => ?_
    exact mf_M_leaf_mem _ _ (i := idx) ha _ _ (Nat.div_eq_of_lt hidx)
  · obtain ⟨h, hh, l, r, hlr⟩ := ar_mem_climb _ _ _ _ c hc
    rw [Vector.length_toList] at hh
    unfold xmssNodeHashWith at hlr
    rw [ar_calls_wTh, List.mem_singleton] at hlr
    subst hlr
    refine ⟨_, ?_, rfl, (arityOf_xmssNode adrs _ _).symm⟩
    refine mf_M_node_mem _ _ (Nat.succ_pos h) _ _ hh ?_
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_of_le hh]
    exact Nat.div_eq_of_lt hidx

open GeneralHypertree in
theorem ar_ht (pk : prims.PkSeed) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : prims.Y) (sigs : Vector (XmssSig vp.params prims.core) layers),
      ∀ c ∈ calls (recoverFromPositionWith vp prims.core
          (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
          (fun a xs => sub_wTh pk (prims.adrsToKey a) xs)
          (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r]) pk pos layers h msg sigs),
        ∃ coord : LayerTreeCoord vp, ArGood vp prims (mf_xmssL vp coord.toAdrs) c
  | 0, pos, h, msg, sigs => by
    intro c hc
    exact absurd hc List.not_mem_nil
  | 1, pos, h, msg, sigs => by
    intro c hc
    exact ⟨LayerTreeCoord.ofPosition pos, ar_xmss pk pos.leaf.val pos.leaf.isLt _ _ _ c hc⟩
  | layers + 2, pos, h, msg, sigs => by
    intro c hc
    rw [recoverFromPositionWith, calls_bind, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨LayerTreeCoord.ofPosition pos, ar_xmss pk pos.leaf.val pos.leaf.isLt _ _ _ c hc⟩
    · exact ar_ht pk (layers + 1) _ _ _ _ c hc

theorem ar_fors (pk : prims.PkSeed) (sig : ForsSigCore vp.params prims.core) (md : List Byte)
    (adrs : Adrs) :
    ∀ c ∈ calls (forsPkFromSigWith prims.core
        (fun a x => sub_wTh pk (prims.adrsToKey a) [x])
        (fun a l r => sub_wTh pk (prims.adrsToKey a) [l, r])
        (fun a xs => sub_wTh pk (prims.adrsToKey a) xs) sig md adrs),
      ArGood vp prims (mf_forsL vp adrs) c := by
  intro c hc
  unfold forsPkFromSigWith at hc
  rw [calls_bind, List.mem_append] at hc
  rcases hc with hc | hc
  · rw [mem_calls_ofFnM] at hc
    obtain ⟨i, hi⟩ := hc
    rw [calls_bind, List.mem_append] at hi
    have hdiv := sub_fors_idx_div (p := vp.params) md i.val
    rcases hi with hi | hi
    · rw [ar_calls_wTh, List.mem_singleton] at hi
      subst hi
      refine ⟨_, ?_, rfl, (arityOf_forsLeaf adrs _).symm⟩
      unfold mf_forsL
      refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩)
      exact mf_M_leaf_mem _ _ (List.mem_singleton_self _) _ _ hdiv
    · obtain ⟨h, hh, l, r, hlr⟩ := ar_mem_climb _ _ _ _ c hi
      rw [Vector.length_toList] at hh
      unfold forsNodeHashWith at hlr
      rw [ar_calls_wTh, List.mem_singleton] at hlr
      subst hlr
      refine ⟨_, ?_, rfl, (arityOf_forsNode adrs _ _).symm⟩
      unfold mf_forsL
      refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩)
      refine mf_M_node_mem _ _ (Nat.succ_pos h) _ _ hh ?_
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_of_le hh]
      exact hdiv
  · rw [ar_calls_wTh, List.mem_singleton] at hc
    subst hc
    refine ⟨_, ?_, rfl, Vector.length_toList.trans (arityOf_forsPk adrs).symm⟩
    unfold mf_forsL
    exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **Verification.**  Every hash call of the verification of an arbitrary signature under an
arbitrary public key is made at an address of the honest structure, with that address's arity. -/
theorem verifyCalls_arity (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    ∀ c ∈ verifyCalls pk msg sig, ArGood vp prims (mf_all vp) c := by
  intro c hc
  rw [sub_verifyCalls_eq, calls_bind, List.mem_append] at hc
  rcases hc with hc | hc
  · refine (ar_fors pk.pkSeed _ _ _ c hc).mono fun a ha => ?_
    rw [← BottomPosition.forsAdrs_ofDigestParts] at ha
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, mem_allBottomPositions vp _, ha⟩)
  · obtain ⟨coord, hcoord⟩ := ar_ht pk.pkSeed _ _ _ _ _ c hc
    refine hcoord.mono fun a ha => ?_
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨coord, mem_allXmssTrees vp coord, ha⟩)

end Verify

/-! ## The hypothesis of `TcrSplitFinal.lean` -/

theorem mf_all_subset_ledger : ∀ a ∈ mf_all vp, a ∈ constructionAddresses vp :=
  ((((constructionAddresses_nodup vp).subperm mf_ledger_subset).perm_of_length_le
    (le_of_eq mf_all_length)).symm).subset

/-- **Arity soundness, for arbitrary keys.**  Under the structural side conditions, a hash call
of the verification of any signature under any public key and a call of the honest structure of
any table and seed at the same tweak have the same arity, one of `1, 2, len, k`. -/
theorem verifyCalls_honestCalls_arity (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    ∀ c ∈ verifyCalls pk msg sig, ∀ t ∈ honestCalls tbl pkSeed,
      t.1 = c.1 → c.2.length = t.2.length ∧ ∃ i : Fin 4, t.2.length = arities vp i := by
  intro c hc t ht hkey
  obtain ⟨a, ha, hak, hal⟩ := verifyCalls_arity pk msg sig c hc
  obtain ⟨b, hb, hbk, hbl⟩ := honestCalls_arity tbl pkSeed t ht
  have hab : b = a := hS.keyInj
    (addressFacts_of_mem_constructionAddresses hS.bounds (mf_all_subset_ledger b hb))
    (addressFacts_of_mem_constructionAddresses hS.bounds (mf_all_subset_ledger a ha))
    (hbk.symm.trans (hkey.trans hak))
  subst hab
  refine ⟨hal.trans hbl.symm, ?_⟩
  obtain ⟨i, hi⟩ := arityOf_mem_arities (vp := vp) b
  exact ⟨i, hbl.trans hi⟩

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-- **`VerifyAritySound` holds** — the named hypothesis of `Reduction/TcrSplitFinal.lean`, for
every validated parameter set and every primitive bundle. -/
theorem verifyAritySound : VerifyAritySound vp prims :=
  fun hS tbl pkSeed msg sig =>
    verifyCalls_honestCalls_arity hS tbl pkSeed (idealPk vp prims tbl pkSeed) msg sig

#print axioms honestCalls_arity
#print axioms verifyCalls_arity
#print axioms verifyCalls_honestCalls_arity
#print axioms verifyAritySound

end Reduction

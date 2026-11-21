import Reduction.Harness
import HashSig.SLHDSA.Security.NodeGraph

/-!
# Step 6: the collision branch (SM-TCR on `Thash`)

`bTcr A` (EC: `R_TRHSMDTTCRC_EUFCMA`, `R_TRCOSMDTTCRC_EUFCMA`, `R_SMDTTCRCPKCO_EUFNAGCMA`,
`R_SMDTTCRCTRH_EUFNAGCMA` merged into one adversary, because `Thash` is attacked as a whole):

* `choose` (seed hidden): sample the secret table and evaluate the **entire honest structure** —
  every FORS public key and every XMSS tree of the hypertree — through the challenge oracle, in
  the fixed order of `structureVia`.  Each tweakable-hash call of the structure is one target;
  the tweaks are the encodings of the union ledger `constructionAddresses`, hence distinct, and
  there are `tcrTargets vp` of them
  (`tcrTargets vp = 2^h·(k·(2^(a+1)−1)+1) + #inst·(len·(w−1)+1) + 2^h − 1`,
  `Resources.tcrTargets_eq'`).
* `forge` (seed revealed): recompute the list of targets (`honestCalls`), run `A` once exactly as
  `G2` does (`g2Run`), list the hash calls of verifying the forgery (`verifyCalls`), and output
  the first verification call that collides with a target at the same tweak on a different input.

The reduction is choice-free, black-box and straight-line and runs `A` once.  It is not
feasible: `choose` evaluates the whole key structure through the challenge oracle (`tcrTargets vp`
targets; `1062560399506556770327551 ≈ 2^79.81` at 128s, `Resources.tcrTargets_128s_val`) and
`forge` recomputes it; in addition `choose` as written samples the eager `2^256`-cell
`sampleTable` (replaced by `structSecIdx`-many samples, `≈ 2^78.81`, in
`Reduction/Lazy/TcrSparse.lean`).  The work is exponential in `h` in any variant, as in the
paper, whose reduction also costs one evaluation of the key structure.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-- Evaluate the whole honest structure — the FORS public key of every bottom position
(`allBottomPositions vp`) and the root of every XMSS tree (`allXmssTrees vp`), in the order of
these explicit enumerations — with every tweakable-hash call routed to `th` and every secret read
routed to `secret`. -/
noncomputable def structureVia {m : Type → Type} [Monad m]
    (th : prims.AdrsKey → List prims.Y → m prims.Y) (secret : Adrs → m prims.Y) : m Unit := do
  (allBottomPositions vp).forM fun bp => do
    let _ ← forsPkGenWithSecret prims.core (fun a x => th (prims.adrsToKey a) [x])
      (fun a l r => th (prims.adrsToKey a) [l, r]) (fun a xs => th (prims.adrsToKey a) xs)
      secret bp.forsAdrs
    pure ()
  (allXmssTrees vp).forM fun c => do
    let _ ← xmssRootWithSecret prims.core (fun a x => th (prims.adrsToKey a) [x])
      (fun a xs => th (prims.adrsToKey a) xs) (fun a l r => th (prims.adrsToKey a) [l, r])
      secret c.toAdrs
    pure ()

/-- A hash callback that evaluates `Thash` at `pk` and appends the call to a log. -/
def logTh (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    StateM (List (prims.AdrsKey × List prims.Y)) prims.Y := do
  modify (· ++ [(key, xs)])
  pure (prims.Thash pk key xs)

/-- All tweakable-hash calls `(tweak, input)` of the honest structure of `(tbl, pk)`, in the
order `structureVia` makes them. -/
noncomputable def honestCalls (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    List (prims.AdrsKey × List prims.Y) :=
  ((structureVia (vp := vp) (logTh pk) (fun a => pure (secretOf vp prims tbl a))).run []).2

/-- All tweakable-hash calls made by verifying `(msg, sig)` under `pk`. -/
def verifyCalls (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) : List (prims.AdrsKey × List prims.Y) :=
  let parts : DigestParts vp.params := digestParts pk sig.randomness msg
  let th := logTh (prims := prims) pk.pkSeed
  let prog : StateM (List (prims.AdrsKey × List prims.Y)) prims.Y := do
    let forsPk ← forsPkFromSigWith prims.core (fun a x => th (prims.adrsToKey a) [x])
      (fun a l r => th (prims.adrsToKey a) [l, r]) (fun a xs => th (prims.adrsToKey a) xs)
      sig.fors parts.md.toList parts.forsAdrs
    GeneralHypertree.pkFromSigWith vp prims.core (fun a x => th (prims.adrsToKey a) [x])
      (fun a xs => th (prims.adrsToKey a) xs) (fun a l r => th (prims.adrsToKey a) [l, r])
      forsPk sig.hypertree pk.pkSeed parts
  (prog.run []).2

/-- The first call of `calls` that collides with a target of `targets` (same tweak, different
input, same `Thash` value), as `(target index, colliding input)`. -/
def findCollision [DecidableEq prims.Y] [DecidableEq prims.AdrsKey] (pk : prims.PkSeed)
    (targets calls : List (prims.AdrsKey × List prims.Y)) : Option (ℕ × List prims.Y) :=
  calls.findSome? fun c =>
    let j := targets.findIdx fun t =>
      decide (t.1 = c.1 ∧ c.2 ≠ t.2 ∧ prims.Thash pk c.1 c.2 = prims.Thash pk t.1 t.2)
    if j < targets.length then some (j, c.2) else none

end Reduction

/-! ## Deterministic trace lemmas: tweaks of the honest structure (`mf_*`) -/

namespace Reduction
variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-! ## Trace predicate -/

/-- Running `x` appends to the log exactly calls whose tweaks are `L.map f`. -/
def mf_Tr {K V A α : Type} (f : A → K) (x : StateM (List (K × V)) α) (L : List A) : Prop :=
  ∀ s, ((x.run s).2.map Prod.fst) = s.map Prod.fst ++ L.map f

section tr
variable {K V A : Type} {f : A → K}

theorem mf_Tr_pure {α : Type} (a : α) : mf_Tr f (pure a : StateM (List (K × V)) α) [] := by
  intro s; show List.map Prod.fst s = _; simp

theorem mf_Tr_bind {α β : Type} {x : StateM (List (K × V)) α} {g : α → StateM (List (K × V)) β}
    {L₁ L₂ : List A} (hx : mf_Tr f x L₁) (hg : ∀ a, mf_Tr f (g a) L₂) :
    mf_Tr f (x >>= g) (L₁ ++ L₂) := by
  intro s
  have h : (x >>= g).run s = (g (x.run s).1).run (x.run s).2 := rfl
  rw [h, hg, hx]; simp

theorem mf_Tr_cast {α : Type} {x : StateM (List (K × V)) α} {L L' : List A}
    (hx : mf_Tr f x L) (h : L = L') : mf_Tr f x L' := h ▸ hx

theorem mf_Tr_ofFnM {α : Type} : ∀ {n : ℕ} (g : Fin n → StateM (List (K × V)) α)
    (L : Fin n → List A), (∀ i, mf_Tr f (g i) (L i)) →
    mf_Tr f (Vector.ofFnM g) ((List.finRange n).flatMap L)
  | 0, g, L, _ => by
      rw [Vector.ofFnM_zero]; exact mf_Tr_cast (mf_Tr_pure _) (by simp)
  | n + 1, g, L, h => by
      rw [Vector.ofFnM_succ]
      refine mf_Tr_cast (mf_Tr_bind (mf_Tr_ofFnM (fun i => g i.castSucc) (fun i => L i.castSucc)
        (fun i => h _)) (fun xs => mf_Tr_bind (h (Fin.last n)) (fun x => mf_Tr_pure _))) ?_
      rw [List.finRange_succ_last]
      simp [List.flatMap_map]

theorem mf_Tr_forM {β : Type} (g : β → StateM (List (K × V)) PUnit) (L : β → List A)
    (h : ∀ b, mf_Tr f (g b) (L b)) : ∀ l : List β, mf_Tr f (l.forM g) (l.flatMap L)
  | [] => by
      exact mf_Tr_cast (mf_Tr_pure _) (by simp)
  | b :: l => by
      show mf_Tr f (g b >>= fun _ => l.forM g) _
      exact mf_Tr_cast (mf_Tr_bind (h b) (fun _ => mf_Tr_forM g L h l)) (by simp)

/-- Addresses of a depth-first Merkle root evaluation. -/
def mf_M (leaf : ℕ → List A) (node : ℕ → ℕ → A) : ℕ → ℕ → List A
  | 0, t => leaf t
  | z + 1, t => mf_M leaf node z (2 * t) ++ (mf_M leaf node z (2 * t + 1) ++ [node (z + 1) t])

theorem mf_Tr_merkle {Y : Type} (leafM : ℕ → StateM (List (K × V)) Y)
    (nodeHash : ℕ → ℕ → Y → Y → StateM (List (K × V)) Y) (leaf : ℕ → List A) (node : ℕ → ℕ → A)
    (hl : ∀ t, mf_Tr f (leafM t) (leaf t)) (hn : ∀ h i l r, mf_Tr f (nodeHash h i l r) [node h i]) :
    ∀ z t, mf_Tr f (PerfectMerkleTree.merkleRootM leafM nodeHash z t) (mf_M leaf node z t)
  | 0, t => hl t
  | z + 1, t => by
      rw [PerfectMerkleTree.merkleRootM, mf_M]
      exact mf_Tr_bind (mf_Tr_merkle leafM nodeHash leaf node hl hn z _) fun _ =>
        mf_Tr_bind (mf_Tr_merkle leafM nodeHash leaf node hl hn z _) fun _ => hn _ _ _ _

theorem mf_M_length (leaf : ℕ → List A) (node : ℕ → ℕ → A) (c : ℕ)
    (hc : ∀ t, (leaf t).length = c) :
    ∀ z t, (mf_M leaf node z t).length = 2 ^ z * c + (2 ^ z - 1)
  | 0, t => by simp [mf_M, hc]
  | z + 1, t => by
      simp only [mf_M, List.length_append, mf_M_length leaf node c hc z, List.length_singleton]
      have : 0 < 2 ^ z := by positivity
      rw [pow_succ]; ring_nf; omega

theorem mf_M_leaf_mem (leaf : ℕ → List A) (node : ℕ → ℕ → A) {x : A} {i : ℕ} (hx : x ∈ leaf i) :
    ∀ z t, i / 2 ^ z = t → x ∈ mf_M leaf node z t
  | 0, t, h => by
      simp at h; subst h; exact hx
  | z + 1, t, h => by
      rw [mf_M]
      have h2 : i / 2 ^ z / 2 = t := by rw [Nat.div_div_eq_div_mul, ← pow_succ]; exact h
      rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ z) with h0 | h1
      · exact List.mem_append_left _ (mf_M_leaf_mem leaf node hx z _ (by omega))
      · exact List.mem_append_right _ (List.mem_append_left _
          (mf_M_leaf_mem leaf node hx z _ (by omega)))

theorem mf_M_node_mem (leaf : ℕ → List A) (node : ℕ → ℕ → A) {h i : ℕ} (hh : 0 < h) :
    ∀ z t, h ≤ z → i / 2 ^ (z - h) = t → node h i ∈ mf_M leaf node z t
  | 0, t, hz, _ => by omega
  | z + 1, t, hz, ht => by
      rw [mf_M]
      rcases Nat.lt_or_ge z h with hlt | hge
      · have : h = z + 1 := by omega
        subst this
        simp at ht; subst ht
        simp
      · have h2 : i / 2 ^ (z - h) / 2 = t := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ]
          rw [show z - h + 1 = z + 1 - h by omega]; exact ht
        rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ (z - h)) with h0 | h1
        · exact List.mem_append_left _ (mf_M_node_mem leaf node hh z _ hge (by omega))
        · exact List.mem_append_right _ (List.mem_append_left _
            (mf_M_node_mem leaf node hh z _ hge (by omega)))

theorem mf_length_flatMap_const {β : Type} (g : β → List A) (c : ℕ) :
    ∀ l : List β, (∀ b ∈ l, (g b).length = c) → (l.flatMap g).length = l.length * c
  | [], _ => by simp
  | b :: l, h => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [h b (by simp), mf_length_flatMap_const g c l (fun b hb => h b (by simp [hb]))]
      ring

end tr

/-! ## Address lists of the components -/

def mf_wotsL (vp : ValidatedParams) (adrs : Adrs) : List Adrs :=
  (List.finRange vp.params.len).flatMap (fun i =>
    (List.range (vp.params.w - 1)).map fun j => (wotsChainAdrs adrs i.val).setHashAddress j) ++
    [wotsPkAdrs adrs]

def mf_xmssL (vp : ValidatedParams) (adrs : Adrs) : List Adrs :=
  mf_M (fun t => mf_wotsL vp (wotsLeafAdrs adrs t)) (xmssNodeAdrs adrs) vp.params.hp 0

def mf_forsL (vp : ValidatedParams) (adrs : Adrs) : List Adrs :=
  (List.finRange vp.params.k).flatMap (fun i =>
    mf_M (fun t => [forsNodeAdrs adrs 0 t]) (forsNodeAdrs adrs) vp.params.a i.val) ++
    [forsPkAdrs adrs]

noncomputable def mf_all (vp : ValidatedParams) : List Adrs :=
  (allBottomPositions vp).flatMap (fun bp => mf_forsL vp bp.forsAdrs) ++
    (allXmssTrees vp).flatMap (fun c => mf_xmssL vp c.toAdrs)

theorem mf_Tr_logTh (pk : prims.PkSeed) (a : Adrs) (xs : List prims.Y) :
    mf_Tr prims.adrsToKey (logTh pk (prims.adrsToKey a) xs) [a] := by
  intro s
  show List.map Prod.fst (s ++ [(prims.adrsToKey a, xs)]) = _
  simp

theorem mf_Tr_chain (pk : prims.PkSeed) (adrs : Adrs) (x : prims.Y) : ∀ s : ℕ,
    mf_Tr prims.adrsToKey
      (chainWith (fun a x => logTh (prims := prims) pk (prims.adrsToKey a) [x]) adrs x 0 s)
      ((List.range s).map fun j => adrs.setHashAddress j)
  | 0 => by rw [chainWith_zero]; exact mf_Tr_cast (mf_Tr_pure _) (by simp)
  | s + 1 => by
      rw [chainWith_succ]
      refine mf_Tr_cast (mf_Tr_bind (mf_Tr_chain pk adrs x s) fun _ => mf_Tr_logTh pk _ _) ?_
      simp [List.range_succ]

theorem mf_Tr_wots (tbl : SecretTable vp prims) (pk : prims.PkSeed) (adrs : Adrs) :
    mf_Tr prims.adrsToKey
      (wotsPkGenWithSecret prims.core (fun a x => logTh (prims := prims) pk (prims.adrsToKey a) [x])
        (fun a xs => logTh pk (prims.adrsToKey a) xs)
        (fun a => pure (secretOf vp prims tbl a)) adrs)
      (mf_wotsL vp adrs) := by
  rw [wotsPkGenWithSecret, wotsPkGenTopsWithSecret, mf_wotsL]
  refine mf_Tr_bind (mf_Tr_ofFnM _ _ fun i => ?_) fun _ => mf_Tr_logTh pk _ _
  exact mf_Tr_cast (mf_Tr_bind (mf_Tr_pure _) fun x => mf_Tr_chain pk _ x _) (by simp)

theorem mf_Tr_xmss (tbl : SecretTable vp prims) (pk : prims.PkSeed) (adrs : Adrs) :
    mf_Tr prims.adrsToKey
      (xmssRootWithSecret prims.core (fun a x => logTh (prims := prims) pk (prims.adrsToKey a) [x])
        (fun a xs => logTh pk (prims.adrsToKey a) xs)
        (fun a l r => logTh pk (prims.adrsToKey a) [l, r])
        (fun a => pure (secretOf vp prims tbl a)) adrs)
      (mf_xmssL vp adrs) := by
  rw [xmssRootWithSecret, xmssNodeWithSecret, mf_xmssL]
  refine mf_Tr_merkle _ _ (fun t => mf_wotsL vp (wotsLeafAdrs adrs t)) (xmssNodeAdrs adrs)
    (fun t => ?_) (fun h i l r => ?_) _ _
  · unfold xmssLeafWithSecret; exact mf_Tr_wots tbl pk _
  · unfold xmssNodeHashWith; exact mf_Tr_logTh pk _ _

theorem mf_Tr_fors (tbl : SecretTable vp prims) (pk : prims.PkSeed) (adrs : Adrs) :
    mf_Tr prims.adrsToKey
      (forsPkGenWithSecret prims.core (fun a x => logTh (prims := prims) pk (prims.adrsToKey a) [x])
        (fun a l r => logTh pk (prims.adrsToKey a) [l, r])
        (fun a xs => logTh pk (prims.adrsToKey a) xs)
        (fun a => pure (secretOf vp prims tbl a)) adrs)
      (mf_forsL vp adrs) := by
  rw [forsPkGenWithSecret, mf_forsL]
  refine mf_Tr_bind (mf_Tr_ofFnM _ _ fun i => ?_) fun _ => mf_Tr_logTh pk _ _
  rw [forsRootWithSecret]
  refine mf_Tr_merkle _ _ (fun t => [forsNodeAdrs adrs 0 t]) (forsNodeAdrs adrs)
    (fun t => ?_) (fun h i l r => ?_) _ _
  · unfold forsLeafWithSecret
    exact mf_Tr_cast (mf_Tr_bind (mf_Tr_pure _) fun x => mf_Tr_logTh pk _ _) (by simp)
  · unfold forsNodeHashWith; exact mf_Tr_logTh pk _ _

theorem mf_Tr_all (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    mf_Tr prims.adrsToKey
      (structureVia (vp := vp) (logTh pk) (fun a => pure (secretOf vp prims tbl a)))
      (mf_all vp) := by
  rw [structureVia, mf_all]
  refine mf_Tr_bind (mf_Tr_forM _ _ (fun bp => ?_) _) fun _ => mf_Tr_forM _ _ (fun c => ?_) _
  · exact mf_Tr_cast (mf_Tr_bind (mf_Tr_fors tbl pk _) fun _ => mf_Tr_pure _) (by simp)
  · exact mf_Tr_cast (mf_Tr_bind (mf_Tr_xmss tbl pk _) fun _ => mf_Tr_pure _) (by simp)

/-! ## Counting -/

theorem mf_wotsL_length (adrs : Adrs) :
    (mf_wotsL vp adrs).length = vp.params.len * (vp.params.w - 1) + 1 := by
  rw [mf_wotsL, List.length_append, mf_length_flatMap_const _ (vp.params.w - 1) _ (by simp)]
  simp

theorem mf_xmssL_length (adrs : Adrs) :
    (mf_xmssL vp adrs).length =
      2 ^ vp.params.hp * (vp.params.len * (vp.params.w - 1) + 1) + (2 ^ vp.params.hp - 1) :=
  mf_M_length _ _ _ (fun _ => mf_wotsL_length _) _ _

theorem mf_forsL_length (adrs : Adrs) :
    (mf_forsL vp adrs).length =
      vp.params.k * (2 ^ vp.params.a * 1 + (2 ^ vp.params.a - 1)) + 1 := by
  rw [mf_forsL, List.length_append, mf_length_flatMap_const _ _ _
    (fun i _ => mf_M_length _ _ 1 (fun _ => rfl) _ _)]
  simp

theorem mf_univ_length : (allXmssTrees vp).length = xmssTreeCount vp.params :=
  allXmssTrees_length vp

theorem mf_all_length : (mf_all vp).length = (constructionAddresses vp).length := by
  rw [constructionAddresses_length, mf_all, List.length_append,
    mf_length_flatMap_const _ _ _ (fun bp _ => mf_forsL_length (vp := vp) bp.forsAdrs),
    mf_length_flatMap_const _ _ _ (fun c _ => mf_xmssL_length (vp := vp) c.toAdrs),
    allBottomPositions_length, mf_univ_length]
  simp only [targetCount, wotsInstanceCount_eq_xmssTreeCount_mul]
  generalize 2 ^ vp.params.a - 1 = A
  generalize 2 ^ vp.params.hp - 1 = B
  generalize vp.params.w - 1 = W
  ring

/-! ## Membership -/

theorem mf_ledger_subset : constructionAddresses vp ⊆ mf_all vp := by
  intro x hx
  rw [mem_constructionAddresses_iff] at hx
  have hfors : ∀ (bp : BottomPosition vp), x ∈ mf_forsL vp bp.forsAdrs → x ∈ mf_all vp :=
    fun bp h => List.mem_append_left _ (List.mem_flatMap.mpr ⟨bp, mem_allBottomPositions vp bp, h⟩)
  have hxmss : ∀ (c : LayerTreeCoord vp), x ∈ mf_xmssL vp c.toAdrs → x ∈ mf_all vp :=
    fun c h => List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, mem_allXmssTrees vp c, h⟩)
  have hwots : ∀ (pos : LayerPosition vp), x ∈ mf_wotsL vp (wotsInstanceAdrs pos) →
      x ∈ mf_all vp := fun pos h =>
    hxmss ⟨pos.layer, pos.tree⟩ (mf_M_leaf_mem _ _ (i := pos.leaf.val) h _ _
      (Nat.div_eq_of_lt pos.leaf.isLt))
  rcases hx with hx | hx | hx | hx | hx | hx
  · simp only [forsLeafAddresses, List.mem_map] at hx
    obtain ⟨⟨⟨bp, i⟩, j⟩, -, rfl⟩ := hx
    refine hfors bp (List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩))
    refine mf_M_leaf_mem _ _ (List.mem_singleton_self _) _ _ ?_
    have hj : j.val < 2 ^ vp.params.a := j.isLt
    show (i.val * 2 ^ vp.params.a + j.val) / 2 ^ vp.params.a = i.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hj, Nat.zero_add]
  · simp only [forsTreeAddresses, List.mem_map] at hx
    obtain ⟨⟨⟨bp, i⟩, ⟨z, idx⟩⟩, hmem, rfl⟩ := hx
    have hzi : (z, idx) ∈ perfectInternalCoords vp.params.a := (List.mem_product.mp hmem).2
    obtain ⟨hz, hza, hidx⟩ := mem_perfectInternalCoords.mp hzi
    refine hfors bp (List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩))
    refine mf_M_node_mem _ _ hz _ _ hza ?_
    show (i.val * 2 ^ (vp.params.a - z) + idx) / 2 ^ (vp.params.a - z) = i.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hidx,
      Nat.zero_add]
  · simp only [forsRootAddresses, List.mem_map] at hx
    obtain ⟨bp, -, rfl⟩ := hx
    exact hfors bp (List.mem_append_right _ (List.mem_singleton_self _))
  · simp only [wotsStepAddresses, List.mem_map] at hx
    obtain ⟨⟨⟨pos, i⟩, j⟩, -, rfl⟩ := hx
    refine hwots pos (List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩))
    exact List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩
  · simp only [wotsPkAddresses, List.mem_map] at hx
    obtain ⟨pos, -, rfl⟩ := hx
    exact hwots pos (List.mem_append_right _ (List.mem_singleton_self _))
  · simp only [xmssNodeAddresses, List.mem_map] at hx
    obtain ⟨⟨c, ⟨z, idx⟩⟩, hmem, rfl⟩ := hx
    have hzi : (z, idx) ∈ perfectInternalCoords vp.params.hp := (List.mem_product.mp hmem).2
    obtain ⟨hz, hza, hidx⟩ := mem_perfectInternalCoords.mp hzi
    exact hxmss c (mf_M_node_mem _ _ hz _ _ hza (Nat.div_eq_of_lt hidx))

theorem mf_honestCalls_map_fst (_hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : prims.PkSeed) :
    ((honestCalls tbl pk).map (·.1)).Perm ((constructionAddresses vp).map prims.adrsToKey) := by
  have h := mf_Tr_all tbl pk []
  have hp : (mf_all vp).Perm (constructionAddresses vp) :=
    (((constructionAddresses_nodup vp).subperm mf_ledger_subset).perm_of_length_le
      (le_of_eq mf_all_length)).symm
  have h' : (honestCalls tbl pk).map (·.1) = (mf_all vp).map prims.adrsToKey := by
    simpa [honestCalls] using h
  rw [h']
  exact hp.map _

end Reduction

/-! ## Deterministic trace lemmas: two-signature comparison and correctness (`col_*`) -/

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-! ## Logging interpreter -/

/-- Logging interpreter: answers like `PublicHash.impl` and appends each `Thash` call. -/
def col_logImpl (prims : Primitives vp.params) :
    QueryImpl (publicHashSpec prims.core) (StateM (List (prims.AdrsKey × List prims.Y)))
  | .thash pkSeed key xs => do
      modify (· ++ [(key, xs)])
      pure (prims.Thash pkSeed key xs)
  | .hmsg r pkSeed pkRoot msg => pure (prims.Hmsg r pkSeed pkRoot msg)

/-- The calls logged by a program. -/
def col_calls {α : Type} (oa : OracleComp (publicHashSpec prims.core) α) :
    List (prims.AdrsKey × List prims.Y) :=
  ((simulateQ (col_logImpl prims) oa).run []).2

theorem col_run {α : Type} (oa : OracleComp (publicHashSpec prims.core) α)
    (s : List (prims.AdrsKey × List prims.Y)) :
    (simulateQ (col_logImpl prims) oa).run s =
      (simulateQ (PublicHash.impl prims) oa, s ++ col_calls oa) := by
  unfold col_calls
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => exact Prod.ext rfl (List.append_nil s).symm
  | query_bind t f ih =>
    cases t with
    | thash pkSeed key xs =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change (simulateQ (col_logImpl prims) (f (prims.Thash pkSeed key xs))).run
          (s ++ [(key, xs)]) =
        (simulateQ (PublicHash.impl prims) (f (prims.Thash pkSeed key xs)),
          s ++ ((simulateQ (col_logImpl prims) (f (prims.Thash pkSeed key xs))).run
            ([] ++ [(key, xs)])).2)
      rw [ih _ (s ++ [(key, xs)]), ih _ ([] ++ [(key, xs)])]
      refine Prod.ext rfl ?_
      simp [List.append_assoc]
    | hmsg r pkSeed pkRoot msg =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change (simulateQ (col_logImpl prims) (f (prims.Hmsg r pkSeed pkRoot msg))).run s =
        (simulateQ (PublicHash.impl prims) (f (prims.Hmsg r pkSeed pkRoot msg)),
          s ++ ((simulateQ (col_logImpl prims) (f (prims.Hmsg r pkSeed pkRoot msg))).run []).2)
      exact ih _ s

theorem col_calls_pure {α : Type} (x : α) :
    col_calls (prims := prims) (pure x : OracleComp (publicHashSpec prims.core) α) = [] := rfl

theorem col_calls_bind {α β : Type} (oa : OracleComp (publicHashSpec prims.core) α)
    (f : α → OracleComp (publicHashSpec prims.core) β) :
    col_calls (oa >>= f) = col_calls oa ++ col_calls (f (simulateQ (PublicHash.impl prims) oa)) := by
  unfold col_calls
  rw [simulateQ_bind, StateT.run_bind]
  change ((simulateQ (col_logImpl prims) (f ((simulateQ (col_logImpl prims) oa).run []).1)).run
    ((simulateQ (col_logImpl prims) oa).run []).2).2 = _
  rw [col_run oa [], col_run]
  simp [col_calls]

theorem col_calls_f (pk : prims.PkSeed) (a : Adrs) (x : prims.Y) :
    col_calls (PublicHash.f prims.core pk a x : OracleComp (publicHashSpec prims.core) prims.Y) =
      [(prims.adrsToKey a, [x])] := by
  unfold col_calls PublicHash.f
  rw [simulateQ_HasQuery_query]; rfl

theorem col_calls_h (pk : prims.PkSeed) (a : Adrs) (l r : prims.Y) :
    col_calls (PublicHash.h prims.core pk a l r : OracleComp (publicHashSpec prims.core) prims.Y) =
      [(prims.adrsToKey a, [l, r])] := by
  unfold col_calls PublicHash.h
  rw [simulateQ_HasQuery_query]; rfl

theorem col_calls_tl (pk : prims.PkSeed) (a : Adrs) (xs : List prims.Y) :
    col_calls (PublicHash.tl prims.core pk a xs : OracleComp (publicHashSpec prims.core) prims.Y) =
      [(prims.adrsToKey a, xs)] := by
  unfold col_calls PublicHash.tl
  rw [simulateQ_HasQuery_query]; rfl

theorem col_mem_bind_left {α β : Type} {oa : OracleComp (publicHashSpec prims.core) α}
    (f : α → OracleComp (publicHashSpec prims.core) β) {c} (h : c ∈ col_calls oa) :
    c ∈ col_calls (oa >>= f) := by
  rw [col_calls_bind]; exact List.mem_append_left _ h

theorem col_mem_bind_right {α β : Type} (oa : OracleComp (publicHashSpec prims.core) α)
    {f : α → OracleComp (publicHashSpec prims.core) β} {c}
    (h : c ∈ col_calls (f (simulateQ (PublicHash.impl prims) oa))) :
    c ∈ col_calls (oa >>= f) := by
  rw [col_calls_bind]; exact List.mem_append_right _ h

theorem col_mem_ofFnM {α : Type} {k : ℕ} (g : Fin k → OracleComp (publicHashSpec prims.core) α)
    (i : Fin k) {c} (h : c ∈ col_calls (g i)) : c ∈ col_calls (Vector.ofFnM g) := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [Vector.ofFnM_succ]
    rcases Fin.lastCases (motive := fun i => i = Fin.last k ∨ ∃ j : Fin k, i = j.castSucc)
      (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i with rfl | ⟨j, rfl⟩
    · exact col_mem_bind_right _ (col_mem_bind_left _ h)
    · exact col_mem_bind_left _ (ih (fun i => g i.castSucc) j h)

/-! ## `verifyCalls` as the calls of the two canonical programs -/

/-- Query capability of the logging monad (local to the proofs below). -/
@[reducible] def col_hasQuery (prims : Primitives vp.params) :
    HasQuery (publicHashSpec prims.core) (StateM (List (prims.AdrsKey × List prims.Y))) :=
  ⟨col_logImpl prims⟩

/-- `simulateQ (col_logImpl prims)` as a query-preserving morphism. -/
def col_hom (prims : Primitives vp.params) :
    @HasQuery.QueryHom _ (publicHashSpec prims.core) (OracleComp (publicHashSpec prims.core)) _ _
      (StateM (List (prims.AdrsKey × List prims.Y))) _ (col_hasQuery prims) :=
  letI := col_hasQuery prims
  { toMonadHom := simulateQ' (col_logImpl prims)
    map_query' := fun t => simulateQ_HasQuery_query (col_logImpl prims) t }

theorem col_verifyCalls_eq (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    verifyCalls pk msg sig =
      col_calls (forsPkFromSigM prims.core sig.fors (digestParts pk sig.randomness msg).md.toList
        pk.pkSeed (digestParts pk sig.randomness msg).forsAdrs :
          OracleComp (publicHashSpec prims.core) prims.Y) ++
      col_calls (GeneralHypertree.pkFromSigM vp prims.core
        (forsPkFromSig prims sig.fors (digestParts pk sig.randomness msg).md.toList
          pk.pkSeed (digestParts pk sig.randomness msg).forsAdrs)
        sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg) :
          OracleComp (publicHashSpec prims.core) prims.Y) := by
  have e1 : simulateQ (col_logImpl prims) (forsPkFromSigM prims.core sig.fors
        (digestParts pk sig.randomness msg).md.toList pk.pkSeed
        (digestParts pk sig.randomness msg).forsAdrs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      forsPkFromSigWith prims.core
        (fun a x => logTh (prims := prims) pk.pkSeed (prims.adrsToKey a) [x])
        (fun a l r => logTh (prims := prims) pk.pkSeed (prims.adrsToKey a) [l, r])
        (fun a xs => logTh (prims := prims) pk.pkSeed (prims.adrsToKey a) xs)
        sig.fors (digestParts pk sig.randomness msg).md.toList
        (digestParts pk sig.randomness msg).forsAdrs :=
    @forsPkFromSigM_natural _ prims.core _ _ _ _ _ _ _ (col_hasQuery prims) (col_hom prims)
      sig.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
      (digestParts pk sig.randomness msg).forsAdrs
  have e2 : ∀ m0 : prims.Y, simulateQ (col_logImpl prims)
        (GeneralHypertree.pkFromSigM vp prims.core m0 sig.hypertree pk.pkSeed
          (digestParts pk sig.randomness msg) :
            OracleComp (publicHashSpec prims.core) prims.Y) =
      GeneralHypertree.pkFromSigWith vp prims.core
        (fun a x => logTh (prims := prims) pk.pkSeed (prims.adrsToKey a) [x])
        (fun a xs => logTh (prims := prims) pk.pkSeed (prims.adrsToKey a) xs)
        (fun a l r => logTh (prims := prims) pk.pkSeed (prims.adrsToKey a) [l, r])
        m0 sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg) := fun m0 =>
    @GeneralHypertree.pkFromSigM_natural vp prims.core _ _ _ _ _ _ _ (col_hasQuery prims)
      (col_hom prims) m0 sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg)
  refine Eq.trans ?_ (col_calls_bind (forsPkFromSigM prims.core sig.fors
        (digestParts pk sig.randomness msg).md.toList pk.pkSeed
        (digestParts pk sig.randomness msg).forsAdrs :
          OracleComp (publicHashSpec prims.core) prims.Y) (fun m0 => (GeneralHypertree.pkFromSigM vp prims.core m0
    sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg) :
      OracleComp (publicHashSpec prims.core) prims.Y)))
  unfold verifyCalls col_calls
  rw [simulateQ_bind, e1]
  simp only [e2]

/-! ## Collisions between two logs -/

/-- Two logs contain calls at the same tweak with different inputs and equal `Thash` value. -/
def col_Coll (pk : prims.PkSeed) (L L' : List (prims.AdrsKey × List prims.Y)) : Prop :=
  ∃ c ∈ L, ∃ c' ∈ L', c.1 = c'.1 ∧ c.2 ≠ c'.2 ∧ prims.Thash pk c.1 c.2 = prims.Thash pk c'.1 c'.2

theorem col_Coll.mono {pk : prims.PkSeed} {L L' M M' : List (prims.AdrsKey × List prims.Y)}
    (h : col_Coll pk L L') (h1 : ∀ c ∈ L, c ∈ M) (h2 : ∀ c ∈ L', c ∈ M') : col_Coll pk M M' := by
  obtain ⟨c, hc, c', hc', h⟩ := h
  exact ⟨c, h1 c hc, c', h2 c' hc', h⟩

theorem col_sim_bind {α β : Type} (oa : OracleComp (publicHashSpec prims.core) α)
    (f : α → OracleComp (publicHashSpec prims.core) β) :
    simulateQ (PublicHash.impl prims) (oa >>= f) =
      simulateQ (PublicHash.impl prims) (f (simulateQ (PublicHash.impl prims) oa)) := by
  rw [simulateQ_bind]; rfl

/-- Two climbs at the same index from different nodes to the same root collide. -/
theorem col_climb_collision (pk : prims.PkSeed) :
    ∀ (auth1 auth2 : List prims.Y), auth1.length = auth2.length →
    ∀ (nodeAdr : ℕ → ℕ → Adrs) (idx : ℕ) (n1 n2 : prims.Y), n1 ≠ n2 →
    simulateQ (PublicHash.impl prims)
        (PerfectMerkleTree.climbM (fun z t l r => PublicHash.h prims.core pk (nodeAdr z t) l r)
          idx n1 auth1 : OracleComp (publicHashSpec prims.core) prims.Y) =
      simulateQ (PublicHash.impl prims)
        (PerfectMerkleTree.climbM (fun z t l r => PublicHash.h prims.core pk (nodeAdr z t) l r)
          idx n2 auth2 : OracleComp (publicHashSpec prims.core) prims.Y) →
    col_Coll pk
      (col_calls (PerfectMerkleTree.climbM
        (fun z t l r => PublicHash.h prims.core pk (nodeAdr z t) l r) idx n1 auth1 :
          OracleComp (publicHashSpec prims.core) prims.Y))
      (col_calls (PerfectMerkleTree.climbM
        (fun z t l r => PublicHash.h prims.core pk (nodeAdr z t) l r) idx n2 auth2 :
          OracleComp (publicHashSpec prims.core) prims.Y)) := by
  intro auth1
  induction auth1 with
  | nil =>
    intro auth2 hlen nodeAdr idx n1 n2 hne h
    obtain rfl : auth2 = [] := List.length_eq_zero_iff.mp hlen.symm
    exact absurd h hne
  | cons a1 r1 ih =>
    intro auth2 hlen nodeAdr idx n1 n2 hne h
    obtain ⟨a2, r2, rfl⟩ : ∃ a2 r2, auth2 = a2 :: r2 := by
      cases auth2 with
      | nil => simp at hlen
      | cons a2 r2 => exact ⟨a2, r2, rfl⟩
    have hlen' : r1.length = r2.length := by simpa using hlen
    rw [PerfectMerkleTree.climbM_cons, PerfectMerkleTree.climbM_cons] at h ⊢
    rw [col_sim_bind, col_sim_bind] at h
    by_cases hpar : idx % 2 = 0
    · simp only [hpar, ite_true] at h ⊢
      rw [PublicHash.simulateQ_h, PublicHash.simulateQ_h] at h
      by_cases hp : prims.H pk (nodeAdr 1 (idx / 2)) n1 a1 = prims.H pk (nodeAdr 1 (idx / 2)) n2 a2
      · refine ⟨(prims.adrsToKey (nodeAdr 1 (idx / 2)), [n1, a1]),
          col_mem_bind_left _ (by rw [col_calls_h]; exact List.mem_singleton_self _),
          (prims.adrsToKey (nodeAdr 1 (idx / 2)), [n2, a2]),
          col_mem_bind_left _ (by rw [col_calls_h]; exact List.mem_singleton_self _),
          rfl, ?_, hp⟩
        intro heq
        exact hne (List.cons.inj heq).1
      · refine (ih r2 hlen' (fun z t => nodeAdr (z + 1) t) (idx / 2) _ _ hp h).mono ?_ ?_
        · intro c hc
          refine col_mem_bind_right _ ?_
          rw [PublicHash.simulateQ_h]; exact hc
        · intro c hc
          refine col_mem_bind_right _ ?_
          rw [PublicHash.simulateQ_h]; exact hc
    · simp only [hpar, ite_false] at h ⊢
      rw [PublicHash.simulateQ_h, PublicHash.simulateQ_h] at h
      by_cases hp : prims.H pk (nodeAdr 1 (idx / 2)) a1 n1 = prims.H pk (nodeAdr 1 (idx / 2)) a2 n2
      · refine ⟨(prims.adrsToKey (nodeAdr 1 (idx / 2)), [a1, n1]),
          col_mem_bind_left _ (by rw [col_calls_h]; exact List.mem_singleton_self _),
          (prims.adrsToKey (nodeAdr 1 (idx / 2)), [a2, n2]),
          col_mem_bind_left _ (by rw [col_calls_h]; exact List.mem_singleton_self _),
          rfl, ?_, hp⟩
        intro heq
        exact hne (List.cons.inj (List.cons.inj heq).2).1
      · refine (ih r2 hlen' (fun z t => nodeAdr (z + 1) t) (idx / 2) _ _ hp h).mono ?_ ?_
        · intro c hc
          refine col_mem_bind_right _ ?_
          rw [PublicHash.simulateQ_h]; exact hc
        · intro c hc
          refine col_mem_bind_right _ ?_
          rw [PublicHash.simulateQ_h]; exact hc

/-! ## FORS -/

/-- Two FORS signatures recovering the same public key while some tree's leaf images differ
collide (at the `T_k` compression or at an `H` node of that tree). -/
theorem col_fors_collision (pk : prims.PkSeed) (s1 s2 : ForsSigCore vp.params prims.core)
    (md : List Byte) (adrs : Adrs) (i : Fin vp.params.k)
    (hleaf : prims.F pk (forsNodeAdrs adrs 0 (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val))
        (s1[i.val]).sk ≠
      prims.F pk (forsNodeAdrs adrs 0 (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val))
        (s2[i.val]).sk)
    (hpk : forsPkFromSig prims s1 md pk adrs = forsPkFromSig prims s2 md pk adrs) :
    col_Coll pk
      (col_calls (forsPkFromSigM prims.core s1 md pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y))
      (col_calls (forsPkFromSigM prims.core s2 md pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y)) := by
  -- the per-tree program
  let tree : ForsSigCore vp.params prims.core → Fin vp.params.k →
      OracleComp (publicHashSpec prims.core) prims.Y := fun s i => do
    let leaf ← PublicHash.f prims.core pk
      (forsNodeAdrs adrs 0 (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)) (s[i.val]).sk
    PerfectMerkleTree.climbM (forsNodeHashWith (PublicHash.h prims.core pk) adrs)
      (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) leaf (s[i.val]).auth.toList
  have hprog : ∀ s : ForsSigCore vp.params prims.core,
      (forsPkFromSigM prims.core s md pk adrs : OracleComp (publicHashSpec prims.core) prims.Y) =
        Vector.ofFnM (tree s) >>= fun roots =>
          PublicHash.tl prims.core pk (forsPkAdrs adrs) roots.toList := fun s => rfl
  have hval : ∀ s : ForsSigCore vp.params prims.core, forsPkFromSig prims s md pk adrs =
      prims.Tl pk (forsPkAdrs adrs)
        (simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s))).toList := by
    intro s
    show simulateQ (PublicHash.impl prims) (forsPkFromSigM prims.core s md pk adrs :
      OracleComp (publicHashSpec prims.core) prims.Y) = _
    rw [hprog, col_sim_bind, PublicHash.simulateQ_tl]
  rw [hprog s1, hprog s2]
  rw [hval s1, hval s2] at hpk
  by_cases hroots : (simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s1))).toList =
      (simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s2))).toList
  · -- equal roots: climb collision in tree `i`
    have hvec : simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s1)) =
        simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s2)) := Vector.toList_inj.mp hroots
    rw [simulateQ_ofFnM, simulateQ_ofFnM] at hvec
    have hi : simulateQ (PublicHash.impl prims) (tree s1 i) =
        simulateQ (PublicHash.impl prims) (tree s2 i) := by
      have h1 := congrArg (fun v : Vector prims.Y vp.params.k => v[i.val]) hvec
      have e : ∀ g : Fin vp.params.k → Id prims.Y,
          (Vector.ofFnM g : Id (Vector prims.Y vp.params.k)) = Vector.ofFn g := fun g =>
        Vector.idRun_ofFnM
      simp only [e] at h1
      simpa using h1
    have htree : ∀ s : ForsSigCore vp.params prims.core,
        simulateQ (PublicHash.impl prims) (tree s i) =
          simulateQ (PublicHash.impl prims)
            (PerfectMerkleTree.climbM
              (fun z t l r => PublicHash.h prims.core pk (forsNodeAdrs adrs z t) l r)
              (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)
              (prims.F pk (forsNodeAdrs adrs 0
                (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)) (s[i.val]).sk)
              (s[i.val]).auth.toList : OracleComp (publicHashSpec prims.core) prims.Y) := by
      intro s
      show simulateQ (PublicHash.impl prims) (_ >>= _) = _
      rw [col_sim_bind, PublicHash.simulateQ_f]
      rfl
    rw [htree s1, htree s2] at hi
    refine (col_climb_collision pk _ _ (by simp) _ _ _ _ hleaf hi).mono ?_ ?_
    · intro c hc
      refine col_mem_bind_left _ (col_mem_ofFnM (tree s1) i ?_)
      refine col_mem_bind_right _ ?_
      rw [PublicHash.simulateQ_f]; exact hc
    · intro c hc
      refine col_mem_bind_left _ (col_mem_ofFnM (tree s2) i ?_)
      refine col_mem_bind_right _ ?_
      rw [PublicHash.simulateQ_f]; exact hc
  · -- different roots: `T_k` collision
    refine ⟨(prims.adrsToKey (forsPkAdrs adrs),
        (simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s1))).toList),
      col_mem_bind_right _ (by rw [col_calls_tl]; exact List.mem_singleton_self _),
      (prims.adrsToKey (forsPkAdrs adrs),
        (simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s2))).toList),
      col_mem_bind_right _ (by rw [col_calls_tl]; exact List.mem_singleton_self _),
      rfl, hroots, hpk⟩

/-! ## XMSS -/

/-- Two XMSS signatures at the same leaf recovering the same root from different WOTS+ chain
ends collide (at the `T_len` compression or at an `H` node of the tree). -/
theorem col_xmss_collision (pk : prims.PkSeed) (idx : ℕ)
    (g1 g2 : XmssSig vp.params prims.core) (m1 m2 : prims.Y) (adrs : Adrs)
    (htops : wotsPkFromSigTops prims g1.wots m1 pk (wotsLeafAdrs adrs idx) ≠
      wotsPkFromSigTops prims g2.wots m2 pk (wotsLeafAdrs adrs idx))
    (hroot : xmssPkFromSig prims idx g1 m1 pk adrs = xmssPkFromSig prims idx g2 m2 pk adrs) :
    col_Coll pk
      (col_calls (xmssPkFromSigM prims.core idx g1 m1 pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y))
      (col_calls (xmssPkFromSigM prims.core idx g2 m2 pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y)) := by
  have hprog : ∀ (g : XmssSig vp.params prims.core) (m : prims.Y),
      (xmssPkFromSigM prims.core idx g m pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y) =
      ((wotsPkFromSigTopsM prims.core g.wots m pk (wotsLeafAdrs adrs idx) :
          OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len)) >>= fun tops =>
        PublicHash.tl prims.core pk (wotsPkAdrs (wotsLeafAdrs adrs idx)) tops.toList) >>=
      fun leaf => PerfectMerkleTree.climbM
        (fun z t l r => PublicHash.h prims.core pk (xmssNodeAdrs adrs z t) l r) idx leaf
        g.auth.toList := fun g m => rfl
  have hleaf : ∀ (g : XmssSig vp.params prims.core) (m : prims.Y),
      simulateQ (PublicHash.impl prims)
        ((wotsPkFromSigTopsM prims.core g.wots m pk (wotsLeafAdrs adrs idx) :
          OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len)) >>= fun tops =>
        PublicHash.tl prims.core pk (wotsPkAdrs (wotsLeafAdrs adrs idx)) tops.toList) =
      prims.Tl pk (wotsPkAdrs (wotsLeafAdrs adrs idx))
        (wotsPkFromSigTops prims g.wots m pk (wotsLeafAdrs adrs idx)).toList := by
    intro g m
    rw [col_sim_bind, PublicHash.simulateQ_tl]
    rfl
  have hval : ∀ (g : XmssSig vp.params prims.core) (m : prims.Y),
      xmssPkFromSig prims idx g m pk adrs =
        simulateQ (PublicHash.impl prims)
          (PerfectMerkleTree.climbM
            (fun z t l r => PublicHash.h prims.core pk (xmssNodeAdrs adrs z t) l r) idx
            (prims.Tl pk (wotsPkAdrs (wotsLeafAdrs adrs idx))
              (wotsPkFromSigTops prims g.wots m pk (wotsLeafAdrs adrs idx)).toList)
            g.auth.toList : OracleComp (publicHashSpec prims.core) prims.Y) := by
    intro g m
    show simulateQ (PublicHash.impl prims) (xmssPkFromSigM prims.core idx g m pk adrs :
      OracleComp (publicHashSpec prims.core) prims.Y) = _
    rw [hprog, col_sim_bind, hleaf]
  rw [hprog g1 m1, hprog g2 m2]
  rw [hval g1 m1, hval g2 m2] at hroot
  have hlist : (wotsPkFromSigTops prims g1.wots m1 pk (wotsLeafAdrs adrs idx)).toList ≠
      (wotsPkFromSigTops prims g2.wots m2 pk (wotsLeafAdrs adrs idx)).toList :=
    fun h => htops (Vector.toList_inj.mp h)
  by_cases hl : prims.Tl pk (wotsPkAdrs (wotsLeafAdrs adrs idx))
        (wotsPkFromSigTops prims g1.wots m1 pk (wotsLeafAdrs adrs idx)).toList =
      prims.Tl pk (wotsPkAdrs (wotsLeafAdrs adrs idx))
        (wotsPkFromSigTops prims g2.wots m2 pk (wotsLeafAdrs adrs idx)).toList
  · refine ⟨(prims.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs idx)),
        (wotsPkFromSigTops prims g1.wots m1 pk (wotsLeafAdrs adrs idx)).toList),
      col_mem_bind_left _ (col_mem_bind_right _
        (by rw [col_calls_tl]; exact List.mem_singleton_self _)),
      (prims.adrsToKey (wotsPkAdrs (wotsLeafAdrs adrs idx)),
        (wotsPkFromSigTops prims g2.wots m2 pk (wotsLeafAdrs adrs idx)).toList),
      col_mem_bind_left _ (col_mem_bind_right _
        (by rw [col_calls_tl]; exact List.mem_singleton_self _)),
      rfl, hlist, hl⟩
  · refine (col_climb_collision pk _ _ (by simp) _ _ _ _ hl hroot).mono ?_ ?_
    · intro c hc
      refine col_mem_bind_right _ ?_
      rw [hleaf]; exact hc
    · intro c hc
      refine col_mem_bind_right _ ?_
      rw [hleaf]; exact hc

/-! ## Hypertree -/

/-- The XMSS recovery program of layer `j` on the path of `parts`. -/
def col_layerProg (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (j : Fin vp.params.d) :
    OracleComp (publicHashSpec prims.core) prims.Y :=
  xmssPkFromSigM prims.core (LayerPosition.atLayer vp parts j).leaf.val s[j.val]
    (layerMsg pkSeed parts s m0 j.val) pkSeed (LayerPosition.atLayer vp parts j).toAdrs

theorem col_getElem_tail {α : Type} {n : ℕ} (v : Vector α (n + 1)) (i : ℕ) (hi : i < n) :
    v.tail[i] = v[i + 1] := by
  simp [Vector.tail_eq_cast_extract, Nat.add_comm]

theorem col_layerMsg_succ (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (j : Fin vp.params.d) :
    layerMsg pkSeed parts s m0 (j.val + 1) =
      simulateQ (PublicHash.impl prims) (col_layerProg pkSeed parts s m0 j) := by
  rw [layerMsg, dite_eq_left_of_eq_true (eq_true j.isLt)]
  rfl

/-- The recovery loop from layer `j` computes `layerMsg … d` and makes all the calls of the
layer programs `≥ j`. -/
theorem col_recover (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) :
    ∀ (layers : ℕ) (j : Fin vp.params.d) (pos : LayerPosition vp)
      (hpos : pos = LayerPosition.atLayer vp parts j)
      (hrem : pos.layer.val + layers = vp.params.d)
      (sigs : Vector (XmssSig vp.params prims.core) layers)
      (hs : ∀ (i : ℕ) (hi : i < layers), sigs[i] = s[j.val + i]'(by
        have := j.isLt; subst hpos; simp at hrem; omega)),
      simulateQ (PublicHash.impl prims)
          (GeneralHypertree.recoverFromPositionM vp prims.core pkSeed pos layers hrem
            (layerMsg pkSeed parts s m0 j.val) sigs :
              OracleComp (publicHashSpec prims.core) prims.Y) =
        layerMsg pkSeed parts s m0 vp.params.d ∧
      ∀ (j' : Fin vp.params.d), j.val ≤ j'.val →
        ∀ c ∈ col_calls (col_layerProg pkSeed parts s m0 j'),
          c ∈ col_calls (GeneralHypertree.recoverFromPositionM vp prims.core pkSeed pos layers
            hrem (layerMsg pkSeed parts s m0 j.val) sigs :
              OracleComp (publicHashSpec prims.core) prims.Y) := by
  intro layers
  induction layers using Nat.twoStepInduction with
  | zero =>
    intro j pos hpos hrem
    have := pos.layer.isLt
    omega
  | one =>
    intro j pos hpos hrem sigs hs
    subst hpos
    have hjd : j.val + 1 = vp.params.d := by simpa using hrem
    have h0 : sigs.head = s[j.val] := by
      have := hs 0 (by omega)
      simpa [Vector.head] using this
    have hprog : (GeneralHypertree.recoverFromPositionM vp prims.core pkSeed
        (LayerPosition.atLayer vp parts j) 1 hrem (layerMsg pkSeed parts s m0 j.val) sigs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
        col_layerProg pkSeed parts s m0 j := by
      unfold col_layerProg
      rw [← h0]
      rfl
    rw [hprog]
    refine ⟨?_, ?_⟩
    · rw [← col_layerMsg_succ]
      exact congrArg _ hjd
    · intro j' hj' c hc
      have : j' = j := Fin.ext (by have := j'.isLt; omega)
      subst this
      exact hc
  | more layers _ ih =>
    intro j pos hpos hrem sigs hs
    subst hpos
    have hsum : j.val + (layers + 2) = vp.params.d := by simpa using hrem
    have hjd : j.val + 1 < vp.params.d := by omega
    have h0 : sigs.head = s[j.val] := by
      have := hs 0 (by omega)
      simpa [Vector.head] using this
    have hnext : (LayerPosition.atLayer vp parts j).next (by simpa using hjd) =
        LayerPosition.atLayer vp parts ⟨j.val + 1, hjd⟩ :=
      (LayerPosition.atLayer_succ_eq_next vp parts j hjd).symm
    have hprog : (GeneralHypertree.recoverFromPositionM vp prims.core pkSeed
        (LayerPosition.atLayer vp parts j) (layers + 2) hrem
        (layerMsg pkSeed parts s m0 j.val) sigs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
        col_layerProg pkSeed parts s m0 j >>= fun root =>
          GeneralHypertree.recoverFromPositionM vp prims.core pkSeed
            ((LayerPosition.atLayer vp parts j).next (by simpa using hjd)) (layers + 1)
            (by simp only [LayerPosition.next_layer_val, LayerPosition.atLayer_layer_val]; omega)
            root sigs.tail := by
      unfold col_layerProg
      rw [← h0]
      rfl
    have hs' : ∀ (i : ℕ) (hi : i < layers + 1),
        sigs.tail[i] = s[j.val + 1 + i]'(by omega) := by
      intro i hi
      have := hs (i + 1) (by omega)
      rw [col_getElem_tail, this]
      congr 1
      omega
    obtain ⟨ihv, ihc⟩ := ih ⟨j.val + 1, hjd⟩ _ hnext
      (by simp only [LayerPosition.next_layer_val, LayerPosition.atLayer_layer_val]; omega)
      sigs.tail hs'
    rw [hprog]
    refine ⟨?_, ?_⟩
    · rw [col_sim_bind, ← col_layerMsg_succ]
      exact ihv
    · intro j' hj' c hc
      by_cases hjj : j' = j
      · subst hjj
        exact col_mem_bind_left _ hc
      · refine col_mem_bind_right _ ?_
        rw [← col_layerMsg_succ]
        refine ihc j' ?_ c hc
        have : j.val ≠ j'.val := fun h => hjj (Fin.ext h.symm)
        show j.val + 1 ≤ j'.val
        omega

theorem col_pkFromSig (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) :
    GeneralHypertree.pkFromSig vp prims m0 s pkSeed parts =
        layerMsg pkSeed parts s m0 vp.params.d ∧
      ∀ (j : Fin vp.params.d), ∀ c ∈ col_calls (col_layerProg pkSeed parts s m0 j),
        c ∈ col_calls (GeneralHypertree.pkFromSigM vp prims.core m0 s pkSeed parts :
          OracleComp (publicHashSpec prims.core) prims.Y) := by
  obtain ⟨hv, hc⟩ := col_recover pkSeed parts s m0 vp.params.d ⟨0, vp.valid.d_pos⟩
    (LayerPosition.initial vp parts) (LayerPosition.atLayer_zero_eq_initial vp parts).symm
    (by simp) s (fun i hi => by simp)
  exact ⟨hv, fun j c hcj => hc j (Nat.zero_le _) c hcj⟩

/-- The first layer where two message sequences meet. -/
theorem col_meet {α : Type} (F H : ℕ → α) (d : ℕ) (h0 : F 0 ≠ H 0) (hd : F d = H d) :
    ∃ j, j < d ∧ F j ≠ H j ∧ F (j + 1) = H (j + 1) := by
  induction d with
  | zero => exact absurd hd h0
  | succ d ih =>
    by_cases h : F d = H d
    · obtain ⟨j, hj, h1, h2⟩ := ih h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨d, by omega, h, hd⟩

/-! ## The two-signature comparison, for arbitrary signatures -/

section Classify

variable [DecidableEq prims.Y]

/-- Two signatures on the same digest that recover the same root, where the comparison of the
first against the second is of class `tcr`, verify through colliding calls. -/
theorem col_collision_of_classify (pk : PublicKeyCore prims.core)
    (signed : List (List Byte × prims.Y)) (msg : List Byte)
    (forged ref : GeneralScheme.SignatureCore vp prims.core)
    (hR : ref.randomness = forged.randomness)
    (hroot : GeneralHypertree.pkFromSig vp prims
        (forsPkFromSig prims forged.fors (digestParts pk forged.randomness msg).md.toList pk.pkSeed
          (digestParts pk forged.randomness msg).forsAdrs)
        forged.hypertree pk.pkSeed (digestParts pk forged.randomness msg) =
      GeneralHypertree.pkFromSig vp prims
        (forsPkFromSig prims ref.fors (digestParts pk forged.randomness msg).md.toList pk.pkSeed
          (digestParts pk forged.randomness msg).forsAdrs)
        ref.hypertree pk.pkSeed (digestParts pk forged.randomness msg))
    (hclass : classify pk signed msg forged ref = .tcr) :
    col_Coll pk.pkSeed (verifyCalls pk msg forged) (verifyCalls pk msg ref) := by
  rw [col_verifyCalls_eq, col_verifyCalls_eq, hR]
  generalize hparts : digestParts pk forged.randomness msg = parts at hroot ⊢
  -- unpack the class
  unfold classify at hclass
  simp only [hparts] at hclass
  split_ifs at hclass with hitsr hwots hopen
  rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hwots hopen
  by_cases h0 : forsPkFromSig prims forged.fors parts.md.toList pk.pkSeed parts.forsAdrs =
      forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs
  · -- FORS branch
    push Not at hitsr
    obtain ⟨x, hx, hxo⟩ := hitsr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hik : i < vp.params.k := List.mem_range.mp hi
    have hnone := List.find?_eq_none.mp hopen ⟨i, hik⟩ (List.mem_finRange _)
    have hleaf : prims.F pk.pkSeed (forsNodeAdrs parts.forsAdrs 0
          (i * 2 ^ vp.params.a + forsIdx vp.params parts.md.toList i)) (forged.fors[i]).sk ≠
        prims.F pk.pkSeed (forsNodeAdrs parts.forsAdrs 0
          (i * 2 ^ vp.params.a + forsIdx vp.params parts.md.toList i)) (ref.fors[i]).sk := by
      intro heq
      apply hnone
      exact decide_eq_true ⟨hxo, heq⟩
    exact (col_fors_collision pk.pkSeed forged.fors ref.fors parts.md.toList parts.forsAdrs
      ⟨i, hik⟩ hleaf h0).mono (fun c hc => List.mem_append_left _ hc)
      (fun c hc => List.mem_append_left _ hc)
  · -- hypertree branch
    obtain ⟨hF, hcF⟩ := col_pkFromSig pk.pkSeed parts forged.hypertree
      (forsPkFromSig prims forged.fors parts.md.toList pk.pkSeed parts.forsAdrs)
    obtain ⟨hH, hcH⟩ := col_pkFromSig pk.pkSeed parts ref.hypertree
      (forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs)
    rw [hF, hH] at hroot
    obtain ⟨j, hj, hne, heq⟩ := col_meet
      (layerMsg pk.pkSeed parts forged.hypertree
        (forsPkFromSig prims forged.fors parts.md.toList pk.pkSeed parts.forsAdrs))
      (layerMsg pk.pkSeed parts ref.hypertree
        (forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs))
      vp.params.d h0 hroot
    have hnone := List.find?_eq_none.mp hwots ⟨j, hj⟩ (List.mem_finRange _)
    have htops : layerTops pk.pkSeed parts forged.hypertree
          (forsPkFromSig prims forged.fors parts.md.toList pk.pkSeed parts.forsAdrs) ⟨j, hj⟩ ≠
        layerTops pk.pkSeed parts ref.hypertree
          (forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs) ⟨j, hj⟩ := by
      intro h
      apply hnone
      exact decide_eq_true ⟨hne, h⟩
    have hsucc := heq
    rw [col_layerMsg_succ pk.pkSeed parts _ _ ⟨j, hj⟩,
      col_layerMsg_succ pk.pkSeed parts _ _ ⟨j, hj⟩] at hsucc
    exact (col_xmss_collision pk.pkSeed _ _ _ _ _ _ htops hsucc).mono
      (fun c hc => List.mem_append_right _ (hcF ⟨j, hj⟩ c hc))
      (fun c hc => List.mem_append_right _ (hcH ⟨j, hj⟩ c hc))

end Classify

/-! ## Correctness over an arbitrary pure secret provider -/

theorem col_wotsSign_val (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsSignWithSecret prims.core (PublicHash.f prims.core pk) (fun a => pure (sec a)) msg adrs :
          OracleComp (publicHashSpec prims.core) (WotsSig vp.params prims.core)) =
      Vector.ofFn fun i : Fin vp.params.len =>
        chain prims pk (wotsChainAdrs adrs i.val) (sec (wotsSkAdrs adrs i.val)) 0
          (chainStepsCore prims.core msg i.val) := by
  unfold wotsSignWithSecret
  rw [simulateQ_ofFnM]
  simp only [pure_bind]
  exact Vector.idRun_ofFnM

theorem col_wotsTops_val (sec : Adrs → prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkGenTopsWithSecret prims.core (PublicHash.f prims.core pk) (fun a => pure (sec a)) adrs :
          OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len)) =
      Vector.ofFn fun i : Fin vp.params.len =>
        chain prims pk (wotsChainAdrs adrs i.val) (sec (wotsSkAdrs adrs i.val)) 0
          (vp.params.w - 1) := by
  unfold wotsPkGenTopsWithSecret
  rw [simulateQ_ofFnM]
  simp only [pure_bind]
  exact Vector.idRun_ofFnM

theorem col_wots_correct (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y)
    (adrs : Adrs) :
    wotsPkFromSig prims
        (simulateQ (PublicHash.impl prims)
          (wotsSignWithSecret prims.core (PublicHash.f prims.core pk) (fun a => pure (sec a))
            msg adrs : OracleComp (publicHashSpec prims.core) (WotsSig vp.params prims.core)))
        msg pk adrs =
      simulateQ (PublicHash.impl prims)
        (wotsPkGenWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
          (fun a => pure (sec a)) adrs : OracleComp (publicHashSpec prims.core) prims.Y) := by
  rw [wotsPkFromSig_eq_tl]
  unfold wotsPkGenWithSecret
  rw [col_sim_bind, PublicHash.simulateQ_tl, col_wotsTops_val, col_wotsSign_val]
  congr 2
  apply Vector.ext
  intro i hi
  simp only [wotsPkFromSigTops_eq_ofFn, Vector.getElem_ofFn]
  have hc := chain_compose prims pk (wotsChainAdrs adrs i)
    (sec (wotsSkAdrs adrs i)) 0 (chainStepsCore prims.core msg i)
    (vp.params.w - 1 - chainStepsCore prims.core msg i)
  rw [Nat.zero_add] at hc
  rw [hc, Nat.add_sub_cancel' (chainStepsCore_le prims.core msg i)]

theorem col_xmss_correct (sec : Adrs → prims.Y) (pk : prims.PkSeed) (msg : prims.Y)
    (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ vp.params.hp) :
    xmssPkFromSig prims idx
        (simulateQ (PublicHash.impl prims)
          (xmssSignWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
            (PublicHash.h prims.core pk) (fun a => pure (sec a)) msg adrs idx :
              OracleComp (publicHashSpec prims.core) (XmssSig vp.params prims.core)))
        msg pk adrs =
      simulateQ (PublicHash.impl prims)
        (xmssRootWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
          (PublicHash.h prims.core pk) (fun a => pure (sec a)) adrs :
            OracleComp (publicHashSpec prims.core) prims.Y) := by
  have hsign : simulateQ (PublicHash.impl prims)
      (xmssSignWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
        (PublicHash.h prims.core pk) (fun a => pure (sec a)) msg adrs idx :
          OracleComp (publicHashSpec prims.core) (XmssSig vp.params prims.core)) =
      ⟨simulateQ (PublicHash.impl prims)
          (wotsSignWithSecret prims.core (PublicHash.f prims.core pk) (fun a => pure (sec a))
            msg (wotsLeafAdrs adrs idx) :
              OracleComp (publicHashSpec prims.core) (WotsSig vp.params prims.core)),
        PerfectMerkleTree.intrinsicAuthPath
          (fun t => simulateQ (PublicHash.impl prims)
            (xmssLeafWithSecret prims.core (PublicHash.f prims.core pk)
              (PublicHash.tl prims.core pk) (fun a => pure (sec a)) adrs t :
                OracleComp (publicHashSpec prims.core) prims.Y))
          (xmssNodeHash prims pk adrs) idx vp.params.hp⟩ := by
    unfold xmssSignWithSecret
    simp only [simulateQ_bind, simulateQ_pure]
    rw [PerfectMerkleTree.simulateQ_intrinsicAuthPathM]
    rfl
  rw [hsign, xmssPkFromSig_eq_climb]
  dsimp only
  rw [col_wots_correct]
  unfold xmssRootWithSecret xmssNodeWithSecret
  rw [PerfectMerkleTree.simulateQ_merkleRootM]
  have key := PerfectMerkleTree.climb_authPath
    (fun t => simulateQ (PublicHash.impl prims)
      (xmssLeafWithSecret prims.core (PublicHash.f prims.core pk)
        (PublicHash.tl prims.core pk) (fun a => pure (sec a)) adrs t :
          OracleComp (publicHashSpec prims.core) prims.Y))
    (xmssNodeHash prims pk adrs) idx vp.params.hp
  rw [Nat.div_eq_of_lt hidx] at key
  rw [PerfectMerkleTree.intrinsicAuthPath_toList]
  exact key

theorem col_head_insertIdx_zero {X : Type} {n : ℕ} (rest : Vector X n) (x : X) :
    (rest.insertIdx 0 x).head = x := by
  simp [Vector.head, Vector.insertIdx_zero]

theorem col_tail_insertIdx_zero {X : Type} {n : ℕ} (rest : Vector X n) (x : X) :
    (rest.insertIdx 0 x).tail = rest := by
  rw [Vector.insertIdx_zero]
  apply Vector.ext
  intro i hi
  simp [Vector.tail_eq_cast_extract]

theorem col_recover_sign (sec : Adrs → prims.Y) (pk : prims.PkSeed) :
    ∀ (layers : ℕ) (rf : Bool) (pos : LayerPosition vp)
      (hrem : pos.layer.val + layers = vp.params.d) (msg : prims.Y),
      simulateQ (PublicHash.impl prims)
        (GeneralHypertree.recoverFromPositionM vp prims.core pk pos layers hrem msg
          (simulateQ (PublicHash.impl prims)
            (GeneralHypertree.signFromPositionWithSecret prims.core (PublicHash.f prims.core pk)
              (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk) (fun a => pure (sec a))
              rf pos layers hrem msg :
                OracleComp (publicHashSpec prims.core)
                  (Vector (XmssSig vp.params prims.core) layers))) :
            OracleComp (publicHashSpec prims.core) prims.Y) =
      simulateQ (PublicHash.impl prims)
        (xmssRootWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
          (PublicHash.h prims.core pk) (fun a => pure (sec a))
          (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) :
            OracleComp (publicHashSpec prims.core) prims.Y) := by
  intro layers
  induction layers using Nat.twoStepInduction with
  | zero =>
    intro rf pos hrem
    have := pos.layer.isLt
    omega
  | one =>
    intro rf pos hrem msg
    have hsig : simulateQ (PublicHash.impl prims)
        (GeneralHypertree.signFromPositionWithSecret prims.core (PublicHash.f prims.core pk)
          (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk) (fun a => pure (sec a))
          rf pos 1 hrem msg :
            OracleComp (publicHashSpec prims.core) (Vector (XmssSig vp.params prims.core) 1)) =
        #v[simulateQ (PublicHash.impl prims)
          (xmssSignWithSecret prims.core (PublicHash.f prims.core pk) (PublicHash.tl prims.core pk)
            (PublicHash.h prims.core pk) (fun a => pure (sec a)) msg pos.toAdrs pos.leaf.val :
              OracleComp (publicHashSpec prims.core) (XmssSig vp.params prims.core))] := by
      rw [GeneralHypertree.signFromPositionWithSecret]
      cases rf <;> simp only [simulateQ_bind, simulateQ_pure, Bool.false_eq_true, ite_false,
        ite_true] <;> rfl
    rw [hsig]
    refine Eq.trans ?_ ((col_xmss_correct sec pk msg pos.toAdrs pos.leaf.val pos.leaf.isLt).trans ?_)
    · rfl
    · rw [GeneralHypertree.LayerPosition.toAdrs_eq_layerAdrs_of_isFinal pos (by omega)]
  | more layers _ ih =>
    intro rf pos hrem msg
    have hnext : pos.layer.val + 1 < vp.params.d := by omega
    have hsig : simulateQ (PublicHash.impl prims)
        (GeneralHypertree.signFromPositionWithSecret prims.core (PublicHash.f prims.core pk)
          (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk) (fun a => pure (sec a))
          rf pos (layers + 2) hrem msg :
            OracleComp (publicHashSpec prims.core)
              (Vector (XmssSig vp.params prims.core) (layers + 2))) =
        (simulateQ (PublicHash.impl prims)
          (GeneralHypertree.signFromPositionWithSecret prims.core (PublicHash.f prims.core pk)
            (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk) (fun a => pure (sec a))
            false (pos.next hnext) (layers + 1) (by simp; omega)
            (xmssPkFromSig prims pos.leaf.val
              (simulateQ (PublicHash.impl prims)
                (xmssSignWithSecret prims.core (PublicHash.f prims.core pk)
                  (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk)
                  (fun a => pure (sec a)) msg pos.toAdrs pos.leaf.val :
                    OracleComp (publicHashSpec prims.core) (XmssSig vp.params prims.core)))
              msg pk pos.toAdrs) :
            OracleComp (publicHashSpec prims.core)
              (Vector (XmssSig vp.params prims.core) (layers + 1)))).insertIdx 0
          (simulateQ (PublicHash.impl prims)
            (xmssSignWithSecret prims.core (PublicHash.f prims.core pk)
              (PublicHash.tl prims.core pk) (PublicHash.h prims.core pk)
              (fun a => pure (sec a)) msg pos.toAdrs pos.leaf.val :
                OracleComp (publicHashSpec prims.core) (XmssSig vp.params prims.core))) := by
      rw [GeneralHypertree.signFromPositionWithSecret]
      simp only [simulateQ_bind, simulateQ_pure]
      rfl
    have hrec : ∀ sigs : Vector (XmssSig vp.params prims.core) (layers + 2),
        simulateQ (PublicHash.impl prims)
          (GeneralHypertree.recoverFromPositionM vp prims.core pk pos (layers + 2) hrem msg sigs :
            OracleComp (publicHashSpec prims.core) prims.Y) =
        simulateQ (PublicHash.impl prims)
          (GeneralHypertree.recoverFromPositionM vp prims.core pk (pos.next hnext) (layers + 1)
            (by simp; omega) (xmssPkFromSig prims pos.leaf.val sigs.head msg pk pos.toAdrs)
            sigs.tail : OracleComp (publicHashSpec prims.core) prims.Y) := by
      intro sigs
      unfold GeneralHypertree.recoverFromPositionM
      rw [GeneralHypertree.recoverFromPositionWith, col_sim_bind]
      rfl
    rw [hsig, hrec, col_head_insertIdx_zero, col_tail_insertIdx_zero]
    exact ih false (pos.next hnext) _ _

/-- The reference signature, component by component. -/
theorem col_idealSign_eq (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) (msg : List Byte)
    (R : prims.Y) :
    idealSign vp prims tbl msg (idealPk vp prims tbl pkSeed) R =
      ⟨R,
        simulateQ (PublicHash.impl prims)
          (forsSignWithSecretM prims.core (fun a => pure (secretOf vp prims tbl a))
            (digestParts (idealPk vp prims tbl pkSeed) R msg).md.toList pkSeed
            (digestParts (idealPk vp prims tbl pkSeed) R msg).forsAdrs :
              OracleComp (publicHashSpec prims.core) (ForsSigCore vp.params prims.core)),
        simulateQ (PublicHash.impl prims)
          (GeneralHypertree.signWithSecretM prims.core (fun a => pure (secretOf vp prims tbl a))
            (forsPkFromSig prims
              (simulateQ (PublicHash.impl prims)
                (forsSignWithSecretM prims.core (fun a => pure (secretOf vp prims tbl a))
                  (digestParts (idealPk vp prims tbl pkSeed) R msg).md.toList pkSeed
                  (digestParts (idealPk vp prims tbl pkSeed) R msg).forsAdrs :
                    OracleComp (publicHashSpec prims.core) (ForsSigCore vp.params prims.core)))
              (digestParts (idealPk vp prims tbl pkSeed) R msg).md.toList pkSeed
              (digestParts (idealPk vp prims tbl pkSeed) R msg).forsAdrs)
            pkSeed (digestParts (idealPk vp prims tbl pkSeed) R msg) :
              OracleComp (publicHashSpec prims.core)
                (GeneralHypertree.Signature vp prims.core))⟩ := by
  unfold idealSign GeneralScheme.signInternalWithSecretRandomizerM
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

theorem col_idealSign_randomness (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed)
    (msg : List Byte) (R : prims.Y) :
    (idealSign vp prims tbl msg (idealPk vp prims tbl pkSeed) R).randomness = R := by
  rw [col_idealSign_eq]

/-! ## The two goals -/

section Goals

variable [DecidableEq prims.Y]

/-- Correctness over a table: the reference signature verifies under the table's key. -/
theorem col_verifyInternal_idealSign (_hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (msg : List Byte) (R : prims.Y) :
    GeneralScheme.verifyInternal vp prims msg
      (idealSign vp prims tbl msg (idealPk vp prims tbl pkSeed) R)
      (idealPk vp prims tbl pkSeed) = true := by
  rw [GeneralScheme.verifyInternal_eq_decide, col_idealSign_eq]
  refine decide_eq_true ?_
  exact col_recover_sign (secretOf vp prims tbl) pkSeed vp.params.d _ _ _ _

/-- Two-signature comparison. -/
theorem col_verifyCalls_collision_of_tcr (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (log : G2Log prims) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core)
    (hvalid : g2Valid (idealPk vp prims tbl pkSeed) log msg sig = true)
    (hclass : g2ClassOf tbl (idealPk vp prims tbl pkSeed) log msg sig = .tcr) :
    ∃ c ∈ verifyCalls (idealPk vp prims tbl pkSeed) msg sig,
      ∃ c' ∈ verifyCalls (idealPk vp prims tbl pkSeed) msg
          (idealSign vp prims tbl msg (idealPk vp prims tbl pkSeed) sig.randomness),
        c.1 = c'.1 ∧ c.2 ≠ c'.2 ∧
          prims.Thash pkSeed c.1 c.2 = prims.Thash pkSeed c'.1 c'.2 := by
  have hR := col_idealSign_randomness tbl pkSeed msg sig.randomness
  have hv : GeneralScheme.verifyInternal vp prims msg sig (idealPk vp prims tbl pkSeed) = true :=
    (Bool.and_eq_true_iff.mp hvalid).2
  have hv' := col_verifyInternal_idealSign hS tbl pkSeed msg sig.randomness
  rw [GeneralScheme.verifyInternal_eq_decide] at hv hv'
  have h1 := of_decide_eq_true hv
  have h2 := of_decide_eq_true hv'
  rw [hR] at h2
  exact col_collision_of_classify (idealPk vp prims tbl pkSeed) (G2Log.signed log) msg sig
    (idealSign vp prims tbl msg (idealPk vp prims tbl pkSeed) sig.randomness) hR
    (h1.trans h2.symm) hclass

end Goals

end Reduction

/-! ## Deterministic trace lemmas: honest verification inside the honest structure (`sub_*`) -/

namespace Reduction

/-! ## A writer monad for call logs -/

/-- Writer monad over call lists: a value together with the list of calls made. -/
def sub_W (C : Type) (α : Type) : Type := α × List C

namespace sub_W

variable {C : Type}

instance : Monad (sub_W C) where
  pure a := (a, [])
  bind x f := ((f x.1).1, x.2 ++ (f x.1).2)

instance : LawfulMonad (sub_W C) := LawfulMonad.mk'
  (id_map := by
    intro α x; rcases x with ⟨a, l⟩
    show (a, l ++ []) = (a, l)
    rw [List.append_nil])
  (pure_bind := by
    intro α β x f
    show ((f x).1, [] ++ (f x).2) = f x
    rfl)
  (bind_assoc := by
    intro α β γ x f g
    show ((g (f x.1).1).1, (x.2 ++ (f x.1).2) ++ (g (f x.1).1).2) =
      ((g (f x.1).1).1, x.2 ++ ((f x.1).2 ++ (g (f x.1).1).2))
    rw [List.append_assoc])

/-- The value of a writer computation. -/
def val {α : Type} (x : sub_W C α) : α := x.1
/-- The calls of a writer computation. -/
def calls {α : Type} (x : sub_W C α) : List C := x.2

@[simp] theorem val_pure {α : Type} (a : α) : val (pure a : sub_W C α) = a := rfl
@[simp] theorem calls_pure {α : Type} (a : α) : calls (pure a : sub_W C α) = [] := rfl
@[simp] theorem val_bind {α β : Type} (x : sub_W C α) (f : α → sub_W C β) :
    val (x >>= f) = val (f (val x)) := rfl
@[simp] theorem calls_bind {α β : Type} (x : sub_W C α) (f : α → sub_W C β) :
    calls (x >>= f) = calls x ++ calls (f (val x)) := rfl
@[simp] theorem val_map {α β : Type} (x : sub_W C α) (f : α → β) :
    val (f <$> x) = f (val x) := rfl
@[simp] theorem calls_map {α β : Type} (x : sub_W C α) (f : α → β) :
    calls (f <$> x) = calls x := by
  show x.2 ++ [] = x.2
  simp

/-- Embedding into the logging state monad. -/
def toState : sub_W C →ᵐ StateM (List C) where
  toFun _ x := fun s => (x.1, s ++ x.2)
  toFun_pure' a := by
    funext s
    show (a, s ++ []) = (a, s)
    rw [List.append_nil]
  toFun_bind' x f := by
    funext s
    show ((f x.1).1, s ++ (x.2 ++ (f x.1).2)) = ((f x.1).1, (s ++ x.2) ++ (f x.1).2)
    rw [List.append_assoc]

theorem toState_run {α : Type} (x : sub_W C α) (s : List C) :
    (toState x).run s = (val x, s ++ calls x) := rfl

/-- Projection to the value. -/
def toId : sub_W C →ᵐ Id where
  toFun _ x := x.1
  toFun_pure' _ := rfl
  toFun_bind' _ _ := rfl

theorem toId_eq {α : Type} (x : sub_W C α) : toId x = val x := rfl

/-! ### Generic combinators -/

theorem getElem_ofFnM {α : Type} : ∀ {k : ℕ} (f : Fin k → sub_W C α) (i : ℕ) (hi : i < k),
    (val (Vector.ofFnM f))[i] = val (f ⟨i, hi⟩)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, f, i, hi => by
    rw [Vector.ofFnM_succ]
    simp only [val_bind, val_pure]
    by_cases h : i < k
    · rw [Vector.getElem_push_lt h]
      exact getElem_ofFnM (fun j => f j.castSucc) i h
    · have : i = k := by omega
      subst this
      rw [Vector.getElem_push_eq]
      rfl

theorem mem_calls_ofFnM {α : Type} : ∀ {k : ℕ} (f : Fin k → sub_W C α) (c : C),
    c ∈ calls (Vector.ofFnM f) ↔ ∃ i, c ∈ calls (f i)
  | 0, f, c => by
    rw [Vector.ofFnM_zero]
    simp
  | k + 1, f, c => by
    rw [Vector.ofFnM_succ]
    simp only [calls_bind, calls_pure, List.append_nil, List.mem_append]
    rw [mem_calls_ofFnM (fun j => f j.castSucc) c]
    constructor
    · rintro (⟨i, hi⟩ | h)
      · exact ⟨_, hi⟩
      · exact ⟨_, h⟩
    · rintro ⟨i, hi⟩
      induction i using Fin.lastCases with
      | last => exact Or.inr hi
      | cast j => exact Or.inl ⟨j, hi⟩

theorem mem_calls_forM {α : Type} (f : α → sub_W C PUnit) (c : C) : ∀ (l : List α),
    c ∈ calls (l.forM f) ↔ ∃ x ∈ l, c ∈ calls (f x)
  | [] => by simp
  | a :: l => by
    show c ∈ calls (f a >>= fun _ => l.forM f) ↔ _
    simp only [calls_bind, List.mem_append, mem_calls_forM f c l, List.mem_cons]
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨x, Or.inr hx, h⟩
    · rintro ⟨x, rfl | hx, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, h⟩

/-! ### Merkle trees -/

open PerfectMerkleTree in
theorem length_val_authPathM {Y : Type} (leaf : ℕ → sub_W C Y) (node : ℕ → ℕ → Y → Y → sub_W C Y)
    (idx : ℕ) : ∀ z, (val (authPathM leaf node idx z)).length = z
  | 0 => rfl
  | z + 1 => by
    show (val (authPathM leaf node idx z) ++ [_]).length = z + 1
    rw [List.length_append, length_val_authPathM leaf node idx z]
    rfl

open PerfectMerkleTree in
/-- Climbing the honest authentication path from the honest leaf recomputes the honest root and
only makes calls of the honest root computation. -/
theorem merkle_spec {Y : Type} (leaf : ℕ → sub_W C Y) (node : ℕ → ℕ → Y → Y → sub_W C Y)
    (idx : ℕ) : ∀ z,
    val (climbM node idx (val (leaf idx)) (val (authPathM leaf node idx z))) =
        val (merkleRootM leaf node z (idx / 2 ^ z)) ∧
      (∀ c ∈ calls (climbM node idx (val (leaf idx)) (val (authPathM leaf node idx z))),
        c ∈ calls (merkleRootM leaf node z (idx / 2 ^ z))) ∧
      (∀ c ∈ calls (leaf idx), c ∈ calls (merkleRootM leaf node z (idx / 2 ^ z)))
  | 0 => by
    refine ⟨?_, ?_, ?_⟩
    · show val (leaf idx) = val (leaf (idx / 2 ^ 0))
      simp
    · intro c hc
      have h0 : calls (climbM node idx (val (leaf idx)) (val (authPathM leaf node idx 0))) = [] :=
        rfl
      rw [h0] at hc
      exact absurd hc (List.not_mem_nil)
    · intro c hc
      show c ∈ calls (leaf (idx / 2 ^ 0))
      simpa using hc
  | z + 1 => by
    obtain ⟨ihv, ihc, ihl⟩ := merkle_spec leaf node idx z
    have hlen := length_val_authPathM leaf node idx z
    have hpath : val (authPathM leaf node idx (z + 1)) =
        val (authPathM leaf node idx z) ++
          [val (merkleRootM leaf node z (sibling (idx / 2 ^ z)))] := rfl
    have hroot : merkleRootM leaf node (z + 1) (idx / 2 ^ (z + 1)) =
        merkleRootM leaf node z (2 * (idx / 2 ^ (z + 1))) >>= fun l =>
          merkleRootM leaf node z (2 * (idx / 2 ^ (z + 1)) + 1) >>= fun r =>
            node (z + 1) (idx / 2 ^ (z + 1)) l r := rfl
    have hdiv : idx / 2 ^ (z + 1) = idx / 2 ^ z / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [hpath, climbM_concat, hlen, hroot]
    by_cases hpar : idx / 2 ^ z % 2 = 0
    · have h2 : 2 * (idx / 2 ^ (z + 1)) = idx / 2 ^ z := by omega
      have hs : sibling (idx / 2 ^ z) = 2 * (idx / 2 ^ (z + 1)) + 1 := by
        simp only [sibling, hpar, ↓reduceIte]; omega
      simp only [hpar, ↓reduceIte]
      rw [hs, h2]
      simp only [val_bind, calls_bind, List.mem_append, ihv]
      refine ⟨trivial, ?_, ?_⟩
      · rintro c (hc | hc)
        · exact Or.inl (ihc c hc)
        · exact Or.inr (Or.inr hc)
      · intro c hc
        exact Or.inl (ihl c hc)
    · have h2 : 2 * (idx / 2 ^ (z + 1)) + 1 = idx / 2 ^ z := by omega
      have hs : sibling (idx / 2 ^ z) = 2 * (idx / 2 ^ (z + 1)) := by
        simp only [sibling, hpar, ↓reduceIte]; omega
      simp only [hpar, ↓reduceIte]
      rw [hs, h2]
      simp only [val_bind, calls_bind, List.mem_append, ihv]
      refine ⟨trivial, ?_, ?_⟩
      · rintro c (hc | hc)
        · exact Or.inr (Or.inl (ihc c hc))
        · exact Or.inr (Or.inr hc)
      · intro c hc
        exact Or.inr (Or.inl (ihl c hc))

open PerfectMerkleTree in
theorem val_intrinsicAuthPathM_toList {Y : Type} (leaf : ℕ → sub_W C Y)
    (node : ℕ → ℕ → Y → Y → sub_W C Y) (idx z : ℕ) :
    (val (intrinsicAuthPathM leaf node idx z)).toList = val (authPathM leaf node idx z) := by
  rw [← intrinsicAuthPathM_toList]
  rfl

end sub_W

/-! ## Component lemmas in the writer monad -/

section Components

open sub_W

variable {C : Type} {p : Params} (core : CorePrimitives p)
  (hash : Adrs → core.Y → sub_W C core.Y) (compress : Adrs → List core.Y → sub_W C core.Y)
  (nodeHash : Adrs → core.Y → core.Y → sub_W C core.Y) (s : Adrs → core.Y)

theorem sub_chain_spec {Y : Type} (hash : Adrs → Y → sub_W C Y) (adrs : Adrs) (x : Y) (a n : ℕ)
    (ha : a ≤ n) :
    val (chainWith hash adrs (val (chainWith hash adrs x 0 a)) a (n - a)) =
        val (chainWith hash adrs x 0 n) ∧
      ∀ c ∈ calls (chainWith hash adrs (val (chainWith hash adrs x 0 a)) a (n - a)),
        c ∈ calls (chainWith hash adrs x 0 n) := by
  have h := chainWith_add hash adrs x 0 a (n - a)
  rw [Nat.add_sub_of_le ha, Nat.zero_add] at h
  rw [h]
  simp only [val_bind, calls_bind, List.mem_append]
  exact ⟨trivial, fun c hc => Or.inr hc⟩

theorem sub_wots_sig_getElem (msg : core.Y) (adrs : Adrs) (i : ℕ) (hi : i < p.len) :
    (val (wotsSignWithSecret core hash (fun a => pure (s a)) msg adrs))[i] =
      val (chainWith hash (wotsChainAdrs adrs i) (s (wotsSkAdrs adrs i)) 0
        (chainStepsCore core msg i)) := by
  unfold wotsSignWithSecret
  rw [getElem_ofFnM _ i hi]
  rfl

theorem sub_wots_tops (msg : core.Y) (adrs : Adrs) :
    val (wotsPkFromSigTopsWith core hash
        (val (wotsSignWithSecret core hash (fun a => pure (s a)) msg adrs)) msg adrs) =
      val (wotsPkGenTopsWithSecret core hash (fun a => pure (s a)) adrs) := by
  apply Vector.ext
  intro i hi
  unfold wotsPkFromSigTopsWith wotsPkGenTopsWithSecret
  rw [getElem_ofFnM _ i hi, getElem_ofFnM _ i hi]
  show val (chainWith hash (wotsChainAdrs adrs i) _ _ _) =
    val (chainWith hash (wotsChainAdrs adrs i) (s (wotsSkAdrs adrs i)) 0 (p.w - 1))
  rw [sub_wots_sig_getElem core hash s msg adrs i hi]
  exact (sub_chain_spec hash _ _ _ _ (chainStepsCore_le core msg i)).1

theorem sub_wots_spec (msg : core.Y) (adrs : Adrs) :
    val (wotsPkFromSigWith core hash compress
        (val (wotsSignWithSecret core hash (fun a => pure (s a)) msg adrs)) msg adrs) =
        val (wotsPkGenWithSecret core hash compress (fun a => pure (s a)) adrs) ∧
      ∀ c ∈ calls (wotsPkFromSigWith core hash compress
          (val (wotsSignWithSecret core hash (fun a => pure (s a)) msg adrs)) msg adrs),
        c ∈ calls (wotsPkGenWithSecret core hash compress (fun a => pure (s a)) adrs) := by
  unfold wotsPkFromSigWith wotsPkGenWithSecret
  simp only [val_bind, calls_bind, List.mem_append, sub_wots_tops]
  refine ⟨trivial, ?_⟩
  rintro c (hc | hc)
  · left
    unfold wotsPkFromSigTopsWith at hc
    unfold wotsPkGenTopsWithSecret
    rw [mem_calls_ofFnM] at hc ⊢
    obtain ⟨i, hi⟩ := hc
    refine ⟨i, ?_⟩
    have hi' : c ∈ calls (chainWith hash (wotsChainAdrs adrs i.val)
        (val (wotsSignWithSecret core hash (fun a => pure (s a)) msg adrs))[i.val]
        (chainStepsCore core msg i.val) (p.w - 1 - chainStepsCore core msg i.val)) := hi
    rw [sub_wots_sig_getElem core hash s msg adrs i.val i.isLt] at hi'
    show c ∈ calls (chainWith hash (wotsChainAdrs adrs i.val) (s (wotsSkAdrs adrs i.val)) 0
      (p.w - 1))
    exact (sub_chain_spec hash _ _ _ _ (chainStepsCore_le core msg i.val)).2 c hi'
  · exact Or.inr hc

open PerfectMerkleTree in
theorem sub_xmss_spec (msg : core.Y) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp) :
    val (xmssPkFromSigWith core hash compress nodeHash idx
        (val (xmssSignWithSecret core hash compress nodeHash (fun a => pure (s a)) msg adrs idx))
        msg adrs) =
        val (xmssRootWithSecret core hash compress nodeHash (fun a => pure (s a)) adrs) ∧
      ∀ c ∈ calls (xmssPkFromSigWith core hash compress nodeHash idx
          (val (xmssSignWithSecret core hash compress nodeHash (fun a => pure (s a)) msg adrs
            idx)) msg adrs),
        c ∈ calls (xmssRootWithSecret core hash compress nodeHash (fun a => pure (s a)) adrs) := by
  obtain ⟨mv, mc, ml⟩ := merkle_spec
    (xmssLeafWithSecret core hash compress (fun a => pure (s a)) adrs)
    (xmssNodeHashWith nodeHash adrs) idx p.hp
  rw [Nat.div_eq_of_lt hidx] at mv mc ml
  obtain ⟨wv, wc⟩ := sub_wots_spec core hash compress s msg (wotsLeafAdrs adrs idx)
  have hauth : (val (xmssSignWithSecret core hash compress nodeHash (fun a => pure (s a)) msg
      adrs idx)).auth.toList = val (authPathM
        (xmssLeafWithSecret core hash compress (fun a => pure (s a)) adrs)
        (xmssNodeHashWith nodeHash adrs) idx p.hp) :=
    val_intrinsicAuthPathM_toList _ _ idx p.hp
  have hwots : (val (xmssSignWithSecret core hash compress nodeHash (fun a => pure (s a)) msg
      adrs idx)).wots =
      val (wotsSignWithSecret core hash (fun a => pure (s a)) msg (wotsLeafAdrs adrs idx)) := rfl
  have hroot : xmssRootWithSecret core hash compress nodeHash (fun a => pure (s a)) adrs =
      merkleRootM (xmssLeafWithSecret core hash compress (fun a => pure (s a)) adrs)
        (xmssNodeHashWith nodeHash adrs) p.hp 0 := rfl
  have hleaf : xmssLeafWithSecret core hash compress (fun a => pure (s a)) adrs idx =
      wotsPkGenWithSecret core hash compress (fun a => pure (s a)) (wotsLeafAdrs adrs idx) := rfl
  rw [hleaf] at mv mc ml
  unfold xmssPkFromSigWith
  rw [hroot, hauth, hwots]
  simp only [val_bind, calls_bind, List.mem_append, wv]
  refine ⟨mv, ?_⟩
  rintro c (hc | hc)
  · exact ml c (wc c hc)
  · exact mc c hc

theorem sub_fors_idx_div (md : List Byte) (i : ℕ) :
    (i * 2 ^ p.a + forsIdx p md i) / 2 ^ p.a = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (forsIdx_lt p md i), Nat.zero_add]

open PerfectMerkleTree in
/-- One FORS tree: recovery from the honest tree signature recomputes the honest root. -/
theorem sub_fors_tree_spec (md : List Byte) (adrs : Adrs) (i : ℕ) (hi : i < p.k) :
    val (hash (forsNodeAdrs adrs 0 (i * 2 ^ p.a + forsIdx p md i))
          ((val (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md adrs))[i]).sk >>=
        fun leaf => climbM (forsNodeHashWith nodeHash adrs) (i * 2 ^ p.a + forsIdx p md i) leaf
          ((val (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md adrs))[i]).auth.toList) =
        val (forsRootWithSecret core hash nodeHash (fun a => pure (s a)) adrs i) ∧
      ∀ c ∈ calls (hash (forsNodeAdrs adrs 0 (i * 2 ^ p.a + forsIdx p md i))
          ((val (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md adrs))[i]).sk >>=
        fun leaf => climbM (forsNodeHashWith nodeHash adrs) (i * 2 ^ p.a + forsIdx p md i) leaf
          ((val (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md adrs))[i]).auth.toList),
        c ∈ calls (forsRootWithSecret core hash nodeHash (fun a => pure (s a)) adrs i) := by
  obtain ⟨mv, mc, ml⟩ := merkle_spec
    (forsLeafWithSecret core hash (fun a => pure (s a)) adrs)
    (forsNodeHashWith nodeHash adrs) (i * 2 ^ p.a + forsIdx p md i) p.a
  rw [sub_fors_idx_div] at mv mc ml
  have hsig : (val (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md adrs))[i] =
      ⟨s (forsSkAdrs adrs (i * 2 ^ p.a + forsIdx p md i)),
        val (intrinsicAuthPathM (forsLeafWithSecret core hash (fun a => pure (s a)) adrs)
          (forsNodeHashWith nodeHash adrs) (i * 2 ^ p.a + forsIdx p md i) p.a)⟩ := by
    unfold forsSignWithSecret
    rw [getElem_ofFnM _ i hi]
    rfl
  have hleaf : forsLeafWithSecret core hash (fun a => pure (s a)) adrs
      (i * 2 ^ p.a + forsIdx p md i) =
      hash (forsNodeAdrs adrs 0 (i * 2 ^ p.a + forsIdx p md i))
        (s (forsSkAdrs adrs (i * 2 ^ p.a + forsIdx p md i))) := by
    unfold forsLeafWithSecret
    rw [pure_bind]
  have hroot : forsRootWithSecret core hash nodeHash (fun a => pure (s a)) adrs i =
      merkleRootM (forsLeafWithSecret core hash (fun a => pure (s a)) adrs)
        (forsNodeHashWith nodeHash adrs) p.a i := rfl
  rw [hleaf] at mv mc ml
  rw [hsig, hroot]
  simp only [val_bind, calls_bind, List.mem_append]
  rw [val_intrinsicAuthPathM_toList]
  refine ⟨mv, ?_⟩
  rintro c (hc | hc)
  · exact ml c hc
  · exact mc c hc

theorem sub_fors_spec (md : List Byte) (adrs : Adrs) :
    val (forsPkFromSigWith core hash nodeHash compress
        (val (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md adrs)) md adrs) =
        val (forsPkGenWithSecret core hash nodeHash compress (fun a => pure (s a)) adrs) ∧
      ∀ c ∈ calls (forsPkFromSigWith core hash nodeHash compress
          (val (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md adrs)) md adrs),
        c ∈ calls (forsPkGenWithSecret core hash nodeHash compress (fun a => pure (s a)) adrs) := by
  unfold forsPkFromSigWith forsPkGenWithSecret
  have hroots : val (Vector.ofFnM fun i : Fin p.k =>
      hash (forsNodeAdrs adrs 0 (i.val * 2 ^ p.a + forsIdx p md i.val))
          ((val (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md adrs))[i.val]).sk >>=
        fun leaf => PerfectMerkleTree.climbM (forsNodeHashWith nodeHash adrs)
          (i.val * 2 ^ p.a + forsIdx p md i.val) leaf
          ((val (forsSignWithSecret core hash nodeHash (fun a => pure (s a)) md
            adrs))[i.val]).auth.toList) =
      val (Vector.ofFnM fun i : Fin p.k =>
        forsRootWithSecret core hash nodeHash (fun a => pure (s a)) adrs i.val) := by
    apply Vector.ext
    intro i hi
    rw [getElem_ofFnM _ i hi, getElem_ofFnM _ i hi]
    exact (sub_fors_tree_spec core hash nodeHash s md adrs i hi).1
  simp only [val_bind, calls_bind, List.mem_append]
  refine ⟨?_, ?_⟩
  · exact congrArg (fun v => val (compress (forsPkAdrs adrs) (Vector.toList v))) hroots
  · rintro c (hc | hc)
    · left
      rw [mem_calls_ofFnM] at hc ⊢
      obtain ⟨i, hi⟩ := hc
      exact ⟨i, (sub_fors_tree_spec core hash nodeHash s md adrs i.val i.isLt).2 c hi⟩
    · right
      have h2 := congrArg (fun v => calls (compress (forsPkAdrs adrs) (Vector.toList v))) hroots
      exact h2 ▸ hc

end Components

section Hypertree

open sub_W GeneralHypertree

variable {C : Type} {vp : ValidatedParams} (core : CorePrimitives vp.params)
  (hash : Adrs → core.Y → sub_W C core.Y) (compress : Adrs → List core.Y → sub_W C core.Y)
  (nodeHash : Adrs → core.Y → core.Y → sub_W C core.Y) (s : Adrs → core.Y)

theorem sub_head_insertIdx_zero {X : Type} {n : ℕ} (rest : Vector X n) (x : X) :
    (rest.insertIdx 0 x).head = x := by
  simp [Vector.head, Vector.insertIdx_zero]

theorem sub_tail_insertIdx_zero {X : Type} {n : ℕ} (rest : Vector X n) (x : X) :
    (rest.insertIdx 0 x).tail = rest := by
  rw [Vector.insertIdx_zero]
  apply Vector.ext
  intro i hi
  simp [Vector.tail_eq_cast_extract]

/-- Every call of recovering the honest hypertree signature is a call of the honest root
computation of some XMSS tree of the hypertree. -/
theorem sub_ht_spec (pk : core.PkSeed) :
    ∀ (layers : ℕ) (rf : Bool) (pos : LayerPosition vp)
      (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      ∀ c ∈ calls (recoverFromPositionWith vp core hash compress nodeHash pk pos layers h msg
          (val (signFromPositionWithSecret core hash compress nodeHash (fun a => pure (s a)) rf
            pos layers h msg))),
        ∃ coord : LayerTreeCoord vp, c ∈ calls (xmssRootWithSecret core hash compress nodeHash
          (fun a => pure (s a)) coord.toAdrs)
  | 0, rf, pos, h, msg => by
    intro c hc
    exact absurd hc List.not_mem_nil
  | 1, rf, pos, h, msg => by
    intro c hc
    have hhead : (val (signFromPositionWithSecret core hash compress nodeHash
        (fun a => pure (s a)) rf pos 1 h msg)).head =
        val (xmssSignWithSecret core hash compress nodeHash (fun a => pure (s a)) msg pos.toAdrs
          pos.leaf.val) := by
      cases rf <;> rfl
    have hc' : c ∈ calls (xmssPkFromSigWith core hash compress nodeHash pos.leaf.val
        (val (signFromPositionWithSecret core hash compress nodeHash
        (fun a => pure (s a)) rf pos 1 h msg)).head msg pos.toAdrs) := hc
    rw [hhead] at hc'
    exact ⟨LayerTreeCoord.ofPosition pos,
      (sub_xmss_spec core hash compress nodeHash s msg pos.toAdrs pos.leaf.val pos.leaf.isLt).2 c
        hc'⟩
  | layers + 2, rf, pos, h, msg => by
    intro c hc
    obtain ⟨xv, xc⟩ :=
      sub_xmss_spec core hash compress nodeHash s msg pos.toAdrs pos.leaf.val pos.leaf.isLt
    have hsig : val (signFromPositionWithSecret core hash compress nodeHash
        (fun a => pure (s a)) rf pos (layers + 2) h msg) =
        (val (signFromPositionWithSecret core hash compress nodeHash (fun a => pure (s a)) false
          (pos.next (by omega)) (layers + 1) (by simp; omega)
          (val (xmssPkFromSigWith core hash compress nodeHash pos.leaf.val
            (val (xmssSignWithSecret core hash compress nodeHash (fun a => pure (s a)) msg
              pos.toAdrs pos.leaf.val)) msg pos.toAdrs)))).insertIdx 0
          (val (xmssSignWithSecret core hash compress nodeHash (fun a => pure (s a)) msg
              pos.toAdrs pos.leaf.val)) := rfl
    rw [hsig] at hc
    have hc' : c ∈ calls (xmssPkFromSigWith core hash compress nodeHash pos.leaf.val
          (Vector.head (Vector.insertIdx _ 0 _)) msg pos.toAdrs >>= fun root =>
        recoverFromPositionWith vp core hash compress nodeHash pk (pos.next (by omega))
          (layers + 1) (by simp; omega) root (Vector.tail (Vector.insertIdx _ 0 _))) := hc
    rw [sub_head_insertIdx_zero, sub_tail_insertIdx_zero] at hc'
    simp only [calls_bind, List.mem_append] at hc'
    rcases hc' with hc' | hc'
    · exact ⟨LayerTreeCoord.ofPosition pos, xc c hc'⟩
    · exact sub_ht_spec pk (layers + 1) false (pos.next (by omega)) (by simp; omega) _ c hc'

end Hypertree

/-! ## Transfer to the logging state monad and to the reference signature -/

section Transfer

open sub_W GeneralHypertree

theorem sub_forM_natural {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (F : m →ᵐ n) {α : Type} (f : α → m PUnit) : ∀ l : List α,
    F (l.forM f) = l.forM (fun x => F (f x))
  | [] => F.mmap_pure _
  | a :: l => by
    show F (f a >>= fun _ => l.forM f) = (F (f a) >>= fun _ => l.forM (fun x => F (f x)))
    rw [F.mmap_bind]
    exact bind_congr fun _ => sub_forM_natural F f l

theorem sub_recoverFromPositionWith_natural {vp : ValidatedParams} (core : CorePrimitives vp.params)
    {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y) (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r) (pk : core.PkSeed) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : core.Y) (sigs : Vector (XmssSig vp.params core) layers),
      F (recoverFromPositionWith vp core hashm compressm nodeHashm pk pos layers h msg sigs) =
        recoverFromPositionWith vp core hashn compressn nodeHashn pk pos layers h msg sigs
  | 0, pos, h, msg, sigs => F.mmap_pure _
  | 1, pos, h, msg, sigs =>
    xmssPkFromSigWith_natural F core hashm hashn compressm compressn nodeHashm nodeHashn
      hhash hcompress hnode _ _ _ _
  | layers + 2, pos, h, msg, sigs => by
    rw [recoverFromPositionWith, recoverFromPositionWith, F.mmap_bind,
      xmssPkFromSigWith_natural F core hashm hashn compressm compressn nodeHashm nodeHashn
        hhash hcompress hnode]
    exact bind_congr fun root => sub_recoverFromPositionWith_natural core F hashm hashn compressm
      compressn nodeHashm nodeHashn hhash hcompress hnode pk (layers + 1) _ _ _ _

variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-- The writer-monad hash callback: evaluate `Thash` at `pk` and record the call. -/
def sub_wTh (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    sub_W (prims.AdrsKey × List prims.Y) prims.Y :=
  (prims.Thash pk key xs, [(key, xs)])

theorem sub_toState_wTh (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    toState (sub_wTh pk key xs) = logTh pk key xs := rfl

theorem sub_toId_wTh (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y) :
    toId (sub_wTh pk key xs) = prims.Thash pk key xs := rfl

theorem sub_honestCalls_eq (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    honestCalls tbl pk =
      calls (structureVia (vp := vp) (sub_wTh pk) (fun a => pure (secretOf vp prims tbl a))) := by
  have h : toState (structureVia (vp := vp) (sub_wTh pk)
      (fun a => pure (secretOf vp prims tbl a))) =
      structureVia (vp := vp) (logTh pk) (fun a => pure (secretOf vp prims tbl a)) := by
    unfold structureVia
    rw [MonadHom.mmap_bind, sub_forM_natural]
    refine congrArg₂ _ ?_ ?_
    · refine congrArg _ (funext fun bp => ?_)
      rw [MonadHom.mmap_bind, forsPkGenWithSecret_natural prims.core toState _ _ _ _ _ _ _
        (fun a => pure (secretOf vp prims tbl a)) (fun a y => sub_toState_wTh pk _ _)
        (fun a l r => sub_toState_wTh pk _ _) (fun a ys => sub_toState_wTh pk _ _)
        (fun a _ => MonadHom.mmap_pure _ _)]
      exact bind_congr fun _ => MonadHom.mmap_pure _ _
    · funext _
      rw [sub_forM_natural]
      refine congrArg _ (funext fun c => ?_)
      rw [MonadHom.mmap_bind, xmssRootWithSecret_natural prims.core toState _ _ _ _ _ _ _
        (fun a => pure (secretOf vp prims tbl a)) (fun a y => sub_toState_wTh pk _ _)
        (fun a ys => sub_toState_wTh pk _ _) (fun a l r => sub_toState_wTh pk _ _)
        (fun a _ => MonadHom.mmap_pure _ _)]
      exact bind_congr fun _ => MonadHom.mmap_pure _ _
  unfold honestCalls
  rw [← h, toState_run]
  rfl

theorem sub_verifyCalls_eq (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    verifyCalls pk msg sig =
      calls (forsPkFromSigWith prims.core
          (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
          (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs)
          sig.fors (digestParts pk sig.randomness msg).md.toList
          (digestParts pk sig.randomness msg).forsAdrs >>= fun forsPk =>
        GeneralHypertree.pkFromSigWith vp prims.core
          (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs)
          (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
          forsPk sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg)) := by
  have h : toState (forsPkFromSigWith prims.core
          (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
          (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs)
          sig.fors (digestParts pk sig.randomness msg).md.toList
          (digestParts pk sig.randomness msg).forsAdrs >>= fun forsPk =>
        GeneralHypertree.pkFromSigWith vp prims.core
          (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs)
          (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
          forsPk sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg)) =
      (forsPkFromSigWith prims.core
          (fun a x => logTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a l r => logTh pk.pkSeed (prims.adrsToKey a) [l, r])
          (fun a xs => logTh pk.pkSeed (prims.adrsToKey a) xs)
          sig.fors (digestParts pk sig.randomness msg).md.toList
          (digestParts pk sig.randomness msg).forsAdrs >>= fun forsPk =>
        GeneralHypertree.pkFromSigWith vp prims.core
          (fun a x => logTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a xs => logTh pk.pkSeed (prims.adrsToKey a) xs)
          (fun a l r => logTh pk.pkSeed (prims.adrsToKey a) [l, r])
          forsPk sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg)) := by
    rw [MonadHom.mmap_bind, forsPkFromSigWith_natural toState prims.core _ _ _ _ _ _
      (fun a y => sub_toState_wTh pk.pkSeed _ _) (fun a l r => sub_toState_wTh pk.pkSeed _ _)
      (fun a ys => sub_toState_wTh pk.pkSeed _ _)]
    exact bind_congr fun forsPk => sub_recoverFromPositionWith_natural prims.core toState _ _ _ _
      _ _ (fun a y => sub_toState_wTh pk.pkSeed _ _) (fun a ys => sub_toState_wTh pk.pkSeed _ _)
      (fun a l r => sub_toState_wTh pk.pkSeed _ _) _ _ _ _ _ _
  unfold verifyCalls
  show (StateT.run (forsPkFromSigWith prims.core
          (fun a x => logTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a l r => logTh pk.pkSeed (prims.adrsToKey a) [l, r])
          (fun a xs => logTh pk.pkSeed (prims.adrsToKey a) xs)
          sig.fors (digestParts pk sig.randomness msg).md.toList
          (digestParts pk sig.randomness msg).forsAdrs >>= fun forsPk =>
        GeneralHypertree.pkFromSigWith vp prims.core
          (fun a x => logTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a xs => logTh pk.pkSeed (prims.adrsToKey a) xs)
          (fun a l r => logTh pk.pkSeed (prims.adrsToKey a) [l, r])
          forsPk sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg)) []).2 = _
  rw [← h, toState_run]
  rfl

/-- The reference signature in terms of writer-monad values. -/
theorem sub_idealSign_eq (tbl : SecretTable vp prims) (msg : List Byte)
    (pk : PublicKeyCore prims.core) (R : prims.Y) :
    idealSign vp prims tbl msg pk R =
      ⟨R,
        val (forsSignWithSecret prims.core
          (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
          (fun a => pure (secretOf vp prims tbl a))
          (digestParts pk R msg).md.toList (digestParts pk R msg).forsAdrs),
        val (GeneralHypertree.signWithSecret prims.core
          (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs)
          (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
          (fun a => pure (secretOf vp prims tbl a))
          (val (forsPkFromSigWith prims.core
            (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
            (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
            (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs)
            (val (forsSignWithSecret prims.core
              (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
              (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
              (fun a => pure (secretOf vp prims tbl a))
              (digestParts pk R msg).md.toList (digestParts pk R msg).forsAdrs))
            (digestParts pk R msg).md.toList (digestParts pk R msg).forsAdrs))
          (digestParts pk R msg))⟩ := by
  have k1 : ∀ (md : List Byte) (adrs : Adrs),
      simulateQ (PublicHash.impl prims) (forsSignWithSecretM prims.core
        (fun a => pure (secretOf vp prims tbl a)) md pk.pkSeed adrs :
          OracleComp (publicHashSpec prims.core) _) =
      val (forsSignWithSecret prims.core
          (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
          (fun a => pure (secretOf vp prims tbl a)) md adrs) := by
    intro md adrs
    have h1 := forsSignWithSecret_natural prims.core (simulateQ' (PublicHash.impl prims))
      (PublicHash.f prims.core pk.pkSeed) (fun a x => (prims.F pk.pkSeed a x : Id prims.Y))
      (PublicHash.h prims.core pk.pkSeed) (fun a l r => (prims.H pk.pkSeed a l r : Id prims.Y))
      (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
      (fun a y => PublicHash.simulateQ_f prims pk.pkSeed a y)
      (fun a l r => PublicHash.simulateQ_h prims pk.pkSeed a l r)
      (fun a _ => simulateQ_pure (PublicHash.impl prims) _) md adrs
    have h2 := forsSignWithSecret_natural prims.core
      (toId (C := prims.AdrsKey × List prims.Y))
      (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
      (fun a x => (prims.F pk.pkSeed a x : Id prims.Y))
      (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
      (fun a l r => (prims.H pk.pkSeed a l r : Id prims.Y))
      (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
      (fun a y => rfl) (fun a l r => rfl) (fun a _ => rfl) md adrs
    exact h1.trans h2.symm
  have k2 : ∀ (fs : ForsSigCore vp.params prims.core) (md : List Byte) (adrs : Adrs),
      simulateQ (PublicHash.impl prims) (forsPkFromSigM prims.core fs md pk.pkSeed adrs :
          OracleComp (publicHashSpec prims.core) _) =
      val (forsPkFromSigWith prims.core
            (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
            (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
            (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs) fs md adrs) := by
    intro fs md adrs
    have h1 := forsPkFromSigWith_natural (simulateQ' (PublicHash.impl prims)) prims.core
      (PublicHash.f prims.core pk.pkSeed) (fun a x => (prims.F pk.pkSeed a x : Id prims.Y))
      (PublicHash.h prims.core pk.pkSeed) (fun a l r => (prims.H pk.pkSeed a l r : Id prims.Y))
      (PublicHash.tl prims.core pk.pkSeed) (fun a xs => (prims.Tl pk.pkSeed a xs : Id prims.Y))
      (fun a y => PublicHash.simulateQ_f prims pk.pkSeed a y)
      (fun a l r => PublicHash.simulateQ_h prims pk.pkSeed a l r)
      (fun a xs => PublicHash.simulateQ_tl prims pk.pkSeed a xs) fs md adrs
    have h2 := forsPkFromSigWith_natural (toId (C := prims.AdrsKey × List prims.Y)) prims.core
      (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
      (fun a x => (prims.F pk.pkSeed a x : Id prims.Y))
      (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
      (fun a l r => (prims.H pk.pkSeed a l r : Id prims.Y))
      (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs)
      (fun a xs => (prims.Tl pk.pkSeed a xs : Id prims.Y))
      (fun a y => rfl) (fun a l r => rfl) (fun a xs => rfl) fs md adrs
    exact h1.trans h2.symm
  have k3 : ∀ (m0 : prims.Y) (parts : DigestParts vp.params),
      simulateQ (PublicHash.impl prims) (GeneralHypertree.signWithSecretM prims.core
        (fun a => pure (secretOf vp prims tbl a)) m0 pk.pkSeed parts :
          OracleComp (publicHashSpec prims.core) _) =
      val (GeneralHypertree.signWithSecret prims.core
          (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
          (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs)
          (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
          (fun a => pure (secretOf vp prims tbl a)) m0 parts) := by
    intro m0 parts
    have h1 := GeneralHypertree.signWithSecret_natural prims.core
      (simulateQ' (PublicHash.impl prims))
      (PublicHash.f prims.core pk.pkSeed) (fun a x => (prims.F pk.pkSeed a x : Id prims.Y))
      (PublicHash.tl prims.core pk.pkSeed) (fun a xs => (prims.Tl pk.pkSeed a xs : Id prims.Y))
      (PublicHash.h prims.core pk.pkSeed) (fun a l r => (prims.H pk.pkSeed a l r : Id prims.Y))
      (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
      (fun a y => PublicHash.simulateQ_f prims pk.pkSeed a y)
      (fun a xs => PublicHash.simulateQ_tl prims pk.pkSeed a xs)
      (fun a l r => PublicHash.simulateQ_h prims pk.pkSeed a l r)
      (fun a _ => simulateQ_pure (PublicHash.impl prims) _) m0 parts
    have h2 := GeneralHypertree.signWithSecret_natural prims.core
      (toId (C := prims.AdrsKey × List prims.Y))
      (fun a x => sub_wTh pk.pkSeed (prims.adrsToKey a) [x])
      (fun a x => (prims.F pk.pkSeed a x : Id prims.Y))
      (fun a xs => sub_wTh pk.pkSeed (prims.adrsToKey a) xs)
      (fun a xs => (prims.Tl pk.pkSeed a xs : Id prims.Y))
      (fun a l r => sub_wTh pk.pkSeed (prims.adrsToKey a) [l, r])
      (fun a l r => (prims.H pk.pkSeed a l r : Id prims.Y))
      (fun a => pure (secretOf vp prims tbl a)) (fun a => pure (secretOf vp prims tbl a))
      (fun a y => rfl) (fun a xs => rfl) (fun a l r => rfl) (fun a _ => rfl) m0 parts
    exact h1.trans h2.symm
  rw [← k1, ← k2, ← k3]
  unfold idealSign GeneralScheme.signInternalWithSecretRandomizerM
  simp only [simulateQ_bind, simulateQ_pure, PublicHash.simulateQ_hmsg]
  rfl

end Transfer

/-- Honest verification stays inside the honest structure: every hash call made by verifying the
reference signature is a call of the honest structure (same tweak, same input). -/
theorem sub_verifyCalls_idealSign_subset {vp : ValidatedParams} {prims : Primitives vp.params}
    (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (msg : List Byte) (R : prims.Y) :
    ∀ c ∈ verifyCalls (idealPk vp prims tbl pkSeed) msg
        (idealSign vp prims tbl msg (idealPk vp prims tbl pkSeed) R),
      c ∈ honestCalls tbl pkSeed := by
  intro c hc
  rw [sub_verifyCalls_eq, sub_idealSign_eq] at hc
  rw [sub_honestCalls_eq]
  unfold structureVia
  simp only [sub_W.calls_bind, List.mem_append, sub_W.mem_calls_forM, List.append_nil,
    sub_W.calls_pure] at hc ⊢
  rcases hc with hc | hc
  · left
    refine ⟨BottomPosition.ofDigestParts vp (digestParts (idealPk vp prims tbl pkSeed) R msg),
      mem_allBottomPositions vp _, ?_⟩
    rw [BottomPosition.forsAdrs_ofDigestParts]
    exact (sub_fors_spec prims.core _ _ _ _ _ _).2 c hc
  · right
    obtain ⟨coord, hcoord⟩ := sub_ht_spec prims.core _ _ _ _ _ _ _ _ _ _ c hc
    exact ⟨coord, mem_allXmssTrees vp coord, hcoord⟩

end Reduction

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The SM-TCR adversary built from a forger. -/
noncomputable def bTcr (A : Forger vp prims optRand pkSeedDist) :
    TweakableHash.SM_DT_TCR_Adversary (tcrProblem vp prims pkSeedDist) where
  State := SecretTable vp prims
  choose := do
    let tbl ← (monadLift (sampleTable vp prims) :
      OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey (List prims.Y)
        prims.Y + TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl))
        (SecretTable vp prims))
    structureVia (vp := vp) (prims := prims)
      (fun key xs => do
        let r ← ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey (List prims.Y)
            prims.Y + TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl)).query
            (Sum.inr (Sum.inl (key, xs))) :
          OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
            (List prims.Y) prims.Y +
            TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl))
            (Option prims.Y))
        pure (r.getD default))
      (fun a => pure (secretOf vp prims tbl a))
    return tbl
  forge := fun tbl pkSeed => do
    let pk := idealPk vp prims tbl pkSeed
    let ((msg, sig), _) ← g2Run A tbl pk
    return (findCollision pkSeed (honestCalls tbl pkSeed) (verifyCalls pk msg sig)).getD (0, [])

/-! ## Lemmas -/

/-- The honest structure makes exactly one call per ledger address. -/
theorem honestCalls_map_fst (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : prims.PkSeed) :
    ((honestCalls tbl pk).map (·.1)).Perm ((constructionAddresses vp).map prims.adrsToKey) :=
  mf_honestCalls_map_fst hS tbl pk

/-- Target-count lemma: the tweaks are distinct and there are `tcrTargets vp` of them, so no
challenge query of `bTcr` is refused. -/
theorem honestCalls_nodup_length (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : prims.PkSeed) :
    ((honestCalls tbl pk).map (·.1)).Nodup ∧ (honestCalls tbl pk).length = tcrTargets vp := by
  have hperm := honestCalls_map_fst hS tbl pk
  refine ⟨hperm.nodup_iff.mpr ?_, ?_⟩
  · refine List.Nodup.map_on (fun a ha b hb hab => ?_) (constructionAddresses_nodup vp)
    exact hS.keyInj (addressFacts_of_mem_constructionAddresses hS.bounds ha)
      (addressFacts_of_mem_constructionAddresses hS.bounds hb) hab
  · have := hperm.length_eq
    simpa [tcrTargets] using this

/-- **Correctness over a table.**  The reference signature verifies under the table's key. -/
theorem verifyInternal_idealSign (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (msg : List Byte) (R : prims.Y) :
    GeneralScheme.verifyInternal vp prims msg
      (idealSign vp prims tbl msg (idealPk vp prims tbl pkSeed) R)
      (idealPk vp prims tbl pkSeed) = true :=
  col_verifyInternal_idealSign hS tbl pkSeed msg R

/-- **Two-signature comparison.**  In `G2`, a fresh valid forgery of class `tcr` and the
reference signature (the honest signature on the same message under the forgery's randomizer)
make, during verification, two hash calls at the same tweak on different inputs with the same
output. -/
theorem verifyCalls_collision_of_tcr (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (log : G2Log prims) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core)
    (hvalid : g2Valid (idealPk vp prims tbl pkSeed) log msg sig = true)
    (hclass : g2ClassOf tbl (idealPk vp prims tbl pkSeed) log msg sig = .tcr) :
    ∃ c ∈ verifyCalls (idealPk vp prims tbl pkSeed) msg sig,
      ∃ c' ∈ verifyCalls (idealPk vp prims tbl pkSeed) msg
          (idealSign vp prims tbl msg (idealPk vp prims tbl pkSeed) sig.randomness),
        c.1 = c'.1 ∧ c.2 ≠ c'.2 ∧
          prims.Thash pkSeed c.1 c.2 = prims.Thash pkSeed c'.1 c'.2 :=
  col_verifyCalls_collision_of_tcr hS tbl pkSeed log msg sig hvalid hclass

/-- **Honest verification stays inside the honest structure.**  Every hash call made by
verifying the reference signature is a call of the honest structure (same tweak, same input). -/
theorem verifyCalls_idealSign_subset (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (msg : List Byte) (R : prims.Y) :
    ∀ c ∈ verifyCalls (idealPk vp prims tbl pkSeed) msg
        (idealSign vp prims tbl msg (idealPk vp prims tbl pkSeed) R),
      c ∈ honestCalls tbl pkSeed :=
  sub_verifyCalls_idealSign_subset hS tbl pkSeed msg R

/-- **Deterministic extraction (the heart of the case analysis).**  In `G2`, a fresh valid
forgery of class `tcr` verifies through a hash call that collides with a call of the honest
structure. -/
theorem findCollision_isSome_of_tcr (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (log : G2Log prims) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core)
    (hvalid : g2Valid (idealPk vp prims tbl pkSeed) log msg sig = true)
    (hclass : g2ClassOf tbl (idealPk vp prims tbl pkSeed) log msg sig = .tcr) :
    (findCollision pkSeed (honestCalls tbl pkSeed)
      (verifyCalls (idealPk vp prims tbl pkSeed) msg sig)).isSome := by
  obtain ⟨c, hc, c', hc', hkey, hne, hcol⟩ :=
    verifyCalls_collision_of_tcr hS tbl pkSeed log msg sig hvalid hclass
  have hmem := verifyCalls_idealSign_subset hS tbl pkSeed msg sig.randomness c' hc'
  unfold findCollision
  rw [List.findSome?_isSome_iff]
  refine ⟨c, hc, ?_⟩
  have hlt : (honestCalls tbl pkSeed).findIdx (fun t =>
      decide (t.1 = c.1 ∧ c.2 ≠ t.2 ∧ prims.Thash pkSeed c.1 c.2 = prims.Thash pkSeed t.1 t.2)) <
      (honestCalls tbl pkSeed).length :=
    List.findIdx_lt_length_of_exists ⟨c', hmem, decide_eq_true ⟨hkey.symm, hne, hcol⟩⟩
  dsimp only
  rw [if_pos hlt]
  rfl

/-- Whatever `findCollision` returns is a winning SM-TCR answer against the target list. -/
theorem findCollision_sound (pk : prims.PkSeed)
    (targets calls : List (prims.AdrsKey × List prims.Y)) (j : ℕ) (m : List prims.Y)
    (h : findCollision pk targets calls = some (j, m)) :
    ∃ t, targets[j]? = some t ∧ m ≠ t.2 ∧ prims.Thash pk t.1 m = prims.Thash pk t.1 t.2 := by
  unfold findCollision at h
  obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at hc
  split_ifs at hc with hlt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
  refine ⟨_, List.getElem?_eq_getElem hlt, ?_⟩
  have := List.findIdx_getElem (w := hlt)
  simp only [decide_eq_true_eq] at this
  obtain ⟨h1, h2, h3⟩ := this
  exact ⟨h2, (congrArg (fun k => prims.Thash pk k c.2) h1).trans h3⟩

/-! ### The structure as a free program

`structureVia` is polymorphic in the monad, so every instance is the image of the free instance
`structureFree` (one oracle: the tweakable hash) under `simulateQ`. -/

/-- The single-oracle interface "evaluate the tweakable hash". -/
abbrev thSpec (prims : Primitives vp.params) : OracleSpec (prims.AdrsKey × List prims.Y) :=
  (prims.AdrsKey × List prims.Y) →ₒ prims.Y

/-- The honest structure as a program over the hash oracle. -/
noncomputable def structureFree (tbl : SecretTable vp prims) : OracleComp (thSpec prims) Unit :=
  structureVia (vp := vp) (prims := prims)
    (fun key xs => (liftM ((thSpec prims).query (key, xs)) : OracleComp (thSpec prims) prims.Y))
    (fun a => pure (secretOf vp prims tbl a))

theorem forM_natural {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (F : m →ᵐ n) {α : Type} (l : List α) (f : α → m PUnit) (g : α → n PUnit)
    (h : ∀ a, F (f a) = g a) : F (l.forM f) = l.forM g := by
  induction l with
  | nil => simp [F.mmap_pure]
  | cons a l ih => simp [F.mmap_bind, h, ih]

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
/-- `structureVia` commutes with monad morphisms. -/
theorem structureVia_natural {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n]
    [LawfulMonad n] (F : m →ᵐ n) (th : prims.AdrsKey → List prims.Y → m prims.Y)
    (secret : Adrs → m prims.Y) :
    F (structureVia (vp := vp) th secret) =
      structureVia (vp := vp) (fun k xs => F (th k xs)) (fun a => F (secret a)) := by
  unfold structureVia
  rw [F.mmap_bind]
  congr 1
  · refine forM_natural F _ _ _ fun bp => ?_
    rw [F.mmap_bind, forsPkGenWithSecret_natural prims.core F _ _ _ _ _ _ _ _
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
    exact bind_congr fun _ => F.mmap_pure _
  · funext _
    refine forM_natural F _ _ _ fun c => ?_
    rw [F.mmap_bind, xmssRootWithSecret_natural prims.core F _ _ _ _ _ _ _ _
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)]
    exact bind_congr fun _ => F.mmap_pure _

/-- The logging handler of `honestCalls`. -/
def logImpl (pk : prims.PkSeed) :
    QueryImpl (thSpec prims) (StateM (List (prims.AdrsKey × List prims.Y))) :=
  fun t => logTh pk t.1 t.2

/-- The handler `bTcr` routes hash calls to, inside the SM-TCR game at seed `pk`. -/
noncomputable def chalImpl (pkSeedDist : ProbComp prims.PkSeed) (pk : prims.PkSeed) :
    QueryImpl (thSpec prims)
      (StateT (TweakableHash.SM_DT_TCR_State prims.AdrsKey (List prims.Y)) ProbComp) :=
  fun t => do
    let r ← TweakableHash.SM_DT_TCR_challengeOracle (tcrProblem vp prims pkSeedDist) pk t
    pure (r.getD default)

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
theorem honestCalls_eq_free (tbl : SecretTable vp prims) (pk : prims.PkSeed) :
    honestCalls tbl pk = ((simulateQ (logImpl pk) (structureFree tbl)).run []).2 := by
  unfold honestCalls structureFree
  have := structureVia_natural (vp := vp) (simulateQ' (logImpl (prims := prims) pk))
    (fun key xs => (liftM ((thSpec prims).query (key, xs)) : OracleComp (thSpec prims) prims.Y))
    (fun a => pure (secretOf vp prims tbl a))
  simp only [simulateQ'_apply, simulateQ_spec_query, simulateQ_pure] at this
  rw [this]
  rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
/-- The log only grows. -/
theorem logImpl_run_prefix {α : Type} (pk : prims.PkSeed) (P : OracleComp (thSpec prims) α)
    (qs : List (prims.AdrsKey × List prims.Y)) :
    ∃ l, ((simulateQ (logImpl pk) P).run qs).2 = qs ++ l := by
  induction P using OracleComp.inductionOn generalizing qs with
  | pure a => exact ⟨[], by rw [List.append_nil]; rfl⟩
  | query_bind t k ih =>
    obtain ⟨l, hl⟩ := ih (prims.Thash pk t.1 t.2) (qs ++ [t])
    refine ⟨[t] ++ l, ?_⟩
    rw [simulateQ_bind, simulateQ_spec_query, ← List.append_assoc, ← hl]
    rfl

/-- **Simulation lemma.**  If the logged run of a hash program from history `qs` ends with
distinct tweaks and at most the target cap of entries, then running it against the SM-TCR
challenge oracle from `(qs, [])` refuses no query, returns the same value and records the same
history. -/
theorem chalImpl_run_eq {α : Type} (pk : prims.PkSeed) (P : OracleComp (thSpec prims) α)
    (qs : List (prims.AdrsKey × List prims.Y))
    (hnd : (((simulateQ (logImpl pk) P).run qs).2.map (·.1)).Nodup)
    (hlen : ((simulateQ (logImpl pk) P).run qs).2.length ≤ tcrTargets vp) :
    (simulateQ (chalImpl (vp := vp) pkSeedDist pk) P).run (qs, []) =
      pure (((simulateQ (logImpl pk) P).run qs).1, (((simulateQ (logImpl pk) P).run qs).2, [])) := by
  induction P using OracleComp.inductionOn generalizing qs with
  | pure a => rfl
  | query_bind t k ih =>
    have hstep : (simulateQ (logImpl pk) (liftM ((thSpec prims).query t) >>= k)).run qs =
        (simulateQ (logImpl pk) (k (prims.Thash pk t.1 t.2))).run (qs ++ [t]) := by
      rw [simulateQ_bind, simulateQ_spec_query]; rfl
    rw [hstep] at hnd hlen ⊢
    obtain ⟨l, hl⟩ := logImpl_run_prefix pk (k (prims.Thash pk t.1 t.2)) (qs ++ [t])
    have hfresh : TweakableHash.TweakFresh Prod.fst qs ([] : List prims.AdrsKey) t.1 := by
      refine ⟨?_, by simp⟩
      rintro ⟨e, he, het⟩
      rw [hl, List.map_append, List.map_append] at hnd
      have := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 e.1
        (List.mem_map_of_mem he) t.1 (by simp)
      exact this het
    have hlt : qs.length < (tcrProblem vp prims pkSeedDist).numTargets := by
      rw [hl] at hlen
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      show qs.length < tcrTargets vp
      omega
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hq : (chalImpl (vp := vp) pkSeedDist pk t).run (qs, []) =
        pure (prims.Thash pk t.1 t.2, (qs ++ [t], [])) := by
      unfold chalImpl
      rw [StateT.run_bind, TweakableHash.SM_DT_TCR_challengeOracle_run_of_fresh hlt hfresh,
        pure_bind]
      rfl
    rw [hq, pure_bind]
    exact ih _ _ hnd hlen

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [Inhabited prims.Y] in
/-- Private randomness of `choose` passes through the SM-TCR oracles untouched. -/
theorem tcrOracles_run_lift {α : Type} (pk : prims.PkSeed) (oa : ProbComp α)
    (s : TweakableHash.SM_DT_TCR_State prims.AdrsKey (List prims.Y)) :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
      (monadLift oa :
      OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey (List prims.Y)
        prims.Y + TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl)) α)).run s =
      (fun a => (a, s)) <$> oa := by
  unfold TweakableHash.SM_DT_TCR_oracles
  erw [QueryImpl.simulateQ_add_liftM_left]
  rw [simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp

/-- The `choose` phase of `bTcr`, run in the SM-TCR game at seed `pk`, records exactly
`honestCalls tbl pk` as its challenge history (and returns `tbl`). -/
theorem bTcr_choose_run (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) :
    (simulateQ (TweakableHash.SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
        (bTcr A).choose).run ([], []) =
      (fun tbl => (tbl, (honestCalls tbl pk, []))) <$> sampleTable vp prims := by
  have hstruct : ∀ tbl : SecretTable vp prims,
      simulateQ (TweakableHash.SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk)
        (structureVia (vp := vp) (prims := prims)
          (fun key xs => do
            let r ← ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
                (List prims.Y) prims.Y +
                TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl)).query
                (Sum.inr (Sum.inl (key, xs))) :
              OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
                (List prims.Y) prims.Y +
                TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl))
                (Option prims.Y))
            pure (r.getD default))
          (fun a => pure (secretOf vp prims tbl a))) =
      simulateQ (chalImpl (vp := vp) pkSeedDist pk) (structureFree tbl) := by
    intro tbl
    have h1 := structureVia_natural (vp := vp)
      (simulateQ' (TweakableHash.SM_DT_TCR_oracles (tcrProblem vp prims pkSeedDist) pk))
      (fun key xs => do
            let r ← ((unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
                (List prims.Y) prims.Y +
                TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl)).query
                (Sum.inr (Sum.inl (key, xs))) :
              OracleComp (unifSpec + (TweakableHash.SM_DT_TCR_challengeSpec prims.AdrsKey
                (List prims.Y) prims.Y +
                TweakableHash.collectionSpec (tcrProblem vp prims pkSeedDist).thColl))
                (Option prims.Y))
            pure (r.getD default))
      (fun a => pure (secretOf vp prims tbl a))
    have h2 := structureVia_natural (vp := vp)
      (simulateQ' (chalImpl (vp := vp) (prims := prims) pkSeedDist pk))
      (fun key xs => (liftM ((thSpec prims).query (key, xs)) : OracleComp (thSpec prims) prims.Y))
      (fun a => pure (secretOf vp prims tbl a))
    simp only [simulateQ'_apply, simulateQ_spec_query, simulateQ_pure, simulateQ_bind] at h1 h2
    unfold structureFree
    rw [h1, h2]
    unfold chalImpl TweakableHash.SM_DT_TCR_oracles
    simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    rfl
  have hnl := honestCalls_nodup_length hS
  unfold bTcr
  dsimp only
  rw [simulateQ_bind, StateT.run_bind]
  rw [tcrOracles_run_lift, map_eq_bind_pure_comp, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr fun tbl => ?_
  rw [Function.comp_apply, pure_bind, simulateQ_bind, StateT.run_bind, hstruct tbl,
    chalImpl_run_eq pk _ [] (by rw [← honestCalls_eq_free]; exact (hnl tbl pk).1)
      (by rw [← honestCalls_eq_free]; exact (hnl tbl pk).2.le), pure_bind,
    ← honestCalls_eq_free]
  rfl

/-- The SM-TCR experiment at `bTcr A`, with the `choose` phase evaluated. -/
theorem tcrExperiment_bTcr (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    TweakableHash.SM_DT_TCR_Experiment (bTcr A) = (do
      let pkSeed ← pkSeedDist
      let tbl ← sampleTable vp prims
      let r ← g2Run A tbl (idealPk vp prims tbl pkSeed)
      let jm := (findCollision pkSeed (honestCalls tbl pkSeed)
        (verifyCalls (idealPk vp prims tbl pkSeed) r.1.1 r.1.2)).getD (0, [])
      match (honestCalls tbl pkSeed)[jm.1]? with
      | none => return false
      | some (t, mj) => return decide (jm.2 ≠ mj ∧
          prims.Thash pkSeed t jm.2 = prims.Thash pkSeed t mj)) := by
  unfold TweakableHash.SM_DT_TCR_Experiment
  refine bind_congr fun pkSeed => ?_
  rw [bTcr_choose_run hS A pkSeed]
  rw [map_eq_bind_pure_comp]
  refine (bind_assoc _ _ _).trans ?_
  refine bind_congr fun tbl => ?_
  refine (pure_bind _ _).trans ?_
  refine (bind_assoc (g2Run A tbl (idealPk vp prims tbl pkSeed)) _ _).trans ?_
  refine bind_congr fun r => ?_
  obtain ⟨⟨msg, sig⟩, log⟩ := r
  refine (pure_bind _ _).trans ?_
  dsimp only
  generalize (findCollision pkSeed (honestCalls tbl pkSeed)
    (verifyCalls (idealPk vp prims tbl pkSeed) msg sig)).getD (0, []) = jm
  obtain ⟨j, m⟩ := jm
  dsimp only
  cases (honestCalls tbl pkSeed)[j]? with
  | none => rfl
  | some t => rfl

/-- **Step 6.** -/
theorem stepTCR (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    StepTCR A (bTcr A) := by
  unfold StepTCR TweakableHash.SM_DT_TCR_Advantage prTrue
  rw [tcrExperiment_bTcr hS A, g2Class]
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pkSeed => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun tbl => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  obtain ⟨⟨msg, sig⟩, log⟩ := r
  dsimp only
  by_cases hv : (g2Valid (idealPk vp prims tbl pkSeed) log msg sig &&
      decide (g2ClassOf tbl (idealPk vp prims tbl pkSeed) log msg sig = .tcr)) = true
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hv
    have hsome := findCollision_isSome_of_tcr hS tbl pkSeed log msg sig hv.1 hv.2
    obtain ⟨⟨j, m⟩, hjm⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨t, ht, hne, heq⟩ := findCollision_sound _ _ _ j m hjm
    rw [hjm]
    simp only [Option.getD_some, ht]
    simp [hne, heq, hv.1, hv.2]
  · rw [Bool.not_eq_true] at hv
    rw [hv]
    simp

end Reduction

#print axioms Reduction.honestCalls_map_fst
#print axioms Reduction.honestCalls_nodup_length
#print axioms Reduction.findCollision_sound
#print axioms Reduction.findCollision_isSome_of_tcr
#print axioms Reduction.bTcr_choose_run
#print axioms Reduction.stepTCR

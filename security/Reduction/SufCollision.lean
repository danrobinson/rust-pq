import Reduction.TCR

/-!
# Two different signatures with the same randomizer collide (deterministic)

The deterministic core of the strong-unforgeability analysis (`Reduction.Suf`): two *different*
signatures `sig ≠ ref` with the same randomizer that both verify for the same message under the
same public key either

* WOTS+-sign different messages with the same recovered chain ends at some hypertree layer
  (`wotsLayer?` finds a layer), or
* make two verification hash calls at the same tweak on different inputs with the same output
  (`col_Coll`).

No probability, no adversary, no assumption.  It extends `col_collision_of_classify`
(`Reduction.TCR`), which treats the case "some unopened FORS leaf image differs", to *every*
difference between the two signatures:

* a FORS secret value differs but has the same `F`-image — a collision of `F` at that leaf;
* an authentication path differs while the node below agrees — a collision at an `H` node
  (`suf_climb_collision`);
* a WOTS+ signature value differs while the signed message and the chain ends agree — a
  collision of `F` inside that chain (`suf_chain_collision`);
* the remaining cases are those of `col_fors_collision` and `col_xmss_collision`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-! ## Extensionality helpers -/

theorem suf_vec_exists_ne {α : Type} {n : ℕ} (v w : Vector α n) (h : v ≠ w) :
    ∃ i : Fin n, v[i.val] ≠ w[i.val] := by
  by_contra hcon
  exact h (Vector.ext fun i hi => by_contra fun hi' => hcon ⟨⟨i, hi⟩, hi'⟩)

theorem suf_forsTree_ext (a b : ForsTreeSigCore vp.params prims.core) (h1 : a.sk = b.sk)
    (h2 : a.auth = b.auth) : a = b := by
  obtain ⟨s1, a1⟩ := a
  obtain ⟨s2, a2⟩ := b
  dsimp only at h1 h2
  subst h1
  subst h2
  rfl

theorem suf_xmssSig_ext (a b : XmssSig vp.params prims.core) (h1 : a.wots = b.wots)
    (h2 : a.auth = b.auth) : a = b := by
  obtain ⟨s1, a1⟩ := a
  obtain ⟨s2, a2⟩ := b
  dsimp only at h1 h2
  subst h1
  subst h2
  rfl

theorem suf_sig_ext (a b : GeneralScheme.SignatureCore vp prims.core)
    (h1 : a.randomness = b.randomness) (h2 : a.fors = b.fors) (h3 : a.hypertree = b.hypertree) :
    a = b := by
  obtain ⟨r1, f1, t1⟩ := a
  obtain ⟨r2, f2, t2⟩ := b
  dsimp only at h1 h2 h3
  subst h1
  subst h2
  subst h3
  rfl

/-- The last layer where two message sequences that agree at `d` still differ. -/
theorem suf_meet {α : Type} (F H : ℕ → α) (d j0 : ℕ) (hj0 : j0 ≤ d) (h0 : F j0 ≠ H j0)
    (hd : F d = H d) : ∃ j, j < d ∧ F j ≠ H j ∧ F (j + 1) = H (j + 1) := by
  obtain ⟨k, hk, hne, heq⟩ := col_meet (fun k => F (j0 + k)) (fun k => H (j0 + k)) (d - j0)
    (by simpa using h0) (by
      have : j0 + (d - j0) = d := by omega
      simpa [this] using hd)
  exact ⟨j0 + k, by omega, hne, heq⟩

/-! ## Chains -/

/-- Two chains over the same positions from different start values to the same end value collide
at an `F` call. -/
theorem suf_chain_collision (pk : prims.PkSeed) (adrs : Adrs) (i : ℕ) :
    ∀ (s : ℕ) (x1 x2 : prims.Y), x1 ≠ x2 →
    chain prims pk adrs x1 i s = chain prims pk adrs x2 i s →
    col_Coll pk
      (col_calls (chainM prims.core pk adrs x1 i s :
        OracleComp (publicHashSpec prims.core) prims.Y))
      (col_calls (chainM prims.core pk adrs x2 i s :
        OracleComp (publicHashSpec prims.core) prims.Y)) := by
  intro s
  induction s with
  | zero =>
    intro x1 x2 hne h
    exact absurd h hne
  | succ s ih =>
    intro x1 x2 hne h
    have hprog : ∀ x : prims.Y,
        (chainM prims.core pk adrs x i (s + 1) :
          OracleComp (publicHashSpec prims.core) prims.Y) =
        (chainM prims.core pk adrs x i s :
          OracleComp (publicHashSpec prims.core) prims.Y) >>= fun y =>
            PublicHash.f prims.core pk (adrs.setHashAddress (i + s)) y := fun x => rfl
    rw [hprog x1, hprog x2]
    rw [chain_succ, chain_succ] at h
    by_cases hs : chain prims pk adrs x1 i s = chain prims pk adrs x2 i s
    · exact (ih x1 x2 hne hs).mono (fun c hc => col_mem_bind_left _ hc)
        (fun c hc => col_mem_bind_left _ hc)
    · refine ⟨(prims.adrsToKey (adrs.setHashAddress (i + s)), [chain prims pk adrs x1 i s]),
        col_mem_bind_right _ (by rw [col_calls_f]; exact List.mem_singleton_self _),
        (prims.adrsToKey (adrs.setHashAddress (i + s)), [chain prims pk adrs x2 i s]),
        col_mem_bind_right _ (by rw [col_calls_f]; exact List.mem_singleton_self _),
        rfl, ?_, h⟩
      intro heq
      exact hs (List.cons.inj heq).1

/-- Two different WOTS+ signatures of the same message that recover the same chain ends collide
at an `F` call of some chain. -/
theorem suf_wots_collision (pk : prims.PkSeed) (sig1 sig2 : WotsSig vp.params prims.core)
    (msg : prims.Y) (adrs : Adrs) (hne : sig1 ≠ sig2)
    (htops : wotsPkFromSigTops prims sig1 msg pk adrs = wotsPkFromSigTops prims sig2 msg pk adrs) :
    col_Coll pk
      (col_calls (wotsPkFromSigTopsM prims.core sig1 msg pk adrs :
        OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len)))
      (col_calls (wotsPkFromSigTopsM prims.core sig2 msg pk adrs :
        OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len))) := by
  obtain ⟨i, hi⟩ := suf_vec_exists_ne sig1 sig2 hne
  let ch : WotsSig vp.params prims.core → Fin vp.params.len →
      OracleComp (publicHashSpec prims.core) prims.Y := fun sig i =>
    chainM prims.core pk (wotsChainAdrs adrs i.val) sig[i.val]
      (chainStepsCore prims.core msg i.val) (vp.params.w - 1 - chainStepsCore prims.core msg i.val)
  have hprog : ∀ sig : WotsSig vp.params prims.core,
      (wotsPkFromSigTopsM prims.core sig msg pk adrs :
        OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len)) =
      Vector.ofFnM (ch sig) := fun sig => rfl
  have hval : ∀ sig : WotsSig vp.params prims.core, wotsPkFromSigTops prims sig msg pk adrs =
      simulateQ (PublicHash.impl prims) (Vector.ofFnM (ch sig)) := fun sig => rfl
  rw [hval sig1, hval sig2, simulateQ_ofFnM, simulateQ_ofFnM] at htops
  have hch : simulateQ (PublicHash.impl prims) (ch sig1 i) =
      simulateQ (PublicHash.impl prims) (ch sig2 i) := by
    have h1 := congrArg (fun v : Vector prims.Y vp.params.len => v[i.val]) htops
    have e : ∀ g : Fin vp.params.len → Id prims.Y,
        (Vector.ofFnM g : Id (Vector prims.Y vp.params.len)) = Vector.ofFn g := fun g =>
      Vector.idRun_ofFnM
    simp only [e] at h1
    simpa using h1
  rw [hprog sig1, hprog sig2]
  exact (suf_chain_collision pk (wotsChainAdrs adrs i.val) _ _ _ _ hi hch).mono
    (fun c hc => col_mem_ofFnM (ch sig1) i hc) (fun c hc => col_mem_ofFnM (ch sig2) i hc)

/-! ## Climbs -/

/-- Two climbs at the same index that differ in the start node or in the authentication path and
reach the same root collide at an `H` node. -/
theorem suf_climb_collision (pk : prims.PkSeed) :
    ∀ (auth1 auth2 : List prims.Y), auth1.length = auth2.length →
    ∀ (nodeAdr : ℕ → ℕ → Adrs) (idx : ℕ) (n1 n2 : prims.Y), (n1 ≠ n2 ∨ auth1 ≠ auth2) →
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
    intro auth2 hlen nodeAdr idx n1 n2 hd h
    obtain rfl : auth2 = [] := List.length_eq_zero_iff.mp hlen.symm
    rcases hd with hd | hd
    · exact absurd h hd
    · exact absurd rfl hd
  | cons a1 r1 ih =>
    intro auth2 hlen nodeAdr idx n1 n2 hd h
    obtain ⟨a2, r2, rfl⟩ : ∃ a2 r2, auth2 = a2 :: r2 := by
      cases auth2 with
      | nil => simp at hlen
      | cons a2 r2 => exact ⟨a2, r2, rfl⟩
    have hlen' : r1.length = r2.length := by simpa using hlen
    have hrest : n1 = n2 → a1 = a2 → r1 ≠ r2 := by
      intro hn ha hr
      subst hn ha hr
      rcases hd with hd | hd
      · exact hd rfl
      · exact hd rfl
    rw [PerfectMerkleTree.climbM_cons, PerfectMerkleTree.climbM_cons] at h ⊢
    rw [col_sim_bind, col_sim_bind] at h
    by_cases hpar : idx % 2 = 0
    · simp only [hpar, ite_true] at h ⊢
      rw [PublicHash.simulateQ_h, PublicHash.simulateQ_h] at h
      by_cases hp : prims.H pk (nodeAdr 1 (idx / 2)) n1 a1 = prims.H pk (nodeAdr 1 (idx / 2)) n2 a2
      · by_cases hin : n1 = n2 ∧ a1 = a2
        · refine (ih r2 hlen' (fun z t => nodeAdr (z + 1) t) (idx / 2) _ _
            (Or.inr (hrest hin.1 hin.2)) h).mono ?_ ?_
          · intro c hc
            refine col_mem_bind_right _ ?_
            rw [PublicHash.simulateQ_h]; exact hc
          · intro c hc
            refine col_mem_bind_right _ ?_
            rw [PublicHash.simulateQ_h]; exact hc
        · refine ⟨(prims.adrsToKey (nodeAdr 1 (idx / 2)), [n1, a1]),
            col_mem_bind_left _ (by rw [col_calls_h]; exact List.mem_singleton_self _),
            (prims.adrsToKey (nodeAdr 1 (idx / 2)), [n2, a2]),
            col_mem_bind_left _ (by rw [col_calls_h]; exact List.mem_singleton_self _),
            rfl, ?_, hp⟩
          intro heq
          exact hin ⟨(List.cons.inj heq).1, (List.cons.inj (List.cons.inj heq).2).1⟩
      · refine (ih r2 hlen' (fun z t => nodeAdr (z + 1) t) (idx / 2) _ _ (Or.inl hp) h).mono ?_ ?_
        · intro c hc
          refine col_mem_bind_right _ ?_
          rw [PublicHash.simulateQ_h]; exact hc
        · intro c hc
          refine col_mem_bind_right _ ?_
          rw [PublicHash.simulateQ_h]; exact hc
    · simp only [hpar, ite_false] at h ⊢
      rw [PublicHash.simulateQ_h, PublicHash.simulateQ_h] at h
      by_cases hp : prims.H pk (nodeAdr 1 (idx / 2)) a1 n1 = prims.H pk (nodeAdr 1 (idx / 2)) a2 n2
      · by_cases hin : n1 = n2 ∧ a1 = a2
        · refine (ih r2 hlen' (fun z t => nodeAdr (z + 1) t) (idx / 2) _ _
            (Or.inr (hrest hin.1 hin.2)) h).mono ?_ ?_
          · intro c hc
            refine col_mem_bind_right _ ?_
            rw [PublicHash.simulateQ_h]; exact hc
          · intro c hc
            refine col_mem_bind_right _ ?_
            rw [PublicHash.simulateQ_h]; exact hc
        · refine ⟨(prims.adrsToKey (nodeAdr 1 (idx / 2)), [a1, n1]),
            col_mem_bind_left _ (by rw [col_calls_h]; exact List.mem_singleton_self _),
            (prims.adrsToKey (nodeAdr 1 (idx / 2)), [a2, n2]),
            col_mem_bind_left _ (by rw [col_calls_h]; exact List.mem_singleton_self _),
            rfl, ?_, hp⟩
          intro heq
          exact hin ⟨(List.cons.inj (List.cons.inj heq).2).1, (List.cons.inj heq).1⟩
      · refine (ih r2 hlen' (fun z t => nodeAdr (z + 1) t) (idx / 2) _ _ (Or.inl hp) h).mono ?_ ?_
        · intro c hc
          refine col_mem_bind_right _ ?_
          rw [PublicHash.simulateQ_h]; exact hc
        · intro c hc
          refine col_mem_bind_right _ ?_
          rw [PublicHash.simulateQ_h]; exact hc

/-! ## FORS -/

/-- Two different FORS signatures recovering the same public key collide: at `T_k`, at an `H`
node, or at `F` on a revealed secret value. -/
theorem suf_fors_collision (pk : prims.PkSeed) (s1 s2 : ForsSigCore vp.params prims.core)
    (md : List Byte) (adrs : Adrs) (hne : s1 ≠ s2)
    (hpk : forsPkFromSig prims s1 md pk adrs = forsPkFromSig prims s2 md pk adrs) :
    col_Coll pk
      (col_calls (forsPkFromSigM prims.core s1 md pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y))
      (col_calls (forsPkFromSigM prims.core s2 md pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y)) := by
  obtain ⟨i, hi⟩ := suf_vec_exists_ne s1 s2 hne
  by_cases hleaf : prims.F pk
        (forsNodeAdrs adrs 0 (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val))
        (s1[i.val]).sk =
      prims.F pk (forsNodeAdrs adrs 0 (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val))
        (s2[i.val]).sk
  swap
  · exact col_fors_collision pk s1 s2 md adrs i hleaf hpk
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
  · have hvec : simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s1)) =
        simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s2)) := Vector.toList_inj.mp hroots
    rw [simulateQ_ofFnM, simulateQ_ofFnM] at hvec
    have hti : simulateQ (PublicHash.impl prims) (tree s1 i) =
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
    rw [htree s1, htree s2] at hti
    by_cases hsk : (s1[i.val]).sk = (s2[i.val]).sk
    · -- same secret value: the authentication paths differ
      have hauth : (s1[i.val]).auth.toList ≠ (s2[i.val]).auth.toList := fun h =>
        hi (suf_forsTree_ext _ _ hsk (Vector.toList_inj.mp h))
      refine (suf_climb_collision pk _ _ (by simp) _ _ _ _ (Or.inr hauth) hti).mono ?_ ?_
      · intro c hc
        refine col_mem_bind_left _ (col_mem_ofFnM (tree s1) i ?_)
        refine col_mem_bind_right _ ?_
        rw [PublicHash.simulateQ_f]; exact hc
      · intro c hc
        refine col_mem_bind_left _ (col_mem_ofFnM (tree s2) i ?_)
        refine col_mem_bind_right _ ?_
        rw [PublicHash.simulateQ_f]; exact hc
    · -- different secret values with the same image: a collision of `F` at the leaf
      refine ⟨(prims.adrsToKey (forsNodeAdrs adrs 0
            (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)), [(s1[i.val]).sk]),
        col_mem_bind_left _ (col_mem_ofFnM (tree s1) i
          (col_mem_bind_left _ (by rw [col_calls_f]; exact List.mem_singleton_self _))),
        (prims.adrsToKey (forsNodeAdrs adrs 0
            (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)), [(s2[i.val]).sk]),
        col_mem_bind_left _ (col_mem_ofFnM (tree s2) i
          (col_mem_bind_left _ (by rw [col_calls_f]; exact List.mem_singleton_self _))),
        rfl, ?_, hleaf⟩
      intro heq
      exact hsk (List.cons.inj heq).1
  · refine ⟨(prims.adrsToKey (forsPkAdrs adrs),
        (simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s1))).toList),
      col_mem_bind_right _ (by rw [col_calls_tl]; exact List.mem_singleton_self _),
      (prims.adrsToKey (forsPkAdrs adrs),
        (simulateQ (PublicHash.impl prims) (Vector.ofFnM (tree s2))).toList),
      col_mem_bind_right _ (by rw [col_calls_tl]; exact List.mem_singleton_self _),
      rfl, hroots, hpk⟩

/-! ## XMSS -/

/-- Two different XMSS signatures of the same message at the same leaf recovering the same root
collide: at an `F` call of a chain, at `T_len`, or at an `H` node. -/
theorem suf_xmss_collision (pk : prims.PkSeed) (idx : ℕ)
    (g1 g2 : XmssSig vp.params prims.core) (m : prims.Y) (adrs : Adrs) (hne : g1 ≠ g2)
    (hroot : xmssPkFromSig prims idx g1 m pk adrs = xmssPkFromSig prims idx g2 m pk adrs) :
    col_Coll pk
      (col_calls (xmssPkFromSigM prims.core idx g1 m pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y))
      (col_calls (xmssPkFromSigM prims.core idx g2 m pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y)) := by
  by_cases htops : wotsPkFromSigTops prims g1.wots m pk (wotsLeafAdrs adrs idx) =
      wotsPkFromSigTops prims g2.wots m pk (wotsLeafAdrs adrs idx)
  swap
  · exact col_xmss_collision pk idx g1 g2 m m adrs htops hroot
  have hprog : ∀ (g : XmssSig vp.params prims.core),
      (xmssPkFromSigM prims.core idx g m pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y) =
      ((wotsPkFromSigTopsM prims.core g.wots m pk (wotsLeafAdrs adrs idx) :
          OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len)) >>= fun tops =>
        PublicHash.tl prims.core pk (wotsPkAdrs (wotsLeafAdrs adrs idx)) tops.toList) >>=
      fun leaf => PerfectMerkleTree.climbM
        (fun z t l r => PublicHash.h prims.core pk (xmssNodeAdrs adrs z t) l r) idx leaf
        g.auth.toList := fun g => rfl
  have hleaf : ∀ (g : XmssSig vp.params prims.core),
      simulateQ (PublicHash.impl prims)
        ((wotsPkFromSigTopsM prims.core g.wots m pk (wotsLeafAdrs adrs idx) :
          OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len)) >>= fun tops =>
        PublicHash.tl prims.core pk (wotsPkAdrs (wotsLeafAdrs adrs idx)) tops.toList) =
      prims.Tl pk (wotsPkAdrs (wotsLeafAdrs adrs idx))
        (wotsPkFromSigTops prims g.wots m pk (wotsLeafAdrs adrs idx)).toList := by
    intro g
    rw [col_sim_bind, PublicHash.simulateQ_tl]
    rfl
  have hval : ∀ (g : XmssSig vp.params prims.core),
      xmssPkFromSig prims idx g m pk adrs =
        simulateQ (PublicHash.impl prims)
          (PerfectMerkleTree.climbM
            (fun z t l r => PublicHash.h prims.core pk (xmssNodeAdrs adrs z t) l r) idx
            (prims.Tl pk (wotsPkAdrs (wotsLeafAdrs adrs idx))
              (wotsPkFromSigTops prims g.wots m pk (wotsLeafAdrs adrs idx)).toList)
            g.auth.toList : OracleComp (publicHashSpec prims.core) prims.Y) := by
    intro g
    show simulateQ (PublicHash.impl prims) (xmssPkFromSigM prims.core idx g m pk adrs :
      OracleComp (publicHashSpec prims.core) prims.Y) = _
    rw [hprog, col_sim_bind, hleaf]
  rw [hprog g1, hprog g2]
  by_cases hw : g1.wots = g2.wots
  · -- same WOTS+ signature: the authentication paths differ
    have hauth : g1.auth.toList ≠ g2.auth.toList := fun h =>
      hne (suf_xmssSig_ext _ _ hw (Vector.toList_inj.mp h))
    rw [hval g1, hval g2] at hroot
    refine (suf_climb_collision pk _ _ (by simp) _ _ _ _ (Or.inr hauth) hroot).mono ?_ ?_
    · intro c hc
      refine col_mem_bind_right _ ?_
      rw [hleaf]; exact hc
    · intro c hc
      refine col_mem_bind_right _ ?_
      rw [hleaf]; exact hc
  · -- different WOTS+ signatures of the same message with the same chain ends
    exact (suf_wots_collision pk g1.wots g2.wots m (wotsLeafAdrs adrs idx) hw htops).mono
      (fun c hc => col_mem_bind_left _ (col_mem_bind_left _ hc))
      (fun c hc => col_mem_bind_left _ (col_mem_bind_left _ hc))

/-! ## The two-signature statement -/

section Main

variable [DecidableEq prims.Y]

/-- **Two different signatures with the same randomizer.**  If `sig ≠ ref` have the same
randomizer and both verify for `msg` under `pk`, then either some hypertree layer WOTS+-signs
different messages with the same recovered chain ends, or the two verifications make hash calls
at the same tweak on different inputs with the same output. -/
theorem sameRandomizer_collision (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig ref : GeneralScheme.SignatureCore vp prims.core)
    (hR : ref.randomness = sig.randomness) (hne : sig ≠ ref)
    (hv : GeneralScheme.verifyInternal vp prims msg sig pk = true)
    (hv' : GeneralScheme.verifyInternal vp prims msg ref pk = true) :
    (wotsLayer? pk (digestParts pk sig.randomness msg) sig ref).isSome = true ∨
      col_Coll pk.pkSeed (verifyCalls pk msg sig) (verifyCalls pk msg ref) := by
  have hdiff : sig.fors ≠ ref.fors ∨ sig.hypertree ≠ ref.hypertree := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hne (suf_sig_ext _ _ hR.symm hcon.1 hcon.2)
  rw [GeneralScheme.verifyInternal_eq_decide] at hv hv'
  have h1 := of_decide_eq_true hv
  have h2 := of_decide_eq_true hv'
  rw [hR] at h2
  have hroot : GeneralHypertree.pkFromSig vp prims
        (forsPkFromSig prims sig.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs)
        sig.hypertree pk.pkSeed (digestParts pk sig.randomness msg) =
      GeneralHypertree.pkFromSig vp prims
        (forsPkFromSig prims ref.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs)
        ref.hypertree pk.pkSeed (digestParts pk sig.randomness msg) := h1.trans h2.symm
  rw [col_verifyCalls_eq, col_verifyCalls_eq, hR]
  generalize digestParts pk sig.randomness msg = parts at hroot ⊢
  obtain ⟨hF, hcF⟩ := col_pkFromSig pk.pkSeed parts sig.hypertree
    (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs)
  obtain ⟨hH, hcH⟩ := col_pkFromSig pk.pkSeed parts ref.hypertree
    (forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs)
  rw [hF, hH] at hroot
  by_cases hall : ∀ j, j ≤ vp.params.d →
      layerMsg pk.pkSeed parts sig.hypertree
          (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs) j =
        layerMsg pk.pkSeed parts ref.hypertree
          (forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs) j
  · -- all layer messages agree
    right
    have h0 : forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs =
        forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs :=
      hall 0 (Nat.zero_le _)
    rcases hdiff with hf | hh
    · exact (suf_fors_collision pk.pkSeed sig.fors ref.fors parts.md.toList parts.forsAdrs hf
        h0).mono (fun c hc => List.mem_append_left _ hc) (fun c hc => List.mem_append_left _ hc)
    · obtain ⟨j, hj⟩ := suf_vec_exists_ne sig.hypertree ref.hypertree hh
      have hmj := hall j.val (le_of_lt j.isLt)
      have hsucc := hall (j.val + 1) j.isLt
      rw [col_layerMsg_succ pk.pkSeed parts _ _ j, col_layerMsg_succ pk.pkSeed parts _ _ j]
        at hsucc
      have hprogH : col_layerProg pk.pkSeed parts ref.hypertree
            (forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs) j =
          xmssPkFromSigM prims.core (LayerPosition.atLayer vp parts j).leaf.val
            ref.hypertree[j.val]
            (layerMsg pk.pkSeed parts sig.hypertree
              (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs) j.val)
            pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs := by
        unfold col_layerProg
        rw [hmj]
      rw [hprogH] at hsucc
      have hc := suf_xmss_collision pk.pkSeed (LayerPosition.atLayer vp parts j).leaf.val
        sig.hypertree[j.val] ref.hypertree[j.val]
        (layerMsg pk.pkSeed parts sig.hypertree
          (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs) j.val)
        (LayerPosition.atLayer vp parts j).toAdrs hj hsucc
      exact hc.mono (fun c hc => List.mem_append_right _ (hcF j c hc))
        (fun c hc => List.mem_append_right _ (hcH j c (by rw [hprogH]; exact hc)))
  · -- some layer message differs
    push Not at hall
    obtain ⟨j0, hj0, hne0⟩ := hall
    obtain ⟨j, hj, hnej, heq⟩ := suf_meet
      (layerMsg pk.pkSeed parts sig.hypertree
        (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs))
      (layerMsg pk.pkSeed parts ref.hypertree
        (forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs))
      vp.params.d j0 hj0 hne0 hroot
    by_cases htops : layerTops pk.pkSeed parts sig.hypertree
          (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs) ⟨j, hj⟩ =
        layerTops pk.pkSeed parts ref.hypertree
          (forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs) ⟨j, hj⟩
    · left
      unfold wotsLayer?
      dsimp only
      rw [List.find?_isSome]
      exact ⟨⟨j, hj⟩, List.mem_finRange _, decide_eq_true ⟨hnej, htops⟩⟩
    · right
      have hsucc := heq
      rw [col_layerMsg_succ pk.pkSeed parts _ _ ⟨j, hj⟩,
        col_layerMsg_succ pk.pkSeed parts _ _ ⟨j, hj⟩] at hsucc
      exact (col_xmss_collision pk.pkSeed _ _ _ _ _ _ htops hsucc).mono
        (fun c hc => List.mem_append_right _ (hcF ⟨j, hj⟩ c hc))
        (fun c hc => List.mem_append_right _ (hcH ⟨j, hj⟩ c hc))

end Main

end Reduction

#print axioms Reduction.sameRandomizer_collision

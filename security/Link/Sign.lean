import Link.SignParts

/-!
# Signing (FIPS 205 Algorithms 12 and 19): `Spec` = VCVio
-/

namespace Link

open SLHDSA SLHDSA.Concrete

/-- One layer of the fold in `Spec.htSign`. -/
private def htSignStep (sk pk : Spec.Bytes) (st : Spec.Bytes × Spec.Bytes × Nat × Nat) (j : Nat) :
    Spec.Bytes × Spec.Bytes × Nat × Nat :=
  let (sig, root, tree, leaf) := st
  let adrs := { Spec.Adrs.zero with layer := j, tree := tree }
  let s := Spec.xmssSign root sk leaf pk adrs
  (sig ++ s, Spec.xmssPkFromSig leaf s root pk adrs, tree >>> Spec.hp, tree % 2 ^ Spec.hp)

/-- The signing walk of `Spec.htSign` as a recursion on the number of remaining layers. -/
private def htSignGo (sk pk : Spec.Bytes) : Nat → Nat → Spec.Bytes → Nat → Nat → Spec.Bytes
  | 0, _, _, _, _ => []
  | n + 1, j, root, tree, leaf =>
    let adrs := { Spec.Adrs.zero with layer := j, tree := tree }
    let s := Spec.xmssSign root sk leaf pk adrs
    s ++ htSignGo sk pk n (j + 1) (Spec.xmssPkFromSig leaf s root pk adrs)
      (tree >>> Spec.hp) (tree % 2 ^ Spec.hp)

private theorem foldl_htSignStep (sk pk : Spec.Bytes) :
    ∀ (n j : Nat) (sig root : Spec.Bytes) (tree leaf : Nat),
      ((List.range' j n).foldl (htSignStep sk pk) (sig, root, tree, leaf)).1 =
        sig ++ htSignGo sk pk n j root tree leaf := by
  intro n
  induction n with
  | zero => intro j sig root tree leaf; simp [htSignGo]
  | succ n ih =>
    intro j sig root tree leaf
    simp only [List.range'_succ, List.foldl_cons, htSignGo]
    rw [htSignStep, ih, List.append_assoc]

private theorem htSign_eq_go (msg sk pk : Spec.Bytes) (t l : Nat) :
    Spec.htSign msg sk pk t l = htSignGo sk pk Spec.d 0 msg t l := by
  have := foldl_htSignStep sk pk Spec.d 0 [] msg t l
  rw [← List.range_eq_range', List.nil_append] at this
  exact this

private theorem signFrom_eq (sk pk : Node) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : Node),
      (GeneralHypertree.signFromPosition vp prims sk pk false pos layers h msg).toList.flatMap
          xmssBytes =
        htSignGo (nd sk) (nd pk) layers pos.layer.val (nd msg) pos.tree.val pos.leaf.val := by
  have hdom : ∀ (pos : LayerPosition vp), BaseDom pos.toAdrs := by
    intro pos
    have hl : pos.layer.val < 7 := pos.layer.isLt
    have ht : pos.tree.val < 2 ^ 64 := by
      have h1 := pos.tree.isLt
      have h2 : layerTreeHeight vp pos.layer.val ≤ 64 := by
        simp only [layerTreeHeight]
        show (7 - (pos.layer.val + 1)) * 9 ≤ 64
        omega
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)
    exact ⟨by show pos.layer.val < 256; omega, ht⟩
  have hx : ∀ (pos : LayerPosition vp) (s : XmssSig vp.params prims.core) (msg : Node),
      nd (SLHDSA.xmssPkFromSig prims pos.leaf.val s msg pk pos.toAdrs) =
        Spec.xmssPkFromSig pos.leaf.val (xmssBytes s) (nd msg) (nd pk)
          { Spec.Adrs.zero with layer := pos.layer.val, tree := pos.tree.val } :=
    fun pos s msg => xmssPkFromSig_eq pos.leaf.val pos.leaf.isLt s msg pk pos.toAdrs (hdom pos)
  have hs : ∀ (pos : LayerPosition vp) (msg : Node),
      xmssBytes (SLHDSA.xmssSign prims msg sk pk pos.toAdrs pos.leaf.val) =
        Spec.xmssSign (nd msg) (nd sk) pos.leaf.val (nd pk)
          { Spec.Adrs.zero with layer := pos.layer.val, tree := pos.tree.val } :=
    fun pos msg => xmssSign_eq msg sk pk pos.toAdrs (hdom pos) pos.leaf.val pos.leaf.isLt
  intro layers
  induction layers using Nat.strong_induction_on with
  | _ layers ih =>
    intro pos h msg
    match layers, h with
    | 0, h => simp [GeneralHypertree.signFromPosition, htSignGo]
    | 1, h =>
      simp only [GeneralHypertree.signFromPosition, htSignGo]
      simp only [Bool.false_eq_true, ite_false, Vector.toList_mk, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact hs pos msg
    | layers + 2, h =>
      simp only [GeneralHypertree.signFromPosition]
      rw [htSignGo]
      have hins : ∀ (v : Vector (XmssSig vp.params prims.core) (layers + 1))
          (s : XmssSig vp.params prims.core),
          (v.insertIdx 0 s).toList = s :: v.toList := by
        intro v s
        rcases v with ⟨⟨l⟩, hl⟩
        simp [Vector.insertIdx]
      rw [hins, List.flatMap_cons]
      refine congrArg₂ (· ++ ·) (hs pos msg) ?_
      refine (ih (layers + 1) (by omega) _ _ _).trans ?_
      rw [hx, hs]
      simp [LayerPosition.next, Nat.shiftRight_eq_div_pow, Spec.hp]
      rfl

/-- Algorithm 12, `ht_sign`. -/
theorem htSign_eq (msg sk pk : Node) (parts : DigestParts vp.params) :
    htBytes (GeneralHypertree.sign vp prims msg sk pk parts) =
      Spec.htSign (nd msg) (nd sk) (nd pk) parts.idxTree.val parts.idxLeaf.val := by
  rw [htSign_eq_go, htBytes]
  refine (congrArg (fun v : HtSigCore vp.params prims.core => v.toList.flatMap xmssBytes)
    (GeneralHypertree.sign_eq_signFromPosition vp prims msg sk pk parts)).trans ?_
  exact signFrom_eq sk pk vp.params.d (LayerPosition.initial vp parts) (by simp) msg

private theorem signWithRandomizer_eq (msg : List Byte) (skSeed pkSeed pkRoot R : Node) :
    GeneralScheme.signInternalWithRandomizer vp prims msg skSeed pkSeed pkRoot R =
      (let parts := splitDigest vp.params (prims.Hmsg R pkSeed pkRoot msg)
       let forsSig := forsSign prims parts.md.toList skSeed pkSeed parts.forsAdrs
       ⟨R, forsSig,
        GeneralHypertree.sign vp prims
          (forsPkFromSig prims forsSig parts.md.toList pkSeed parts.forsAdrs)
          skSeed pkSeed parts⟩) := by
  unfold GeneralScheme.signInternalWithRandomizer GeneralScheme.signInternalWithRandomizerM
    GeneralHypertree.sign forsSign forsPkFromSig
  simp only [simulateQ_bind]
  rfl

/-- FIPS 205 Algorithm 19, `slh_sign_internal`, with `opt_rand = addrnd`. -/
theorem sign_eq (msg : Spec.Bytes) (sk : SecretKeyCore prims.core) (addrnd : Node) :
    Spec.slhSignInternal msg (skBytes sk) (nd addrnd) =
      sigBytes (GeneralScheme.signInternal vp prims (cv msg) sk addrnd) := by
  have hb0 : Spec.block (skBytes sk) 0 = nd sk.skSeed := by
    simp only [Spec.block, skBytes, Nat.zero_mul, List.drop_zero, List.append_assoc]
    exact List.take_left' (nd_length _)
  have hb1 : Spec.block (skBytes sk) 1 = nd sk.skPrf := by
    simp only [Spec.block, skBytes, Nat.one_mul, List.append_assoc]
    exact (congrArg (List.take _) (List.drop_left' (nd_length _))).trans
      (List.take_left' (nd_length _))
  have hb2 : Spec.block (skBytes sk) 2 = nd sk.pkSeed := by
    simp only [Spec.block, skBytes, List.append_assoc]
    rw [← List.append_assoc (nd sk.skSeed)]
    exact (congrArg (List.take _) (List.drop_left' (List.length_append.trans
      (congrArg₂ (· + ·) (nd_length _) (nd_length _))))).trans (List.take_left' (nd_length _))
  have hb3 : Spec.block (skBytes sk) 3 = nd sk.pkRoot := by
    simp only [Spec.block, skBytes]
    exact (congrArg (List.take _) (List.drop_left' (List.length_append.trans
      (congrArg₂ (· + ·) (List.length_append.trans
        (congrArg₂ (· + ·) (nd_length _) (nd_length _))) (nd_length _))))).trans
      (List.take_of_length_le (Nat.le_of_eq (nd_length _)))
  have hR : Spec.PRFmsg (nd sk.skPrf) (nd addrnd) msg =
      nd (prims.PRFmsg sk.skPrf addrnd (cv msg)) :=
    ((PRFmsg_eq _ _ _).trans (congrArg (Spec.PRFmsg _ _) (sp_cv msg))).symm
  refine Eq.trans ?_ (congrArg sigBytes (signWithRandomizer_eq (cv msg) sk.skSeed sk.pkSeed
    sk.pkRoot (prims.PRFmsg sk.skPrf addrnd (cv msg))).symm)
  generalize hRR : prims.PRFmsg sk.skPrf addrnd (cv msg) = R at hR ⊢
  have hdg : sp (prims.Hmsg R sk.pkSeed sk.pkRoot (cv msg)).toList =
      Spec.Hmsg (nd R) (nd sk.pkSeed) (nd sk.pkRoot) msg :=
    (Hmsg_eq _ _ _ _).trans (congrArg (Spec.Hmsg _ _ _) (sp_cv msg))
  generalize hdig : prims.Hmsg R sk.pkSeed sk.pkRoot (cv msg) = dg at hdg
  unfold Spec.slhSignInternal
  simp only [hb0, hb1, hb2, hb3, hR, ← hdg]
  generalize hparts : splitDigest vp.params dg = parts
  have hmd : sp parts.md.toList = (sp dg.toList).take Spec.mdBytes := by
    rw [← hparts, splitDigest_md_toList, sp_take]; rfl
  have ht : parts.idxTree.val = Spec.digestTree (sp dg.toList) := by
    rw [← hparts, splitDigest_idxTree_val, toInt_eq, sp_take, sp_drop]; rfl
  have hl : parts.idxLeaf.val = Spec.digestLeaf (sp dg.toList) := by
    rw [← hparts, splitDigest_idxLeaf_val, toInt_eq, sp_take, sp_drop]; rfl
  have htlt : parts.idxTree.val < 2 ^ 54 := parts.idxTree.isLt
  have hllt : parts.idxLeaf.val < 2 ^ 9 := parts.idxLeaf.isLt
  have hdom : ForsDom parts.forsAdrs :=
    ⟨rfl, by show (0 : ℕ) < 256; omega,
     by show parts.idxTree.val < 2 ^ 64; omega, by show parts.idxLeaf.val < 2 ^ 32; omega⟩
  have hadr : adr parts.forsAdrs =
      specForsAdrs (Spec.digestTree (sp dg.toList)) (Spec.digestLeaf (sp dg.toList)) := by
    rw [← ht, ← hl]; rfl
  have hfs := forsSign_eq parts.md.toList Vector.length_toList sk.skSeed sk.pkSeed
    parts.forsAdrs hdom
  have hfp := forsPkFromSig_eq
    (forsSign prims parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs) parts.md.toList
    Vector.length_toList sk.pkSeed parts.forsAdrs hdom
  have hht := htSign_eq
    (forsPkFromSig prims (forsSign prims parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs)
      parts.md.toList sk.pkSeed parts.forsAdrs) sk.skSeed sk.pkSeed parts
  rw [hfp, hfs, hmd, hadr, ht, hl] at hht
  rw [hmd, hadr] at hfs
  show _ = nd R ++ forsBytes _ ++ htBytes _
  exact congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl hfs.symm) hht.symm

end Link

#print axioms Link.htSign_eq
#print axioms Link.sign_eq

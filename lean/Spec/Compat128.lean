import Spec.Old128

/-!
# The generic specification at SLH-DSA-SHA2-128s is the single-set one

Every function of `Spec` (FIPS 205 for any SHA-2 parameter set), applied to
`Spec.sha2_128s`, equals the function of the same name in `Spec128`, the
verbatim copy of the specification of the single-set tree (git `26aa3d8`; see
`Spec/Old128.lean`). So a theorem stated against `Spec.f Spec.sha2_128s` is the
same theorem as one stated against that tree's `Spec.f`.
-/

namespace Spec128

open Spec (sha2_128s)

/-! ## Constants -/

@[simp] theorem n_eq : sha2_128s.n = n := rfl
@[simp] theorem h_eq : sha2_128s.h = h := rfl
@[simp] theorem d_eq : sha2_128s.d = d := rfl
@[simp] theorem hp_eq : sha2_128s.hp = hp := rfl
@[simp] theorem a_eq : sha2_128s.a = a := rfl
@[simp] theorem k_eq : sha2_128s.k = k := rfl
@[simp] theorem lgw_eq : sha2_128s.lgw = lgw := rfl
@[simp] theorem m_eq : sha2_128s.m = m := rfl
@[simp] theorem w_eq : sha2_128s.w = w := rfl
@[simp] theorem len1_eq : sha2_128s.len1 = len1 := by decide
@[simp] theorem len2_eq : sha2_128s.len2 = len2 := by decide
@[simp] theorem len_eq : sha2_128s.len = len := by decide
@[simp] theorem mdBytes_eq : sha2_128s.mdBytes = mdBytes := rfl
@[simp] theorem treeBytes_eq : sha2_128s.treeBytes = treeBytes := rfl
@[simp] theorem leafBytes_eq : sha2_128s.leafBytes = leafBytes := rfl
@[simp] theorem xmssSigBytes_eq : sha2_128s.xmssSigBytes = xmssSigBytes := by
  simp [Spec.Params.xmssSigBytes, xmssSigBytes]
@[simp] theorem forsSigBytes_eq : sha2_128s.forsSigBytes = forsSigBytes := rfl
@[simp] theorem sigBytes_eq : sha2_128s.sigBytes = sigBytes := by
  simp [Spec.Params.sigBytes, sigBytes]

/-! ## Hash functions -/

theorem block_eq : Spec.block sha2_128s = block := rfl
theorem F_eq : Spec.F sha2_128s = F := rfl
theorem PRF_eq : Spec.PRF sha2_128s = PRF := rfl
theorem H_eq : Spec.H sha2_128s = H := by
  funext pk adrs msg; simp [Spec.H, H, thash, n]
theorem T_eq : Spec.T sha2_128s = T := by
  funext pk adrs msg; simp [Spec.T, T, thash, n]
theorem PRFmsg_eq : Spec.PRFmsg sha2_128s = PRFmsg := by
  funext sk r msg; simp [Spec.PRFmsg, PRFmsg, n]
theorem mgf1_eq (seed : Spec.Bytes) (l : Nat) : Spec.mgf1 Spec.sha256 32 seed l = mgf1 seed l := by
  simp only [Spec.mgf1, mgf1, show l + 32 - 1 = l + 31 by omega]
theorem Hmsg_eq : Spec.Hmsg sha2_128s = Hmsg := by
  funext r pkSeed pkRoot msg; simp [Spec.Hmsg, Hmsg, mgf1_eq, n]

/-! ## WOTS+, XMSS, hypertree, FORS -/

theorem chain_eq : Spec.chain sha2_128s = chain := by
  funext x i s pkSeed adrs; simp only [Spec.chain, chain, F_eq]
theorem wotsDigits_eq : Spec.wotsDigits sha2_128s = wotsDigits := by
  funext msg; simp only [Spec.wotsDigits, wotsDigits, lgw_eq, len1_eq, len2_eq, w_eq]
theorem wotsPkGen_eq : Spec.wotsPkGen sha2_128s = wotsPkGen := by
  funext skSeed pkSeed adrs
  simp only [Spec.wotsPkGen, wotsPkGen, len_eq, w_eq, PRF_eq, chain_eq, T_eq, Spec.wotsSkAdrs,
    wotsSkAdrs, Spec.wotsPkAdrs, wotsPkAdrs]
theorem wotsSign_eq : Spec.wotsSign sha2_128s = wotsSign := by
  funext msg skSeed pkSeed adrs
  simp only [Spec.wotsSign, wotsSign, len_eq, PRF_eq, chain_eq, wotsDigits_eq, Spec.wotsSkAdrs,
    wotsSkAdrs]
theorem wotsPkFromSig_eq : Spec.wotsPkFromSig sha2_128s = wotsPkFromSig := by
  funext sig msg pkSeed adrs
  simp only [Spec.wotsPkFromSig, wotsPkFromSig, len_eq, w_eq, chain_eq, wotsDigits_eq, T_eq,
    block_eq, Spec.wotsPkAdrs, wotsPkAdrs]

theorem xmssNode_eq : Spec.xmssNode sha2_128s = xmssNode := by
  funext skSeed i z pkSeed adrs
  induction z generalizing i with
  | zero => simp only [Spec.xmssNode, xmssNode, wotsPkGen_eq]
  | succ z ih => simp only [Spec.xmssNode, xmssNode, ih, H_eq]
theorem xmssSign_eq : Spec.xmssSign sha2_128s = xmssSign := by
  funext msg skSeed idx pkSeed adrs
  simp only [Spec.xmssSign, xmssSign, hp_eq, xmssNode_eq, wotsSign_eq]
theorem climb_eq : Spec.climb sha2_128s = climb := by
  funext node idx treeIdx auth height pkSeed adrs
  simp only [Spec.climb, climb, H_eq, block_eq]
theorem xmssPkFromSig_eq : Spec.xmssPkFromSig sha2_128s = xmssPkFromSig := by
  funext idx sig msg pkSeed adrs
  simp only [Spec.xmssPkFromSig, xmssPkFromSig, len_eq, n_eq, hp_eq, wotsPkFromSig_eq, climb_eq]
theorem htSign_eq : Spec.htSign sha2_128s = htSign := by
  funext msg skSeed pkSeed idxTree idxLeaf
  simp only [Spec.htSign, htSign, d_eq, hp_eq, xmssSign_eq, xmssPkFromSig_eq]
theorem htVerify_eq : Spec.htVerify sha2_128s = htVerify := by
  funext msg sig pkSeed idxTree idxLeaf pkRoot
  simp only [Spec.htVerify, htVerify, d_eq, hp_eq, xmssSigBytes_eq, xmssPkFromSig_eq]
theorem forsSkGen_eq : Spec.forsSkGen sha2_128s = forsSkGen := by
  funext skSeed pkSeed adrs idx; simp only [Spec.forsSkGen, forsSkGen, PRF_eq]
theorem forsNode_eq : Spec.forsNode sha2_128s = forsNode := by
  funext skSeed i z pkSeed adrs
  induction z generalizing i with
  | zero => simp only [Spec.forsNode, forsNode, F_eq, forsSkGen_eq]
  | succ z ih => simp only [Spec.forsNode, forsNode, ih, H_eq]
theorem forsSign_eq : Spec.forsSign sha2_128s = forsSign := by
  funext md skSeed pkSeed adrs
  simp only [Spec.forsSign, forsSign, a_eq, k_eq, forsSkGen_eq, forsNode_eq]
theorem forsPkFromSig_eq : Spec.forsPkFromSig sha2_128s = forsPkFromSig := by
  funext sig md pkSeed adrs
  simp only [Spec.forsPkFromSig, forsPkFromSig, a_eq, k_eq, n_eq, block_eq, F_eq, climb_eq, T_eq]

/-! ## SLH-DSA -/

theorem digestTree_eq : Spec.digestTree sha2_128s = digestTree := by
  funext x; simp only [Spec.digestTree, digestTree, mdBytes_eq, treeBytes_eq, h_eq, d_eq]
theorem digestLeaf_eq : Spec.digestLeaf sha2_128s = digestLeaf := by
  funext x; simp only [Spec.digestLeaf, digestLeaf, mdBytes_eq, treeBytes_eq, leafBytes_eq,
    h_eq, d_eq]

theorem slhKeygenInternal_eq : Spec.slhKeygenInternal sha2_128s = slhKeygenInternal := by
  funext skSeed skPrf pkSeed
  simp only [Spec.slhKeygenInternal, slhKeygenInternal, d_eq, hp_eq, xmssNode_eq]
theorem slhSignInternal_eq : Spec.slhSignInternal sha2_128s = slhSignInternal := by
  funext msg sk addrnd
  simp only [Spec.slhSignInternal, slhSignInternal, block_eq, PRFmsg_eq, Hmsg_eq, mdBytes_eq,
    digestTree_eq, digestLeaf_eq, forsSign_eq, forsPkFromSig_eq, htSign_eq]
theorem slhVerifyInternal_eq : Spec.slhVerifyInternal sha2_128s = slhVerifyInternal := by
  funext msg sig pk
  simp only [Spec.slhVerifyInternal, slhVerifyInternal, sigBytes_eq, block_eq, n_eq,
    forsSigBytes_eq, Hmsg_eq, mdBytes_eq, digestTree_eq, digestLeaf_eq, forsPkFromSig_eq,
    htVerify_eq]
theorem slhSign_eq : Spec.slhSign sha2_128s = slhSign := by
  funext msg ctx sk addrnd; simp only [Spec.slhSign, slhSign, slhSignInternal_eq]
theorem slhVerify_eq : Spec.slhVerify sha2_128s = slhVerify := by
  funext msg sig ctx pk; simp only [Spec.slhVerify, slhVerify, slhVerifyInternal_eq]

/-! ## The checked signer -/

theorem forsPkGen_eq : Spec.forsPkGen sha2_128s = forsPkGen := by
  funext skSeed pkSeed adrs; simp only [Spec.forsPkGen, forsPkGen, k_eq, a_eq, forsNode_eq, T_eq]
theorem htCheckedStep_eq : Spec.htCheckedStep sha2_128s = htCheckedStep := by
  funext skSeed pkSeed pkRoot st j
  simp only [Spec.htCheckedStep, htCheckedStep, xmssSign_eq, xmssPkFromSig_eq, d_eq, xmssNode_eq,
    hp_eq]
theorem htSignChecked_eq : Spec.htSignChecked sha2_128s = htSignChecked := by
  funext mA mB skSeed pkSeed idxTree idxLeaf pkRoot
  simp only [Spec.htSignChecked, htSignChecked, d_eq, htCheckedStep_eq]
theorem slhSignInternalChecked_eq : Spec.slhSignInternalChecked sha2_128s = slhSignInternalChecked := by
  funext msg sk addrnd
  simp only [Spec.slhSignInternalChecked, slhSignInternalChecked, block_eq, PRFmsg_eq, Hmsg_eq,
    mdBytes_eq, digestTree_eq, digestLeaf_eq, forsSign_eq, forsPkFromSig_eq, forsPkGen_eq,
    htSignChecked_eq]
theorem slhSignChecked_eq : Spec.slhSignChecked sha2_128s = slhSignChecked := by
  funext msg ctx sk addrnd; simp only [Spec.slhSignChecked, slhSignChecked, slhSignInternalChecked_eq]
theorem KeyOk_eq : Spec.KeyOk sha2_128s = KeyOk := by
  funext sk; simp only [Spec.KeyOk, KeyOk, block_eq, xmssNode_eq, hp_eq, d_eq]
theorem skPk_eq : Spec.skPk sha2_128s = skPk := rfl

end Spec128

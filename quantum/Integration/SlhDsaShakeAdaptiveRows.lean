import Integration.SlhDsaShakeSignatureItsr
import Integration.SlhDsaShakeXofRows
import Integration.SlhDsaSetItsr

namespace Reduction.ShakeAdaptive
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum QMsg QItsr KeyedHash
open scoped ComplexOrder Kronecker ENNReal
open Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeApi.primitives ShakeSecurity.primitives

abbrev Row (S : Sha2Set) (c : Caps) := S.Node × (S.Node × S.Node × BList SLHDSA.Byte c.ml)

def expand (S : Sha2Set) (c : Caps) (z : Row S c) : ShakeSingle.Query S :=
  (z.1,z.2.1,z.2.2.1,List.ofFn z.2.2.2.2)

def embedding (S : Sha2Set) (c : Caps) {N : ℕ} (cap : 3*S.vp.params.n+c.ml ≤ N) :
    Row S c ↪ ShakeApi.Input N where
  toFun z := BList.ofList (ShakeSingle.encode S (expand S c z)) (by
    simp only [ShakeSingle.encode,expand,List.length_append,Vector.length_toList,List.length_ofFn]
    have := z.2.2.2.1.isLt
    omega)
  inj' := by
    intro a b h
    have he := congrArg (fun x : ShakeApi.Input N => List.ofFn x.2) h
    have e := ShakeSingle.encode_injective S (by simpa only [BList.ofFn_ofList] using he)
    rcases a with ⟨r,p,t,m⟩
    rcases b with ⟨r',p',t',m'⟩
    change (r,p,t,List.ofFn m.2) = (r',p',t',List.ofFn m'.2) at e
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl,rfl,rfl,hm⟩ := e
    have inv (v : BList SLHDSA.Byte c.ml) : cutB c (List.ofFn v.2) = v :=
      (cutB_of c _ (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ v.1.isLt)).trans (BList.ofList_ofFn ..)
    exact congrArg (fun v => (r,p,t,v)) ((inv m).symm.trans ((congrArg (cutB c) hm).trans (inv m')))

theorem eval_row (S : Sha2Set) (c : Caps) {N : ℕ} (cap : 3*S.vp.params.n+c.ml ≤ N)
    (g : ShakeApi.RawTable S N) (H : Row S c → Bytes S.vp.params.m) (R : S.Node)
    (x : S.Node × S.Node × List SLHDSA.Byte) (hx : x.2.2.length ≤ c.ml) :
    (itsrProblem S.vp (ShakeApi.primitives S (ShakeApi.extend (ShakeXof.write (embedding S c cap) g H)))).khf.hash R x =
      H (R,SetOracle.tg S c x) := by
  let j := (R,SetOracle.tg S c x)
  have eq : expand S c j = (R,x) := by
    rcases x with ⟨p,t,m⟩
    change (R,p,t,List.ofFn (cutB c m).2) = (R,p,t,m)
    exact congrArg (fun v => (R,p,t,v)) ((congrArg (fun k : BList SLHDSA.Byte c.ml => List.ofFn k.2) (cutB_of c m hx)).trans (BList.ofFn_ofList ..))
  have hp : (ShakeSingle.encode S (R,x)).length ≤ N := by
    simp only [ShakeSingle.encode,List.length_append,Vector.length_toList]
    omega
  have inp : BList.ofList (ShakeSingle.encode S (R,x)) hp = embedding S c cap j := by
    change _ = BList.ofList (ShakeSingle.encode S (expand S c j)) (by simpa only [eq] using hp)
    simp only [eq]
  change ShakeApi.extend _ (R.toList ++ x.1.toList ++ x.2.1.toList ++ x.2.2) = _
  simp only [List.append_assoc]
  change ShakeApi.extend _ (ShakeSingle.encode S (R,x)) = H j
  rw [ShakeApi.extend_apply _ _ hp,inp]
  simp only [ShakeXof.write,ShakeXof.locate_emb,Option.elim_some]
  ext i hi
  simp [ShakeXof.replaceHead]

theorem win_conv (S : Sha2Set) (c : Caps) {N : ℕ} (cap : 3*S.vp.params.n+c.ml ≤ N) (g : ShakeApi.RawTable S N) (Hf : S.Node × (S.Node × S.Node × BList SLHDSA.Byte c.ml) → (Bytes S.vp.params.m)) {s : ℕ} (Rs : Fin s → S.Node)
    (cand : S.Node × (S.Node × S.Node × List SLHDSA.Byte)) (t : List (S.Node × S.Node × List SLHDSA.Byte))
    (hcand : cand.2.2.2.length ≤ c.ml) (ht : ∀ y ∈ t, y.2.2.length ≤ c.ml) (hlen : t.length ≤ s)
    (hw : (itsrProblem S.vp (ShakeApi.primitives S (ShakeApi.extend (ShakeXof.write (embedding S c cap) g Hf)))).Wins (pairs Rs 0 t) cand) :
    itsrAWin (SetDigest.idxCov S.vp) Rs Hf (⟨QReg.of Unit, ((cand.1, SetOracle.tg S c cand.2), t.map (SetOracle.tg S c))⟩ :
      Σ _ : QReg, (S.Node × (S.Node × S.Node × BList SLHDSA.Byte c.ml)) × List ((S.Node × S.Node × BList SLHDSA.Byte c.ml))) := by
  classical
  set prob := itsrProblem S.vp (ShakeApi.primitives S (ShakeApi.extend (ShakeXof.write (embedding S c cap) g Hf))) with hprob
  obtain ⟨hnot, hcov⟩ := hw
  have hidx : ∀ (R : S.Node) (x : S.Node × S.Node × List SLHDSA.Byte), x.2.2.length ≤ c.ml →
      prob.indexSet (R, x) = (SetDigest.idxOf S.vp) (Hf (R, SetOracle.tg S c x)) := fun R x hx ↦ by
    show prob.indices (prob.khf.hash R x) = _
    rw [eval_row S c cap g Hf R x hx]
    rfl
  refine ⟨fun hmem ↦ hnot ?_, fun i hi ↦ ?_⟩
  · have hmem' : isTgt Rs (t.map (SetOracle.tg S c)) (cand.1, SetOracle.tg S c cand.2) := by
      unfold itsrATargets at hmem
      exact (Finset.mem_filter.1 hmem).2
    obtain ⟨j, hj, hj'⟩ := hmem'
    simp only [List.getElem?_map] at hj'
    obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hj'
    have hjl : j.1 < t.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hy
      cases hy
    have hyt : t[j.1] = y := by
      rw [List.getElem?_eq_getElem hjl] at hy
      exact Option.some.inj hy
    have hyc : y = cand.2 := SetOracle.tg_inj S c y cand.2 (ht y (hyt ▸ List.getElem_mem hjl)) hcand hyx
    refine (SetOracle.mem_pairs S Rs t cand).2 ⟨j.1, hjl, ?_⟩
    rw [rndAt_lt Rs j.1 j.2, hyt, hyc]
    exact Prod.ext hj rfl
  · have hi' : i ∈ prob.indexSet cand := by rw [hidx cand.1 cand.2 hcand]; exact hi
    obtain ⟨e, he, hie⟩ := List.mem_flatMap.1 (hcov i hi')
    obtain ⟨j, hj, rfl⟩ := (SetOracle.mem_pairs S Rs t e).1 he
    have hjs : j < s := lt_of_lt_of_le hj hlen
    have htg : (Rs ⟨j, hjs⟩, SetOracle.tg S c t[j]) ∈ itsrATargets Rs (t.map (SetOracle.tg S c)) := by
      unfold itsrATargets
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨⟨j, hjs⟩, rfl, ?_⟩⟩
      simp [List.getElem?_map, List.getElem?_eq_getElem hj]
    refine ⟨Hf (Rs ⟨j, hjs⟩, SetOracle.tg S c t[j]), Finset.mem_image.2 ⟨_, htg, rfl⟩, ?_⟩
    · rw [hidx _ _ (ht _ (List.getElem_mem hj)), rndAt_lt Rs j hjs] at hie
      exact hie

end Reduction.ShakeAdaptive
#print axioms Reduction.ShakeAdaptive.eval_row

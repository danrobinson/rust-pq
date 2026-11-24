import Integration.SlhDsaShakeApiRaw
import Integration.SlhDsaShakeXofColumn

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder Kronecker
variable (S : Sha2Set) {N L : ℕ}

theorem node_le_digest : S.vp.params.n ≤ S.vp.params.m := by cases S <;> decide

def bytesEmbedding {J : Type} (bytes : J → List SLHDSA.Byte)
    (hb : ∀ j, (bytes j).length ≤ N) (hi : Function.Injective bytes) : J ↪ ShakeApi.Input N where
  toFun j := BList.ofList (bytes j) (hb j)
  inj' := by
    intro a b h
    apply hi
    simpa only [BList.ofFn_ofList] using congrArg (fun x : ShakeApi.Input N => List.ofFn x.2) h

def skEmb (cap : 2*S.vp.params.n+32 ≤ N) : S.Node × (S.Node × Bytes 32) ↪ ShakeApi.Input N :=
  bytesEmbedding (fun x => x.2.1.toList ++ x.2.2.toList ++ x.1.toList)
    (fun _ => by simp; omega) (by
      rintro ⟨k,p,a⟩ ⟨l,q,b⟩ h
      obtain ⟨hp,ha⟩ := List.append_inj h (by simp)
      obtain ⟨hk,ht⟩ := List.append_inj hp (by simp)
      exact Prod.ext (Vector.toList_inj.mp ha) (Prod.ext (Vector.toList_inj.mp hk) (Vector.toList_inj.mp ht)))

def skAddress (d : S.Node × SkAdrs S.vp) : S.Node × Bytes 32 := (d.1,d.2.val.toVector)

theorem skAddress_injective : Function.Injective (skAddress S) := by
  rintro ⟨pk,a⟩ ⟨pk',b⟩ h
  obtain ⟨h1,h2⟩ := Prod.mk.inj h
  exact Prod.ext h1 (Subtype.ext ((Concrete.keyInjective_shakePrimitives S.vp) a.property.addressFacts b.property.addressFacts h2))

theorem skScheme (cap : 2*S.vp.params.n+32 ≤ N) (g : ShakeApi.RawTable S N) :
    skPrfC S.vp (ShakeApi.primitives S (ShakeApi.extend g)) =
      keyedScheme (skAddress S) (read (skEmb S cap) (node_le_digest S) g) := by
  unfold skPrfC keyedScheme
  congr 1
  funext sk d
  change prefixBytes _ (ShakeApi.extend g _) = head _ _
  have len (x y : S.Node) (a : Bytes 32) : (x.toList ++ a.toList ++ y.toList).length ≤ N := by
    simp only [List.length_append,Vector.length_toList]; omega
  rw [head_eq_prefix,ShakeApi.extend_apply _ _ (len d.1 sk d.2.val.toVector)]
  rfl

abbrev MsgDomain (L : ℕ) := S.Node × BList SLHDSA.Byte L

def msgEmb (cap : 2*S.vp.params.n+L ≤ N) : S.Node × MsgDomain S L ↪ ShakeApi.Input N :=
  bytesEmbedding (fun x => x.1.toList ++ x.2.1.toList ++ List.ofFn x.2.2.2)
    (fun x => by have := x.2.2.1.isLt; simp; omega) (by
      rintro ⟨k,r,m⟩ ⟨l,s,z⟩ h
      obtain ⟨p,hm⟩ := List.append_inj h (by simp)
      obtain ⟨hk,hr⟩ := List.append_inj p (by simp)
      have hm' : m = z := by
        have hz : (List.ofFn z.2).length ≤ L := by simp; omega
        have hx : (List.ofFn m.2).length ≤ L := hm ▸ hz
        rw [← BList.ofList_ofFn m hx,← BList.ofList_ofFn z hz]
        congr
      exact Prod.ext (Vector.toList_inj.mp hk) (Prod.ext (Vector.toList_inj.mp hr) hm'))

noncomputable def boundedMsgScheme (g : ShakeApi.RawTable S N) : PRFScheme S.Node (MsgDomain S L) S.Node :=
  ⟨$ᵗ S.Node, fun k d => (ShakeApi.primitives S (ShakeApi.extend g)).PRFmsg k d.1 (List.ofFn d.2.2)⟩

theorem msgScheme (cap : 2*S.vp.params.n+L ≤ N) (g : ShakeApi.RawTable S N) :
    boundedMsgScheme (L := L) S g = keyedScheme id (read (msgEmb S cap) (node_le_digest S) g) := by
  unfold boundedMsgScheme keyedScheme
  congr 1
  funext sk d
  change prefixBytes _ (ShakeApi.extend g _) = head _ _
  have := d.2.1.isLt
  rw [head_eq_prefix,ShakeApi.extend_apply _ _ (by simp; omega)]
  rfl

variable {E : Type} [Fintype E] [DecidableEq E]
abbrev Work (N : ℕ) (E : Type) [Fintype E] [DecidableEq E] := WS (ShakeApi.Input N) (Bytes S.vp.params.m) E

theorem sk_prf (cap : 2*S.vp.params.n+32 ≤ N)
    (A : ShakeApi.RawTable S N → QOC (Work S N E) (PRFScheme.PRFOracleSpec (S.Node × SkAdrs S.vp) S.Node) Bool)
    (q : ℕ) (hA : PrfAnswerCost A q) (ρ : SubState ((ShakeApi.Input N × Bytes S.vp.params.m) × E)) :
    SetOracle.uniformMean (fun g => qPrfRealPr (skPrfC S.vp (ShakeApi.primitives S (ShakeApi.extend g))) (A g)
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    SetOracle.uniformMean (fun g => qPrfIdealPr (A g)
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  simp only [skScheme S cap,← Compression.node_card_real S]
  exact column_prf (node_le_digest S) (skEmb S cap) _ (skAddress_injective S) A q hA ρ

theorem msg_prf (cap : 2*S.vp.params.n+L ≤ N)
    (A : ShakeApi.RawTable S N → QOC (Work S N E) (PRFScheme.PRFOracleSpec (MsgDomain S L) S.Node) Bool)
    (q : ℕ) (hA : PrfAnswerCost A q) (ρ : SubState ((ShakeApi.Input N × Bytes S.vp.params.m) × E)) :
    SetOracle.uniformMean (fun g => qPrfRealPr (boundedMsgScheme S g) (A g)
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    SetOracle.uniformMean (fun g => qPrfIdealPr (A g)
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  simp only [msgScheme S cap,← Compression.node_card_real S]
  exact column_prf (node_le_digest S) (msgEmb S cap) id Function.injective_id A q hA ρ

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.sk_prf
#print axioms Reduction.ShakeXof.msg_prf

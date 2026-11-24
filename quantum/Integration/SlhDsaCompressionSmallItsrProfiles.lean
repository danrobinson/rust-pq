import Integration.SlhDsaCompressionSmallItsrFast
import Integration.SlhDsaCompressionSmallItsrEvidence

set_option backward.isDefEq.respectTransparency false
namespace Reduction.Compression.SmallItsr
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA SLHDSA.DigestTransport OracleComp OracleSpec Classical

private theorem uniform_pair (S : Sha2Set) (i : Fin S.vp.params.k)
    (P : Fin (2^S.vp.params.h) × Fin (2^S.vp.params.a) → Prop) :
    Pr{let d ← $ᵗ (Bytes S.vp.params.m)}[P ((coveringDigest S.vp d).1,(coveringDigest S.vp d).2 i)] =
      Pr{let z ← $ᵗ (Fin (2^S.vp.params.h) × Fin (2^S.vp.params.a))}[P z] :=
  (digest_uniform S _).symm.trans (MessageHash.coordinate_uniform S i P)

namespace Slow
abbrev vp := Sha2Set.s128s.vp
abbrev Key := Fin (2^63) × Fin (2^12)
def key (i : Fin vp.params.k) (s : St) : Key :=
  ((coveringDigest vp (dig30 s)).1,(coveringDigest vp (dig30 s)).2 i)

private theorem shape (g : CompressionTables) (x : Query .s128s) :
    msg .s128s g x = dig30 (g.1 (last .s128s rfl g x)) := by
  obtain ⟨r,pk,root,m⟩ := x
  have h : (tablePrimitives g vp.params).Hmsg r pk root m = (primsG (liftC g.1)).Hmsg r pk root m := by
    change sha2HmsgMixed (liftC g.1) (lift512 g.2) vp.params r pk root m = sha2HmsgG (liftC g.1) Link.vp.params r pk root m
    simp only [sha2HmsgMixed,sha2HmsgG,show vp.params.n = 16 from rfl,show Link.vp.params.n = 16 from rfl,ite_true]
    rfl
  change (tablePrimitives g vp.params).Hmsg r pk root m = _
  rw [h,hmsg_shape]
  change dig30 (mdFold g.1 IV128 (counterBlocks r pk _ 0)) = _
  rw [counterBlocks_pair]
  rfl

theorem covers (i : Fin vp.params.k) : Covers .s128s rfl (key i) i := by
  constructor
  intro g x y h₁ h₂
  rw [shape,shape] at h₁ h₂
  exact Prod.ext h₁ h₂

theorem uniform (i : Fin vp.params.k) (P : Key → Prop) :
    Pr{let s ← $ᵗ St}[P (key i s)] = Pr{let z ← $ᵗ Key}[P z] :=
  (prEvent_dig30 (fun d => P ((coveringDigest vp d).1,(coveringDigest vp d).2 i))).trans (uniform_pair .s128s i P)
end Slow

namespace Fast
def key (i : Ix) (s : St) := trim (digest128f (s,default)) i

private theorem shape (g : CompressionTables) (x : Query .s128f) (i : Ix) :
    trim (msg .s128f g x) i = key i (g.1 (last .s128f rfl g x)) := by
  obtain ⟨r,pk,root,m⟩ := x
  unfold msg
  rw [hmsg_128f_cells]
  exact trim_independent _ _ _ _

theorem covers (i : Ix) : Covers .s128f rfl (key i) i := by
  constructor
  intro g x y h₁ h₂
  rw [← shape,← shape]
  exact Prod.ext (congrArg (fun f : Fin (2^vp.params.h) => (finProdFinEquiv (m := 2^55) (n := 2^11)).symm f |>.1) h₁) h₂

theorem uniform (i : Ix) (P : Key → Prop) :
    Pr{let s ← $ᵗ St}[P (key i s)] = Pr{let z ← $ᵗ Key}[P z] := by
  let π := fun z : Fin (2^66) × Fin (2^6) => (((finProdFinEquiv (m := 2^55) (n := 2^11)).symm z.1).1,z.2)
  let e : Fin (2^66) × Fin (2^6) ≃ Key × Fin (2^11) :=
    ((finProdFinEquiv (m := 2^55) (n := 2^11)).symm.prodCongr (Equiv.refl _)).trans
      ⟨fun z => ((z.1.1,z.2),z.1.2),fun z => ((z.1.1,z.2),z.1.2),fun _ => rfl,fun _ => rfl⟩
  have eq : (fun z : St × St => P (key i z.1)) = fun z => P (trim (digest128f z) i) := by
    funext z
    exact congrArg P (trim_independent z.1 default z.2 i)
  calc _ = Pr{let z ← $ᵗ (St × St)}[P (key i z.1)] := (SampleableType.prEvent_uniformSample_fst _).symm
       _ = Pr{let z ← $ᵗ (St × St)}[P (trim (digest128f z) i)] := congrArg (fun f : St × St → Prop => Pr{let z ← $ᵗ (St × St)}[f z]) eq
       _ = Pr{let d ← $ᵗ (Bytes 34)}[P (trim d i)] := digest128f_uniform (fun d => P (trim d i))
       _ = Pr{let z ← $ᵗ (Fin (2^66) × Fin (2^6))}[P (π z)] := uniform_pair .s128f i (fun z => P (π z))
       _ = _ := (SampleableType.prEvent_uniformSample_comp_of_bijective e.bijective (fun z => P z.1)).trans
         (SampleableType.prEvent_uniformSample_fst P)
end Fast

end Reduction.Compression.SmallItsr
#print axioms Reduction.Compression.SmallItsr.Slow.covers
#print axioms Reduction.Compression.SmallItsr.Fast.covers
#print axioms Reduction.Compression.SmallItsr.Fast.uniform

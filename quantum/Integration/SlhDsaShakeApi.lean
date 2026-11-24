import Integration.SlhDsaSetClosed
import MReduction.ShakeOracle
import ME2E.ShakeRust

/-! Quantum chosen-message experiments for the six pure SHAKE byte schemes.
A single XOF supplies every hash call, including the overlap between the secret
PRF and a one-node tweakable hash. The public port is independent of the syntax
of the adversary and can be instantiated by an XOF or by a permutation. -/
namespace Reduction.ShakeApi

open MLink SLHDSA SLHDSA.Security PQ.Interactive OracleComp OracleSpec Quantum ENNReal
abbrev Xof (S : Sha2Set) := List SLHDSA.Byte → Bytes S.vp.params.m

@[reducible] def bundle (p : Params)
    (th : Bytes p.n → Bytes 32 → List (Bytes p.n) → Bytes p.n)
    (msg : Bytes p.n → Bytes p.n → Bytes p.n → List SLHDSA.Byte → Bytes p.m)
    (prf : Bytes p.n → Bytes p.n → Adrs → Bytes p.n)
    (prfMsg : Bytes p.n → Bytes p.n → List SLHDSA.Byte → Bytes p.n) : Primitives p :=
  { ShakeSecurity.primitives p with Thash := th, Hmsg := msg, PRF := prf, PRFmsg := prfMsg }

@[reducible] def primitives (S : Sha2Set) (H : Xof S) : Primitives S.vp.params :=
  bundle S.vp.params
    (fun pk key xs => prefixBytes _ (H (pk.toList ++ key.toList ++ (xs.map Vector.toList).flatten)))
    (fun r pk root msg => H (r.toList ++ pk.toList ++ root.toList ++ msg))
    (fun pk sk a => prefixBytes _ (H (pk.toList ++ a.toVector.toList ++ sk.toList)))
    (fun sk rand msg => prefixBytes _ (H (sk.toList ++ rand.toList ++ msg)))

theorem concrete (S : Sha2Set) : primitives S (ShakeSecurity.answer S) = ShakeSecurity.prims S := by
  have th := funext fun pk => funext fun k => funext fun xs => ShakeSecurity.thash_layout S pk k xs
  have msg := funext fun r => funext fun pk => funext fun root => funext fun m => ShakeSecurity.hmsg_layout S r pk root m
  have pm := funext fun sk => funext fun rand => funext fun m => ShakeSecurity.prfmsg_layout S sk rand m
  have pr (pk sk : S.Node) (a : Adrs) :
      prefixBytes S.vp.params.n (ShakeSecurity.answer S (pk.toList ++ a.toVector.toList ++ sk.toList)) =
        (ShakeSecurity.prims S).PRF pk sk a := by
    have e := ShakeSecurity.thash_layout S pk a.toVector [sk]
    simpa only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
      ShakeSecurity.prims,ShakeSecurity.primitives,nds,List.flatMap_cons,List.flatMap_nil] using e
  unfold primitives
  rw [th,msg,pm,funext fun pk => funext fun sk => funext fun a => pr pk sk a]

def codec (S : Sha2Set) (H : Xof S) : CoreWireCodec S.vp.params (primitives S H).core where
  pkSeed := WireCodec.bytes _
  skSeed := WireCodec.bytes _
  skPrf := WireCodec.bytes _
  y := WireCodec.bytes _
  y_toBytes := fun _ => rfl

theorem structural (S : Sha2Set) (H : Xof S) : Structural S.vp (primitives S H) :=
  ⟨⟨fun _ _ h => h⟩, Concrete.keyInjective_shakePrimitives _, (fipsApprovedAddressBounds S.fips).toCanonicalAddressBounds⟩

variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
noncomputable abbrev scheme (H : Xof S) :=
  pureBytesAlg S.vp (primitives S H) (codec S H) (fun pk => rand pk.pkSeed pk.pkRoot) seeds

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] (F : PortForger X Y E)

noncomputable abbrev forgerAt (H : Xof S) (port : X → Y) :=
  F.at port (scheme S rand seeds H)

/-- Reductions apply pointwise for a signer and forger with correlated oracle
access. The quantitative games keep the forger's access to this same port. -/
theorem signature_reduction (H : Xof S) (port : X → Y) :
    let Q := forgerAt S rand seeds F H port
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemoG (qPureBytesToInternal Q) ∧
    qUnforgeableAdvantage Q ≤ qBetaEufMemoG (qPureBytesToInternal Q) :=
  ⟨slhdsa_pure_bytes_suf_cma_final_quantum_all_general (structural S H) _,
   slhdsa_pure_bytes_euf_cma_final_quantum_all_general (structural S H) _⟩

end Reduction.ShakeApi
#print axioms Reduction.ShakeApi.concrete
#print axioms Reduction.ShakeApi.structural
#print axioms Reduction.ShakeApi.signature_reduction

import Integration.SlhDsaCompressionWotsSmallAverage
import MIdeal.Hash128f

namespace Reduction.Compression.Wots256
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
open HiddenWeight (mean)
variable {E σ : Type} [Fintype E] [DecidableEq E]
local notation "W" => WS Input Output E

abbrev Hash := Node → Bytes 22 → List Node → Node
def chainHash (g : CF St Blk) : Hash := fun pk t xs => out16 (keyedChain IV128 sb128 g pk (tblocks t xs))

theorem shape_fast (g : CompressionTables) :
    (tablePrimitives g Sha2Set.s128f.vp.params).Thash = chainHash g.1 :=
  funext fun pk => funext fun a => funext fun xs => MIdeal.Hash128f.shape g pk a xs

theorem shape_slow (g : CompressionTables) :
    (tablePrimitives g Sha2Set.s128s.vp.params).Thash = chainHash g.1 := by
  funext pk a xs
  apply Eq.trans _ (primsG_Thash_shape g.1 pk a xs)
  change sha2ThashMixed (liftC g.1) (lift512 g.2) Sha2Set.s128s.vp.params pk a xs =
    sha2ThashG (liftC g.1) Link.vp.params pk a xs
  simp only [sha2ThashMixed,sha2ThashG,show Sha2Set.s128s.vp.params.n = 16 from rfl,
    show Link.vp.params.n = 16 from rfl,ite_eq_left,ite_self]
  rfl

noncomputable def preNative (seeds : ProbComp Node) (n : ℕ) (hash : Hash) : SM_DT_PRE_Problem Unit Node (Bytes 22) Node Node Node where
  th := ⟨seeds,fun pk a m => hash pk a [m]⟩
  thColl := ⟨fun _ => List Node,fun _ => hash⟩
  emb := id
  emb_injective := Function.injective_id
  numTargets := n

theorem pre_native (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (PreSpecG (preP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (t : CompressionTables) (pk : Node) (hash : Hash) (hh : hash = chainHash t.1) :
    preInner (⟨σ,choose,M (oracle t),ρ,hp,ht⟩ : QSM_DT_PRE_Adversary W (preNative seeds n hash)) pk =
      preValue seeds n choose M ρ t pk := by
  subst hash
  unfold preInner preValue preScore mean
  rw [wq_qWeight_liftU_bind_tsum]
  dsimp only [preNative,chainHash,THFam.preProb,THFam.evalT,THFam.evalC,THFam.coll,family,FWots128T,id_eq]
  qm_kernel_rfl

noncomputable def tcrNative (seeds : ProbComp Node) (n : ℕ) (hash : Hash) : SM_DT_TCR_Problem Unit Node (Bytes 22) Node Node where
  th := ⟨seeds,fun pk a m => hash pk a [m]⟩
  thColl := ⟨fun _ => List Node,fun _ => hash⟩
  numTargets := n

theorem tcr_native (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (TcrSpec (tcrP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × Node)) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (t : CompressionTables) (pk : Node) (hash : Hash) (hh : hash = chainHash t.1) :
    tcrInner (⟨σ,choose,M (oracle t),ρ,hp,ht⟩ : QSM_DT_TCR_Adversary W (tcrNative seeds n hash)) pk =
      tcrValue seeds n choose M ρ t pk := by
  subst hash
  unfold tcrInner tcrValue tcrScore mean
  rw [wq_qWeight_liftU_bind_tsum]
  dsimp only [tcrNative,chainHash,THFam.tcrProb,THFam.evalT,THFam.evalC,THFam.coll,family,FWots128T,id_eq]
  qm_kernel_rfl

noncomputable def udNative (seeds : ProbComp Node) (n : ℕ) (hash : Hash) : SM_DT_UD_Problem Unit Node (Bytes 22) Node Node Node where
  th := ⟨seeds,fun pk a m => hash pk a [m]⟩
  thColl := ⟨fun _ => List Node,fun _ => hash⟩
  emb := id
  emb_injective := Function.injective_id
  inputGen := $ᵗ Node
  outputGen := $ᵗ Node
  numTargets := n

theorem ud_native (world : SM_DT_UD_World) (seeds : ProbComp Node) (n : ℕ)
    (choose : OracleComp (UdSpecG (udP seeds n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W Bool) (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1)
    (t : CompressionTables) (pk : Node) (hash : Hash) (hh : hash = chainHash t.1) :
    udInner world (⟨σ,choose,M (oracle t),ρ,hp,ht⟩ : QSM_DT_UD_Adversary W (udNative seeds n hash)) pk =
      udValue world seeds n choose M ρ t pk := by
  subst hash
  unfold udInner udValue udScore mean
  rw [wq_qWeight_liftU_bind_tsum]
  dsimp only [udNative,chainHash,THFam.udProb,THFam.evalT,THFam.evalC,THFam.coll,family,FWots128T,id_eq]
  qm_kernel_rfl
end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.pre_native
#print axioms Reduction.Compression.Wots256.tcr_native
#print axioms Reduction.Compression.Wots256.ud_native

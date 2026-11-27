import Parallel.AuthTableRow
import Parallel.RootTableHosted
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelAuthTable
open ParallelXmssTicket

/-- The metadata fields inserted alongside the chunk tickets by the queue builder. -/
def issuedMetadata (p : params.Params) (layer : Usize) (index h : U32) (start : Usize) := do
  let (_,r,sp,lev,first,_,_,_,_) ← chunk p layer index h 0#usize start
  ok (XmssAuthMeta.mk first sp r lev)

def issuedNode {N : Usize} (p : params.Params) (node : Node N) (layers : alloc.vec.Vec (address.Adrs × U32))
    (j : Usize) (h : U32) (c start : Usize) (sk seed : Array U8 N) := do
  let (_,_,_,_,_,lj,i,z,dest) ← chunk p j layers.val[j.val]!.2 h c start
  subtree_ticket node layers lj i z dest sk seed

/-- A successful physical publication records the exact returned row at its returned slot. -/
theorem chunks_from_jobs {N : Usize} (p : params.Params) (hp : PN p N) (node : Node N) (law : NodeLaw p node 512)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (j : Usize) (h : U32) (start : Usize) (m : XmssAuthMeta)
    (sk seed : Array U8 N) (slots : alloc.vec.Vec (Option (Array U8 N))) (inside : j.val<layers.length)
    (layer : j.val<65536) (below : h.val<p.hp.val) (leaf : layers.val[j.val]!.2.val<2^p.hp.val)
    (space : start.val+2^(depth p.hp.val h.val)≤slots.length)
    (record : issuedMetadata p j layers.val[j.val]!.2 h start=ok m)
    (published : ∀ (c : Usize), c.val<2^(depth p.hp.val h.val) → ∀ (dest : Usize) (row : Array U8 N),
      issuedNode p node layers j h c start sk seed=ok (dest,row) → slots.val[dest.val]! = some row) :
    m.root_idx.val=root layers.val[j.val]!.2.val h.val ∧ m.height.val=h.val ∧
      Chunks p (bytes sk.val) seed (adrsS layers.val[j.val]!.1) m slots := by
  have cap : slots.length≤Usize.max := by scalar_tac
  let index := layers.val[j.val]!.2
  have pos : 0<2^(depth p.hp.val h.val) := Nat.two_pow_pos _
  obtain ⟨⟨next,r,sp,lev,first,lj,i,z,slot⟩,call,_,rootEq,splitEq,levelEq,firstEq,_⟩ := spec_imp_exists
    (chunk_spec p j index h 0#usize start hp.valid.hp_le below leaf layer pos (space.trans cap))
  change (do let (_,r,sp,lev,first,_,_,_,_) ← chunk p j index h 0#usize start
             ok (XmssAuthMeta.mk first sp r lev))=ok m at record
  rw [call] at record
  simp only [bind_ok,ok.injEq] at record
  change ok (XmssAuthMeta.mk first sp r lev)=ok m at record
  have same := Result.ok_injective record
  subst m
  subst lev;subst first
  refine ⟨rootEq,rfl,?_,?_,?_,?_,?_⟩
  · exact splitEq ▸ Nat.sub_le ..
  · have maxH : p.hp.val≤9 := hp.valid.hp_le
    exact Nat.le_trans below.le maxH
  · simpa only [splitEq] using space
  · have maxH : p.hp.val≤9 := hp.valid.hp_le
    have last : 2^(depth p.hp.val h.val)-1<2^(depth p.hp.val h.val) := by omega
    have bound := chunk_bound _ _ _ _ maxH below leaf last
    simp only [rootEq,splitEq]
    have pos2 := Nat.le_mul_of_pos_right (root index.val h.val*2^(depth p.hp.val h.val)+(2^(depth p.hp.val h.val)-1)+1)
      (Nat.two_pow_pos (h.val-depth p.hp.val h.val))
    change (root index.val h.val+1)*2^(depth p.hp.val h.val)≤2^32
    rw [Nat.add_mul,Nat.one_mul];dsimp only [index] at *;omega
  · intro c active
    simp only at active ⊢
    rw [splitEq] at active
    have small : c < 2^UScalarTy.Usize.numBits := by scalar_tac
    let cc := Usize.ofNatCore c small
    have cv : cc.val=c := by simp [cc]
    obtain ⟨⟨dest,row⟩,exec,whereAt,val⟩ := spec_imp_exists
      (issued_subtree p hp node law layers j index h cc start sk seed inside rfl layer below leaf (cv ▸ active) (space.trans cap))
    have saved := published cc (cv ▸ active) dest row exec
    rw [whereAt,cv] at saved
    exact ⟨row,saved,by simpa only [rootEq,splitEq,cv] using val⟩

noncomputable def nativeNode {N : Usize} (host : ParallelRootWalk.Host) (p : params.Params) : Node N :=
  match host with
  | .apple sha3 => hostedNode (.apple sha3) p
  | .x86 => hostedNode .x86 p
  | .linuxArm => WidthThree.linuxNode

theorem native_law {N : Usize} (host : ParallelRootWalk.Host) (p : params.Params) (hp : PN p N) :
    NodeLaw p (nativeNode (N:=N) host p) 512 := by
  cases host with
  | apple sha3 => exact hosted_law (.apple sha3) p hp
  | x86 => exact hosted_law .x86 p hp
  | linuxArm => intro sk i z seed a room; exact WidthThree.linuxNodeSpec p hp sk i z seed a (by omega)

abbrev native_chunks {N : Usize} (host : ParallelRootWalk.Host) (p : params.Params) (hp : PN p N) :=
  @chunks_from_jobs N p hp _ (native_law host p hp)

end slhdsa.ParallelAuthTable

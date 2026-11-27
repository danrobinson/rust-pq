import Buffered.ForsHorizontal.Program
import Buffered.ForsHorizontal.Counts
import Buffered.Transfer
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ForsHorizontal
open ShakeBatch NativeVerify
open Buffered
abbrev Buffer (N : Usize) := Array (Row16 N) 16#usize
abbrev Lengths := Array Usize 16#usize
abbrev Cursors := Array U32 16#usize
abbrev Stack := Buffer
abbrev Scratch := Array address.Adrs 8#usize
abbrev StreamState (N : Usize) := Buffer N × Lengths × Cursors × Scratch × Rows8 N × Rows8 N
def fors {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (h i : Nat) :=
  Spec.forsNode (Shake.params p) (bytes sk.val) i h (bytes seed.val) (adrsS a)

theorem hashed_node {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a tree : address.Adrs)
    {root z c} {buf : Buffer N} {len cur} (old : Grid (fors p sk seed a) root z c buf len cur)
    (h j : Nat) (live : h<z) (enough : 2*j+1<waiting c h) (domain : adrsS tree=adrsS a) :
    Spec.H (Shake.params p) (bytes seed.val) {adrsS tree with word2:=h+1,word3:=nextBase root z c (h+1)+j}
      (cellBytes buf h (2*j) ++ cellBytes buf h (2*j+1)) =
    fors p sk seed a (h+1) (nextBase root z c (h+1)+j) := by
  rw [old.cell h (by omega) (2*j) (by omega),old.cell h (by omega) (2*j+1) enough,domain]
  simp only [fors,Spec.forsNode]
  have e : rowBase root z c h + 2*j = 2*(nextBase root z c (h+1)+j) := by
    simp [rowBase,nextBase,level_step root z h live]
    omega
  rw [e,show rowBase root z c h+(2*j+1)=2*(nextBase root z c (h+1)+j)+1 by omega]

theorem carry_gather {N : Usize} (count : Usize) (tree : address.Adrs)
    (addrs : Array address.Adrs 8#usize) (left right : Rows8 N) (base lvl : U32) (row : Row16 N)
    (fit : count.val≤8) (words : base.val+count.val≤2^32) :
    subtree_loop1_loop0_loop0 ⟨0#usize,count⟩ tree addrs left right base lvl row ⦃ as' ls rs =>
      Gathered count.val tree base lvl row as' ls rs ⦄ :=
  Buffered.carry_gather count tree addrs left right base lvl row fit words

theorem flush_gather {N : Usize} (count : Usize) (tree : address.Adrs)
    (addrs : Array address.Adrs 8#usize) (left right : Rows8 N) (base lvl : U32) (row : Row16 N)
    (fit : count.val≤8) (words : base.val+count.val≤2^32) :
    subtree_loop2_loop0 ⟨0#usize,count⟩ tree addrs left right base lvl row ⦃ as' ls rs =>
      Gathered count.val tree base lvl row as' ls rs ⦄ :=
  Buffered.carry_gather count tree addrs left right base lvl row fit words

variable [kernel : Fused.Kernel]
local instance horizGatherMachine : Machine := Fused.machine kernel

/-- Each active Keccak parent combines exactly its two neighboring cells in the
immutable sixteen-row snapshot, using the parent height and absolute index. -/
theorem hashed_gather {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (tree : address.Adrs) (count : Usize) (base lvl : U32) (row : Row16 N)
    (addrs : Array address.Adrs 8#usize) (left right : Rows8 N) (live : count.val≤8)
    (gathered : Gathered count.val tree base lvl row addrs left right)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    ActiveHash.pair_active kernel.active seed addrs left right count ⦃ out => ∀ k < count.val,
      bytes out.val[k]!.val = Spec.H (Shake.params p) (bytes seed.val)
        {adrsS tree with word2:=lvl.val,word3:=base.val+k}
        (bytes row.val[2*k]!.val ++ bytes row.val[2*k+1]!.val) ⦄ := by
  apply WP.spec_mono (@ActiveHash.pair_fips (Fused.machine kernel) kernel.active N seed addrs left right count live perm hp.le32 (aligned_hash hp))
  intro out hashes k hk
  obtain ⟨a,l,r⟩ := gathered k hk
  rw [←a,←l,←r]
  have fact := hashes k hk
  simp only [Spec.H,Shake.params,paramsS_n,hp.n_eq,List.append_assoc] at fact ⊢
  with_unfolding_all exact fact

end slhdsa.ForsHorizontal

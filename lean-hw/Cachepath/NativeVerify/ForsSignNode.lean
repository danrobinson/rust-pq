import Cachepath.NativeVerify.ForsSignNodeProgram
import Cachepath.NativeVerify.ForsSignLinux
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
section
variable [machine : Machine]

private theorem addressesOf (N : Usize) (a : address.Adrs) (lvl : U32) (indices : Array U32 machine.width) :
    core.array.Array.map (descend.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices (a,lvl) ⦃ out =>
      ∀ j < machine.width.val, out.val[j]! = {a with word2:=lvl,word3:=indices.val[j]!} ⦄ :=
  node_addresses N a lvl indices

private theorem leftIds (N : Usize) (indices : Array U32 machine.width)
    (fit : ∀ j < machine.width.val, 2*indices.val[j]!.val+1 < 2^32) :
    core.array.Array.map (descend.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () ⦃ out =>
      ∀ j < machine.width.val, out.val[j]!.val=2*indices.val[j]!.val ⦄ :=
  left_indices N indices fit

private theorem rightIds (N : Usize) (indices : Array U32 machine.width)
    (fit : ∀ j < machine.width.val, 2*indices.val[j]!.val+1 < 2^32) :
    core.array.Array.map (descend.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () ⦃ out =>
      ∀ j < machine.width.val, out.val[j]!.val=2*indices.val[j]!.val+1 ⦄ :=
  right_indices N indices fit

def LeafLaw (leaf : Leaf) := ∀ {N : Usize} (p : slhdsa.params.Params), PN p N →
  ∀ (sk seed : Array U8 N) (a : address.Adrs) (ids : Array U32 machine.width) (active : Usize),
  (a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) → active.val ≤ machine.width.val →
  leaf sk seed a ids active ⦃ out => ∀ j < active.val, bytes out.val[j]!.val=
    Spec.forsNode (Shake.params p) (bytes sk.val) ids.val[j]!.val 0 (bytes seed.val) (adrsS a) ⦄

def PairLaw (pair : Pair) := ∀ {N : Usize} (p : slhdsa.params.Params), PN p N →
  ∀ (seed : Array U8 N) (addrs : Array address.Adrs machine.width) (left right : Rows N) (active : Usize),
  active.val ≤ machine.width.val → pair seed addrs left right active ⦃ out => ∀ j < active.val,
    bytes out.val[j]!.val = Spec.shake256 (bytes seed.val ++ ((adrsS addrs.val[j]!).bytes ++
      (bytes left.val[j]!.val ++ bytes right.val[j]!.val))) N.val ⦄

theorem descend_correct (leaf : Leaf) (pair : Pair) (leafHash : LeafLaw leaf) (pairHash : PairLaw pair) :
    NodesLaw (descend leaf pair) := by
  intro N p hp sk seed a indices level active dom bound bounds
  change descend leaf pair sk seed a indices level active ⦃ out => ∀ j < active.val, bytes out.val[j]!.val = Spec.forsNode (Shake.params p) (bytes sk.val) indices.val[j]!.val level.val (bytes seed.val) (adrsS a) ⦄
  generalize h : level.val = n at bounds ⊢
  induction n generalizing level indices with
  | zero =>
    have zero : level=0#u32 := by scalar_tac
    subst level
    unfold descend
    simp only [ite_true]
    exact leafHash p hp sk seed a indices active dom bound
  | succ n ih =>
    have nonzero : level≠0#u32 := by scalar_tac
    have valid (j : Nat) (hj : j < machine.width.val) :
        (2*indices.val[j]!.val+1+1)*2^n < 2^32 := by
      rw [show 2*indices.val[j]!.val+1+1=2*(indices.val[j]!.val+1) by omega]
      simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bounds j hj
    have twice (j : Nat) (hj : j < machine.width.val) : 2*indices.val[j]!.val+1 < 2^32 := by
      have := valid j hj
      have hpow := Nat.one_le_two_pow (n:=n)
      nlinarith
    unfold descend
    simp only [nonzero,ite_false]
    step with leftIds N indices twice as ⟨ls,lidx⟩
    step as ⟨lower,lev⟩
    have lower_n : lower.val=n := by omega
    have lb (j : Nat) (hj : j < machine.width.val) : (ls.val[j]!.val+1)*2^n < 2^32 := by
      rw [lidx j hj]
      have := valid j hj
      have hpow := Nat.one_le_two_pow (n:=n)
      nlinarith
    step with ih ls lower lower_n lb as ⟨left,lv⟩
    step with rightIds N indices twice as ⟨rs,ridx⟩
    have rb (j : Nat) (hj : j < machine.width.val) : (rs.val[j]!.val+1)*2^n < 2^32 := by
      rw [ridx j hj]; exact valid j hj
    step with ih rs lower lower_n rb as ⟨right,rv⟩
    step with addressesOf N a level indices as ⟨addresses,rows⟩
    step with pairHash p hp seed addresses left right active bound as ⟨out,hash⟩
    rename_i j hj
    rw [hash j hj,rows j (hj.trans_le bound),lv j hj,rv j hj,lidx j (hj.trans_le bound),ridx j (hj.trans_le bound),Spec.forsNode]
    simp [Spec.H,Shake.params,hp.n_eq,adrsS,h,List.append_assoc]


end

section
local instance : Machine := Kldisp.machine

def observedLeaf : Leaf :=
  fun sk seed a ids _ => ShakeBatch.shake.fors_batch.nodes sk seed a ids 0#u32

def observedPair : Pair :=
  fun seed addrs left right _ => ShakeBatch.shake.batch.pair seed addrs left right

theorem observedLeaf_correct : LeafLaw observedLeaf := by
  intro N p hp sk seed a ids active dom width
  unfold observedLeaf ShakeBatch.shake.fors_batch.nodes
  step with node_addresses N a 0#u32 ids as ⟨addrs,rows⟩
  simp only [ite_true]
  step with fors_secrets p hp sk seed a ids Kldisp.permutation_correct as ⟨secrets,values⟩
  step with short_fips seed addrs secrets Kldisp.permutation_correct hp.le32 (aligned_hash hp) as ⟨out,hash⟩
  rename_i j hj
  have lt := hj.trans_le width
  rw [hash j lt,rows j lt,values j lt,Spec.forsNode]
  simp [Spec.F,Shake.params,hp.n_eq,adrsS,List.append_assoc]

theorem observedPair_correct : PairLaw observedPair := by
  intro N p hp seed addrs left right active width
  apply WP.spec_mono (pair_fips seed addrs left right Kldisp.permutation_correct hp.le32 (aligned_hash hp))
  intro out values j hj
  exact values _ (hj.trans_le width)

def linuxRecursive : WidthThree.ForsSigner :=
  linux observedShort (descend observedLeaf observedPair) observedShort_correct
    (descend_correct observedLeaf observedPair observedLeaf_correct observedPair_correct)

end
end slhdsa.NativeVerify.ForsSign

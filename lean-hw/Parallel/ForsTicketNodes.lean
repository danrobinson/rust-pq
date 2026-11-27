import Parallel.ForsTicketNodesProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelForsTicket
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
local instance nodesMachine : Machine := Kldisp.machine
set_option allowUnsafeReducibility true in
attribute [local reducible] Kldisp.machine nodesMachine UScalar.cMax

private theorem addressesOf (N : Usize) (a : address.Adrs) (lvl : U32) (indices : Array U32 3#usize) :
    core.array.Array.map (nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices (a,lvl) ⦃ out =>
      ∀ j < (3#usize).val, out.val[j]! = {a with word2:=lvl,word3:=indices.val[j]!} ⦄ :=
  node_addresses N a lvl indices

private theorem leftIds (N : Usize) (indices : Array U32 3#usize)
    (fit : ∀ j < (3#usize).val, 2*indices.val[j]!.val+1 < 2^32) :
    core.array.Array.map (nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () ⦃ out =>
      ∀ j < (3#usize).val, out.val[j]!.val=2*indices.val[j]!.val ⦄ :=
  left_indices N indices fit

private theorem rightIds (N : Usize) (indices : Array U32 3#usize)
    (fit : ∀ j < (3#usize).val, 2*indices.val[j]!.val+1 < 2^32) :
    core.array.Array.map (nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () ⦃ out =>
      ∀ j < (3#usize).val, out.val[j]!.val=2*indices.val[j]!.val+1 ⦄ :=
  right_indices N indices fit

variable [wide : Wide]

private theorem recurse {N : Usize} (sk seed : Array U8 N) (a : address.Adrs)
    (indices : Array U32 3#usize) (active : Usize) (level : U32) (nonzero : level≠0#u32) :
    nodes sk seed a indices active level = (do
      let ls ← core.array.Array.map (nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices ()
      let lo ← level-1#u32
      let left ← nodes sk seed a ls active lo
      let rs ← core.array.Array.map (nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices ()
      let right ← nodes sk seed a rs active lo
      let addresses ← core.array.Array.map (nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices (a,level)
      ActiveHash.pair_active activeHash seed addresses left right active) := by
  conv => lhs; unfold nodes
  simp only [nonzero,ite_false]
  rfl

theorem nodes_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (indices : Array U32 3#usize) (active : Usize) (level : U32)
    (dom : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (bound : active.val≤3) (bounds : ∀ j<3, (indices.val[j]!.val+1)*2^level.val<2^32) :
    nodes sk seed a indices active level ⦃ out => ∀ j<active.val, bytes out.val[j]!.val=
      Spec.forsNode (Shake.params p) (bytes sk.val) indices.val[j]!.val level.val (bytes seed.val) (adrsS a) ⦄ := by
  generalize h : level.val = n at bounds ⊢
  induction n generalizing level indices with
  | zero =>
    have zero : level=0#u32 := by scalar_tac
    subst level
    unfold nodes
    simp only [show (3#usize)≠8#usize by decide,ite_false,ite_true]
    exact ForsFused.leaf_correct activeHash NativeVerify.linux p hp sk seed a indices active dom bound
  | succ n ih =>
    have nonzero : level≠0#u32 := by scalar_tac
    have valid (j : Nat) (hj : j < (3#usize).val) :
        (2*indices.val[j]!.val+1+1)*2^n < 2^32 := by
      rw [show 2*indices.val[j]!.val+1+1=2*(indices.val[j]!.val+1) by omega]
      simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bounds j hj
    have twice (j : Nat) (hj : j < (3#usize).val) : 2*indices.val[j]!.val+1 < 2^32 := by
      have := valid j hj
      have hpow := Nat.one_le_two_pow (n:=n)
      nlinarith
    rw [recurse sk seed a indices active level nonzero]
    let* ⟨ls,lidx⟩ ← leftIds N indices twice
    step as ⟨lower,lev⟩
    have lower_n : lower.val=n := by omega
    have lb (j : Nat) (hj : j < (3#usize).val) : (ls.val[j]!.val+1)*2^n < 2^32 := by
      rw [lidx j hj]
      have := valid j hj
      have hpow := Nat.one_le_two_pow (n:=n)
      nlinarith
    step with ih ls lower lower_n lb as ⟨left,lv⟩
    step with rightIds N indices twice as ⟨rs,ridx⟩
    have rb (j : Nat) (hj : j < (3#usize).val) : (rs.val[j]!.val+1)*2^n < 2^32 := by
      rw [ridx j hj]; exact valid j hj
    step with ih rs lower lower_n rb as ⟨right,rv⟩
    step with addressesOf N a level indices as ⟨addresses,rows⟩
    step with ActiveHash.pair_correct activeHash NativeVerify.linux p hp seed addresses left right active bound as ⟨out,hash⟩
    rename_i j hj
    rw [hash j hj,rows j (hj.trans_le bound),lv j hj,rv j hj,lidx j (hj.trans_le bound),ridx j (hj.trans_le bound),Spec.forsNode]
    simp [Spec.H,Shake.params,hp.n_eq,adrsS,h,List.append_assoc]
end slhdsa.ParallelForsTicket

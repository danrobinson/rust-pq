import Parallel.LowForsProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelLowFors
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
variable [machine : Machine]

private theorem addressesOf (N : Usize) (a : address.Adrs) (lvl : U32) (indices : Array U32 machine.width) :
    core.array.Array.map (nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices (a,lvl) ⦃ out =>
      ∀ j < (machine.width).val, out.val[j]! = {a with word2:=lvl,word3:=indices.val[j]!} ⦄ :=
  node_addresses N a lvl indices

private theorem leftIds (N : Usize) (indices : Array U32 machine.width)
    (fit : ∀ j < (machine.width).val, 2*indices.val[j]!.val+1 < 2^32) :
    core.array.Array.map (nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () ⦃ out =>
      ∀ j < (machine.width).val, out.val[j]!.val=2*indices.val[j]!.val ⦄ :=
  left_indices N indices fit

private theorem rightIds (N : Usize) (indices : Array U32 machine.width)
    (fit : ∀ j < (machine.width).val, 2*indices.val[j]!.val+1 < 2^32) :
    core.array.Array.map (nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices () ⦃ out =>
      ∀ j < (machine.width).val, out.val[j]!.val=2*indices.val[j]!.val+1 ⦄ :=
  right_indices N indices fit

variable [host : Host machine] [wide : Wide]

private theorem recurse {N : Usize} (sk seed : Array U8 N) (a : address.Adrs)
    (indices : Array U32 machine.width) (active : Usize) (level : U32) (nonzero : level≠0#u32) (guard : machine.width≠8#usize ∨ level.val<3) :
    nodes sk seed a indices active level = (do
      let ls ← core.array.Array.map (nodes.closure.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices ()
      let lo ← level-1#u32
      let left ← nodes sk seed a ls active lo
      let rs ← core.array.Array.map (nodes.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices ()
      let right ← nodes sk seed a rs active lo
      let addresses ← core.array.Array.map (nodes.closure_2.Insts.CoreOpsFunctionFnMutTupleU32Adrs N) indices (a,level)
      ActiveHash.pair_active host.perm seed addresses left right active) := by
  conv => lhs; unfold nodes
  rcases guard with narrow|low
  · simp [narrow,nonzero]
  · have skip : ¬level≥3#u32 := by scalar_tac
    simp [skip,nonzero]

theorem nodes_spec (correct : ActiveCorrect machine host.perm) {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (indices : Array U32 machine.width) (active : Usize) (level : U32)
    (dom : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (bound : active.val≤machine.width.val) (bounds : ∀ j<machine.width.val, (indices.val[j]!.val+1)*2^level.val<2^32)
    (guard : machine.width≠8#usize ∨ level.val<3) :
    nodes sk seed a indices active level ⦃ out => ∀ j<active.val, bytes out.val[j]!.val=
      Spec.forsNode (Shake.params p) (bytes sk.val) indices.val[j]!.val level.val (bytes seed.val) (adrsS a) ⦄ := by
  generalize h : level.val = n at bounds guard ⊢
  induction n generalizing level indices with
  | zero =>
    have zero : level=0#u32 := by scalar_tac
    subst level
    unfold nodes
    simp only [show ¬(0#u32)≥3#u32 by decide,ite_false,ite_true,ite_self]
    exact ForsFused.leaf_correct host.perm correct p hp sk seed a indices active dom bound
  | succ n ih =>
    have nonzero : level≠0#u32 := by scalar_tac
    have valid (j : Nat) (hj : j < (machine.width).val) :
        (2*indices.val[j]!.val+1+1)*2^n < 2^32 := by
      rw [show 2*indices.val[j]!.val+1+1=2*(indices.val[j]!.val+1) by omega]
      simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bounds j hj
    have twice (j : Nat) (hj : j < (machine.width).val) : 2*indices.val[j]!.val+1 < 2^32 := by
      have := valid j hj
      have hpow := Nat.one_le_two_pow (n:=n)
      nlinarith
    rw [recurse sk seed a indices active level nonzero (h ▸ guard)]
    let* ⟨ls,lidx⟩ ← leftIds N indices twice
    step as ⟨lower,lev⟩
    have lower_n : lower.val=n := by omega
    have lb (j : Nat) (hj : j < (machine.width).val) : (ls.val[j]!.val+1)*2^n < 2^32 := by
      rw [lidx j hj]
      have := valid j hj
      have hpow := Nat.one_le_two_pow (n:=n)
      nlinarith
    step with ih ls lower lower_n lb (by rcases guard with w|l;exact Or.inl w;exact Or.inr (by omega)) as ⟨left,lv⟩
    step with rightIds N indices twice as ⟨rs,ridx⟩
    have rb (j : Nat) (hj : j < (machine.width).val) : (rs.val[j]!.val+1)*2^n < 2^32 := by
      rw [ridx j hj]; exact valid j hj
    step with ih rs lower lower_n rb (by rcases guard with w|l;exact Or.inl w;exact Or.inr (by omega)) as ⟨right,rv⟩
    step with addressesOf N a level indices as ⟨addresses,rows⟩
    step with ActiveHash.pair_correct host.perm correct p hp seed addresses left right active bound as ⟨out,hash⟩
    rename_i j hj
    rw [hash j hj,rows j (hj.trans_le bound),lv j hj,rv j hj,lidx j (hj.trans_le bound),ridx j (hj.trans_le bound),Spec.forsNode]
    simp [Spec.H,Shake.params,hp.n_eq,adrsS,h,List.append_assoc]


omit wide in
theorem secrets_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (addr : address.Adrs) (indices : Array U32 machine.width)
    (active : Usize) (bound : active.val≤machine.width.val) (correct : ActiveCorrect machine host.perm) :
    secrets sk seed addr indices active ⦃ out =>
      ∀ j < active.val, bytes out.val[j]!.val =
        Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS addr) indices.val[j]!.val ⦄ := by
  unfold secrets
  step as ⟨a,atype,fields⟩
  step as ⟨prf,key⟩
  let inst := secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs N
  let post := fun (j : Nat) (v : address.Adrs) => v = {prf with word3:=indices.val[j]!}
  have each (j : Nat) (_ : j < machine.width.val) :
      inst.call_mut prf indices.val[j]! ⦃ x g => post j x ∧ g=prf ⦄ := by
    simp [inst,post,secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs,
      secrets.closure.Insts.CoreOpsFunctionFnMutTupleU32Adrs.call_mut,
      address.Adrs.with_word3,step_simps]
  step with map_spec inst indices prf post each as ⟨addresses,rows⟩
  step with ActiveHash.short_correct host.perm correct p hp seed addresses (Array.repeat machine.width sk) active bound as ⟨out,hash⟩
  rename_i j hj
  have same := rows j (hj.trans_le bound)
  rw [hash j hj,same,Array.repeat_val]
  simp only [key,fields,Spec.forsSkGen,Spec.PRF,Shake.params,paramsS_n,hp.n_eq,adrsS,
    Spec.Adrs.setTypeAndClear,Spec.FORS_PRF,fors_FORS_PRF_eq,List.append_assoc]
  simp [hj.trans_le bound]
end slhdsa.ParallelLowFors

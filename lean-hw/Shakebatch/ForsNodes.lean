import Shakebatch.ForsMaps
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

/-- Every lane computes Algorithm 15 at its own tree index, at any in-range height. -/
theorem fors_nodes {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (permutes : PermutationCorrect)
    (indices : Array U32 machine.width) (level : U32)
    (bounds : ∀ j < machine.width.val, (indices.val[j]!.val+1)*2^level.val < 2^32) :
    shake.fors_batch.nodes sk seed a indices level ⦃ out =>
      ∀ j < machine.width.val, bytes out.val[j]!.val =
        Spec.forsNode (Shake.params p) (bytes sk.val) indices.val[j]!.val level.val (bytes seed.val) (adrsS a) ⦄ := by
  generalize h : level.val = n at bounds ⊢
  induction n generalizing level indices with
  | zero =>
    have zero : level=0#u32 := by scalar_tac
    unfold shake.fors_batch.nodes
    step with node_addresses N a level indices as ⟨addresses,rows⟩
    simp only [zero,ite_true]
    step with fors_secrets p hp sk seed a indices permutes as ⟨secrets,values⟩
    step with short_fips seed addresses secrets permutes hp.le32 (aligned_hash hp) as ⟨out,hash⟩
    rename_i j hj
    rw [hash j hj,rows j hj,values j hj,Spec.forsNode]
    simp [Spec.F,Shake.params,hp.n_eq,adrsS,zero,List.append_assoc]
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
    unfold shake.fors_batch.nodes
    step with node_addresses N a level indices as ⟨addresses,rows⟩
    simp only [nonzero,ite_false]
    step with left_indices N indices twice as ⟨ls,lidx⟩
    step as ⟨lower,lev⟩
    have lower_n : lower.val=n := by omega
    have lb (j : Nat) (hj : j < machine.width.val) : (ls.val[j]!.val+1)*2^n < 2^32 := by
      rw [lidx j hj]
      have := valid j hj
      have hpow := Nat.one_le_two_pow (n:=n)
      nlinarith
    step with ih ls lower lower_n lb as ⟨left,lv⟩
    step with right_indices N indices twice as ⟨rs,ridx⟩
    have rb (j : Nat) (hj : j < machine.width.val) : (rs.val[j]!.val+1)*2^n < 2^32 := by
      rw [ridx j hj]; exact valid j hj
    step with ih rs lower lower_n rb as ⟨right,rv⟩
    step with pair_fips seed addresses left right permutes hp.le32 (aligned_hash hp) as ⟨out,hash⟩
    rename_i j hj
    rw [hash j hj,rows j hj,lv j hj,rv j hj,lidx j hj,ridx j hj,Spec.forsNode]
    simp [Spec.H,Shake.params,hp.n_eq,adrsS,h,List.append_assoc]

end slhdsa.ShakeBatch

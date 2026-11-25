import Armwide.Xmss.LevelsProgram

open Aeneas Aeneas.Std Result
namespace slhdsa.ArmXmss

def levelSpec {N} (p : params.Params) (seed : hash.Seed N) (sk : Array U8 N)
    (a : address.Adrs) (idx height k : Nat) (roots : Nodes N) :=
  ∀ j<2^(height-k), bytes roots.val[j]!.val = Spec.xmssNode (paramsS p) (bytes sk.val)
    (idx*2^(height-k)+j) k (bytes seed.pk_seed.val) (adrsS a)

private theorem nextLevel {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N)
    (hs : SeedOk seed) (wide : N.val=24 ∨ N.val=32) (enabled : Bool) (sk : Array U8 N)
    (a : address.Adrs) (idx h k : Nat) (first level shifted : U32) (n : Usize) (roots : Nodes N)
    (height : h≤4) (active : k<h) (base : first.val=idx*2^h) (lev : level.val=k+1)
    (shiftedVal : shifted.val=first.val >>> level.val)
    (size : n.val=2^(h-(k+1))) (prior : levelSpec p seed sk a idx h k roots)
    (limit : (idx+1)*2^h≤2^32) :
    let adr := {a with typ:=address.TREE,keypair:=0#u32,word2:=level,word3:=0#u32}
    let packed := pairedBuffer seed.state512 adr shifted roots n enabled
    xmss.arm.batch_root_512_loop0_loop0 ⟨packed.1,n⟩ seed.pk_seed seed.state seed.state512 packed.2 adr shifted
      ⦃ out => levelSpec p seed sk a idx h (k+1) out ⦄ := by
  have small : n.val≤8 := by rw [size]; interval_cases h <;> interval_cases k <;> decide
  have spread : 2^(h-k)=2*2^(h-(k+1)) := by
    rw [show h-k=(h-(k+1))+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have off : first.val >>> level.val = idx*2^(h-(k+1)) := by
    rw [base,lev,Nat.shiftRight_eq_div_pow,show h=(h-(k+1))+(k+1) by omega,Nat.pow_add,← Nat.mul_assoc]
    simp
  have firstEq : shifted.val=idx*2^(h-(k+1)) := shiftedVal.trans off
  have room : shifted.val+n.val≤2^32 := by
    rw [firstEq,size,← Nat.add_one_mul]
    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))) limit
  apply WP.spec_mono (full_level p hp seed hs wide enabled _ shifted roots n small room)
  intro out done j hj
  rw [done j (by omega)]
  obtain ⟨hl,hr⟩ : 2*j<2^(h-k) ∧ 2*j+1<2^(h-k) := by omega
  simp only [parent,prior _ hl,prior _ hr,Spec.xmssNode,firstEq,lev]
  have leftEq : idx*2^(h-k)+2*j=2*(idx*2^(h-(k+1))+j) := by rw [spread]; ring
  have rightEq : idx*2^(h-k)+(2*j+1)=2*(idx*2^(h-(k+1))+j)+1 := by omega
  rw [leftEq,rightEq]
  simp only [adrsS,Spec.Adrs.setTypeAndClear,Spec.TREE,address.TREE,← lev,firstEq]
  rfl

abbrev Levels := core.ops.range.RangeInclusive U32

theorem reduceTree {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N)
    (hs : SeedOk seed) (wide : N.val=24 ∨ N.val=32) (enabled : Bool) (sk : Array U8 N)
    (a : address.Adrs) (idx : Nat) (height first : U32) (count : Usize)
    (roots : Nodes N) (positive : 0<height.val) (small : height.val≤4)
    (base : first.val=idx*2^height.val) (size : count.val=2^height.val)
    (prior : levelSpec p seed sk a idx height.val 0 roots) (limit : (idx+1)*2^height.val≤2^32) :
    xmss.arm.batch_root_512_loop0 enabled ⟨1#u32,height,false⟩ seed.pk_seed seed.state seed.state512 a first count roots ⦃ out =>
      levelSpec p seed sk a idx height.val height.val out ⦄ := by
  unfold xmss.arm.batch_root_512_loop0
  apply loop.spec_decr_nat
    (measure := fun q : Levels × Nodes N => if q.1.exhausted then 0 else height.val+1-q.1.start.val)
    (inv := fun q => ∃ k, k≤height.val ∧ q.1.end=height ∧
      (if q.1.exhausted then k=height.val else q.1.start.val=k+1 ∧ k<height.val) ∧
      levelSpec p seed sk a idx height.val k q.2)
  · rintro ⟨it,current⟩ ⟨k,bound,last,status,previous⟩
    simp only at last status previous ⊢
    unfold xmss.arm.batch_root_512_loop0.body
    step as ⟨opt,next,iteration⟩
    by_cases stopped : it.exhausted=true
    · simp [stopped] at status iteration
      simp only [iteration.1,step_simps]
      exact status ▸ previous
    · have live : it.exhausted=false := by simpa using stopped
      simp only [live,Bool.false_eq_true,ite_false] at status
      obtain ⟨level,active⟩ := status
      have valid : ¬ it.end.val < it.start.val := by rw [last,level]; omega
      simp only [live,Bool.false_eq_true,false_or,if_neg valid] at iteration
      have item : opt=some it.start := by split at iteration <;> exact iteration.1
      simp only [item,address.Adrs.with_type,address.Adrs.with_word2,bind_ok]
      step as ⟨shifted,shiftedVal⟩
      step as ⟨n,amount⟩
      · rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> omega
      have nval : n.val=2^(height.val-(k+1)) := by
        rw [amount,size,level,Nat.shiftRight_eq_div_pow]
        rw (occs := .pos [1]) [show height.val=(height.val-(k+1))+(k+1) by omega]
        simp [Nat.pow_add]
      simp [lift,Array.to_slice_mut,Array.to_slice,Array.from_slice,parentSlice,Array.length_eq,bind_ok]
      step with nextLevel p hp seed hs wide enabled sk a idx height.val k first it.start shifted n current small active base level shiftedVal nval previous limit as ⟨out,done⟩
      split at iteration
      · rename_i more
        obtain ⟨_,inc,finish,remains⟩ := iteration
        simp only [step_simps,remains,live,Bool.false_eq_true,ite_false]
        exact ⟨⟨k+1,by omega,finish.trans last,by omega,by rw [last] at more; omega,done⟩,by omega⟩
      · rename_i equal
        obtain ⟨_,_,finish,ends⟩ := iteration
        simp only [step_simps,ends,live,Bool.false_eq_true,ite_false,ite_true]
        exact ⟨⟨k+1,by omega,finish.trans last,by rw [last] at equal; omega,done⟩,by omega⟩
  · exact ⟨0,by omega,rfl,⟨by rfl,positive⟩,prior⟩
end slhdsa.ArmXmss

import Parallel.ScalarForsProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelScalarFors
set_option linter.concreteInstances false
set_option maxHeartbeats 1300000
section
variable [host : Host]

private def recursive {N : Usize} (sk seed : Array U8 N) (a : address.Adrs) (i z : U32) : Result (Array U8 N) := do
  let az ← address.Adrs.with_word2 a z
  let ai ← address.Adrs.with_word3 az i
  if z=0#u32 then do
    let secret ← shake.fors.fors_sk_gen sk seed a i
    shake.hash.thash seed ai secret
  else do
    let i1 ← 2#u32 * i
    let z1 ← z-1#u32
    let left ← node sk i1 z1 seed a
    let i2 ← i1+1#u32
    let right ← node sk i2 z1 seed a
    shake.hash.thash_pair seed ai left right

private theorem unfold_node {N : Usize} (sk seed : Array U8 N) (a : address.Adrs) (i z : U32)
    (avail : Bool) (detect : host.probe N=ok avail) : node sk i z seed a =
    if z≥3#u32 ∧ host.width=8#usize ∧ avail=true then host.horizontal sk seed a i z else recursive sk seed a i z := by
  rw [node.eq_def]
  by_cases big : z≥3#u32 <;> by_cases wide : host.width=8#usize <;> cases avail <;>
    simp [big,wide,detect,recursive,bind_ok]

def HorizontalAt {N : Usize} (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) (avail : Bool) :=
  host.width=8#usize → avail=true → ∀ i z : U32, 3≤z.val → z.val≤14 → (i.val+1)*2^z.val≤1048576 →
    host.horizontal sk seed a i z ⦃ r => bytes r.val=Spec.forsNode (Shake.params p) (bytes sk.val) i.val z.val
      (bytes seed.val) (adrsS a) ⦄

theorem node_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (avail : Bool) (detect : host.probe N=ok avail) (horizontal : HorizontalAt p sk seed a avail)
    (i z : U32) (hi : z.val≤14) (room : (i.val+1)*2^z.val≤1048576) :
    node sk i z seed a ⦃ out => bytes out.val=Spec.forsNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄ := by
  generalize e : z.val=n at hi room ⊢
  induction n generalizing i z with
  | zero =>
    have zero : z=0#u32 := by scalar_tac
    subst z
    rw [unfold_node sk seed a i 0#u32 avail detect,if_neg (fun bad => (by decide : ¬(0#u32 ≥ 3#u32)) bad.1)]
    unfold recursive
    step as ⟨az,level⟩
    step as ⟨ai,idx⟩
    simp only [ite_true]
    step with Shake.fors_sk_gen_spec p hp as ⟨v,val⟩
    step with Shake.thash_spec as ⟨r,hash⟩
    simpa only [Spec.forsNode,Spec.F,Shake.params,paramsS_n,hp.n_eq,level,idx,adrsS,val,show (0#u32).val=0 by decide] using hash
  | succ n ih =>
    rw [unfold_node sk seed a i z avail detect]
    split
    · rename_i on;exact e ▸ horizontal on.2.1 on.2.2 i z on.1 (by omega) (by rwa [e])
    · have nz : z≠0#u32 := by scalar_tac
      unfold recursive
      step as ⟨az,level⟩
      step as ⟨ai,idx⟩
      simp only [nz,ite_false]
      have power : 1≤2^n := Nat.one_le_two_pow
      have rightBound : (2*i.val+1+1)*2^n≤1048576 := by
        rw [show 2*i.val+1+1=2*(i.val+1) by omega]
        simpa [Nat.pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using room
      have leftBound : (2*i.val+1)*2^n≤1048576 := (Nat.mul_le_mul_right _ (by omega : 2*i.val+1≤2*i.val+1+1)).trans rightBound
      have small : 2*i.val+2≤1048576 := by nlinarith
      step as ⟨l,lv⟩
      step as ⟨lower,lowerVal⟩
      have lval : l.val=2*i.val := lv
      step with ih l lower (by omega) (by scalar_tac) (lval ▸ leftBound) as ⟨left,L⟩
      step as ⟨r,rv⟩
      have rval : r.val=2*i.val+1 := by rw [rv,lval]
      step with ih r lower (by omega) (by scalar_tac) (rval ▸ rightBound) as ⟨right,R⟩
      step with Shake.pair_spec as ⟨v,hash⟩
      simpa [Spec.forsNode,Spec.H,Shake.params,hp.n_eq,paramsS_n,adrsS,level,idx,lv,rv,e,L,R,lval,rval] using hash

def Writes {N : Usize} (slot : Usize) (value : Spec.Bytes) (out : Usize × Array U8 N) :=
  out.1=slot ∧ bytes out.2.val=value

theorem tickets {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (avail : Bool) (detect : host.probe N=ok avail) (horizontal : HorizontalAt p sk seed a avail)
    (i z : U32) (slot : Usize) (hi : z.val≤14) (room : (i.val+1)*2^z.val≤1048576) :
    let value := Spec.forsNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a)
    (direct_node_ticket sk seed a i z slot ⦃ w => Writes slot value w ⦄) ∧
      (split_node_ticket sk seed a i z slot ⦃ w => Writes slot value w ⦄) := by
  obtain ⟨v,run,bytesEq⟩ := spec_imp_exists (node_spec p hp sk seed a avail detect horizontal i z hi room)
  constructor <;> simp [direct_node_ticket,split_node_ticket,run,bind_ok,Writes,bytesEq]

end

noncomputable def wide (plat : WidthEight.Platform) (p : params.Params) : Host where
  width := 8#usize
  probe := plat.probe
  horizontal := @(plat.forsTrees p).node

theorem wide_tickets (plat : WidthEight.Platform) {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (domain : ForsHorizontal.Domain a)
    (i z : U32) (slot : Usize) (hi : z.val≤14) (room : (i.val+1)*2^z.val≤1048576) :
    let value := Spec.forsNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a)
    (@direct_node_ticket (wide plat p) N sk seed a i z slot ⦃ w => Writes slot value w ⦄) ∧
      (@split_node_ticket (wide plat p) N sk seed a i z slot ⦃ w => Writes slot value w ⦄) := by
  apply @tickets (wide plat p) N p hp sk seed a (plat.available N) (WidthEight.probe_eq plat N) _ i z slot hi room
  intro _ available idx h lo bound fit
  cases plat with
  | apple sha3 =>
    exact @ForsTreeApple.slhdsa.ForsHorizontal.subtree_spec ((WidthEight.Platform.apple sha3).fused p) N
      p hp sk seed a idx h domain lo bound fit (NativeVerify.apple sha3)
  | x86 =>
    exact @ForsTreeX86.slhdsa.ForsHorizontal.subtree_spec (WidthEight.Platform.x86.fused p) N
      p hp sk seed a idx h domain lo bound fit (NativeVerify.x86 (Bool.and_eq_true_iff.mp available).2)

def narrow : Host where
  width := 3#usize
  probe := ShakeBatch.Linux.available
  horizontal := fun _ _ _ _ _ => fail .panic

theorem narrow_tickets {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (i z : U32) (slot : Usize) (hi : z.val≤14) (room : (i.val+1)*2^z.val≤1048576) :
    let value := Spec.forsNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a)
    (@direct_node_ticket narrow N sk seed a i z slot ⦃ w => Writes slot value w ⦄) ∧
      (@split_node_ticket narrow N sk seed a i z slot ⦃ w => Writes slot value w ⦄) := by
  have detected : narrow.probe N=ok true := by
    change ShakeBatch.shake.batch.available KldispRust.shake256.parallel.available N=ok true
    rw [ShakeBatch.available_for_fips _ p hp];rfl
  exact @tickets narrow N p hp sk seed a true detected (fun impossible =>
    False.elim ((by decide : (3#usize)≠8#usize) impossible)) i z slot hi room

end slhdsa.ParallelScalarFors

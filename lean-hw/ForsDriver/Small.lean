import ForsDriver.Prepare
import ForsDriver.Low
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ForsDriver
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable [kernel : Fused.Kernel] [trees : Trees]

private theorem emptyRow {N : Usize} (sk seed : Array U8 N) (a : address.Adrs)
    (height : U32) (stride t : Usize) (leaf : U32) (sig : Buffer) (small : height.val < 3) :
    sign_loop8_loop0 ⟨3#u32,height⟩ sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 stride sig t leaf
      ⦃ out => out=sig ⦄ := by
  unfold sign_loop8_loop0
  apply loop.spec_decr_nat (measure:=fun _ => 0)
    (inv:=fun q : core.ops.range.Range U32 × Buffer => q.1=⟨3#u32,height⟩ ∧ q.2=sig)
  · rintro ⟨it,out⟩ ⟨rfl,rfl⟩
    unfold sign_loop8_loop0.body
    step with core.iter.range.IteratorRange.next_U32_none_spec ⟨3#u32,height⟩ (by change height.val ≤ 3;omega) as ⟨_,_,tag,_⟩
    simp only [tag,step_simps]
  · exact ⟨rfl,rfl⟩

private theorem emptyTail {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs) (stride : Usize) (sig : Buffer)
    (size : choices.length ≤ 35) (digits : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val) (small : p.a.val < 3) :
    sign_loop8 ⟨0#usize,choices.len⟩ choices sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 p.a stride sig
      ⦃ out => out=sig ⦄ := by
  unfold sign_loop8
  apply range_fold (sign_loop8.body choices sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 p.a stride)
    choices.len sig (fun _ out => out=sig) rfl
  · intro it cur stop live eql
    change it.start.val < choices.length at live
    unfold sign_loop8.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    obtain ⟨leaf,run,_,_⟩ := read_absolute choices p.a it.start hp.valid.a_le live size (digits _ live)
    rw [read_bind choices p.a it.start run]
    step with emptyRow sk seed a p.a stride it.start leaf cur small as ⟨out,unchanged⟩
    exact ⟨next,out,rfl,ends.trans stop,inc,unchanged.trans eql⟩
  · intro it cur last stop
    obtain ⟨_,no⟩ := range_done it _ stop last
    simp [sign_loop8.body,no]

private def staged {N : Usize} (p : params.Params) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs) := do
  let (stride,tree,s0) ← prepare p choices sk seed a
  let s1 ← low0 p choices sk seed a stride s0
  let out ← if p.a>1#u32 then low1 p choices sk seed a tree stride s1 else ok s1
  sign_loop8 ⟨0#usize,choices.len⟩ choices sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 p.a stride out

private theorem staged_eq {N : Usize} (p : params.Params) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs) (hk : choices.length ≤ 35) (pos : 0 < p.a.val) (small : p.a.val < 3) :
    sign p choices sk seed a=staged p choices sk seed a := by
  have bound : choices.len ≤ params.K_MAX := by rw [params.K_MAX];exact hk
  have positive : p.a>0#u32 := pos
  have omitTwo : ¬p.a>2#u32 := by change ¬2 < p.a.val;omega
  by_cases one : p.a>1#u32
  all_goals simp only [sign,staged,prepare,low0,low1,leafPrefix,pairPrefix,positive,one,omitTwo,ite_true,ite_false,
    bne_self_eq_false,Bool.false_or,decide_eq_true bound,massert,bind_tc_eq,Std.bind_assoc,bind_ok]
  all_goals rfl

theorem sign_small_spec {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (count : choices.length=p.k.val) (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) (small : p.a.val < 3) :
    sign p choices sk seed a ⦃ out => bytes out.val=(List.range p.k.val).flatMap (forsSignTree (Shake.params p)
        (bytes sk.val) (bytes seed.val) (adrsS a) (nats choices.val)) ∧ out.length=p.k.val*(1+p.a.val)*N.val ⦄ := by
  have hk : choices.length ≤ 35 := count.symm ▸ hp.valid.k_le
  have pos : 0 < p.a.val := hp.valid.a_pos
  rw [staged_eq p choices sk seed a hk pos small]
  unfold staged
  step with prepare_spec p hp choices sk seed a domain count index perm as ⟨initial,shape,eqTree,zero⟩
  obtain ⟨stride,tree,s0⟩ := initial
  dsimp only at shape eqTree zero ⊢
  step with low0_spec p hp choices sk seed a stride s0 hk index domain shape perm pos zero as ⟨s1,one⟩
  have finish (cur : Buffer) (ready : Fields N.val choices.length (p.a.val+1) stride.val
      (treeBlock p sk seed a choices) (fun _ _ => True) cur) :
      sign_loop8 ⟨0#usize,choices.len⟩ choices sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 p.a stride cur
      ⦃ out => bytes out.val=(List.range p.k.val).flatMap (forsSignTree (Shake.params p)
        (bytes sk.val) (bytes seed.val) (adrsS a) (nats choices.val)) ∧ out.length=p.k.val*(1+p.a.val)*N.val ⦄ := by
    apply WP.spec_mono (emptyTail p hp choices sk seed a stride cur hk index small)
    rintro out rfl
    have done : SigPrefix p sk seed a choices stride.val choices.length out :=
      ⟨ready.1,fun t ht z hz b hb => ready.2 t ht z (by omega) b hb trivial⟩
    refine ⟨prefix_bytes p hp sk seed a choices out count (shape ▸ done),?_⟩
    rw [ready.1,count,shape,Nat.mul_assoc,Nat.add_comm]
  split
  · rename_i yes
    have hi : 1 < p.a.val := yes
    step with low1_spec p hp choices sk seed a tree stride s1 hk index domain eqTree shape perm hi one as ⟨s2,two⟩
    exact finish s2 (two.mono (by intros;omega))
  · rename_i no
    change ¬ 1 < p.a.val at no
    exact finish s1 (one.mono (by intros;omega))
end slhdsa.ForsDriver

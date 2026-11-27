import Parallel.SignJoinValues
import Shakebatch.WidthThreeNative
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelSignJoin
open ParallelFused.Slots

def JoinLawAt (join : Join) (N : Usize) (p : params.Params) : Prop :=
  ∀ (md : Slice U8) (sk seed : Array U8 N)
    (a : address.Adrs) (r : Array U8 N) (tree : U64) (leaf : U32) (threads : Usize),
    2 ≤ threads.val → md.length=(Shake.params p).mdBytes → tree.val<2^(p.h.val-p.hp.val) →
    leaf.val<2^p.hp.val → adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear
      Spec.FORS_TREE with keypair:=leaf.val} →
    join p md sk seed a r tree leaf threads ⦃ cells =>
      Joined N (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a) tree.val leaf.val cells ⦄

@[instance_reducible] def worker (threads : Usize) (join : Join) : ParallelCaller.Worker ParallelCaller.ShakeSeed :=
  ⟨@run (ok threads) join⟩

theorem result_at (threads : Usize) (join : Join) {N : Usize}
    (p : params.Params) (hp : PN p N)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N)
    (tree : U64) (leaf : U32) (leafLt : leaf.val<2^p.hp.val)
    (joined : 2≤threads.val → join p md sk seed a r tree leaf threads ⦃ cells =>
      Joined N (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a) tree.val leaf.val cells ⦄) :
    (worker threads join).run p md sk seed a r tree leaf ⦃ res => match res with
      | none => threads < 2#usize ∨ p.hp=0#u32
      | some out => Output (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
          (bytes r.val) tree.val leaf.val (bytes out.val) ⦄ := by
  unfold worker run
  simp only [bind_ok]
  split
  · simp_all
  · rename_i enough
    split
    · simp_all
    · simp only [lift,bind_ok]
      step with joined (by scalar_tac) as ⟨f,t,w,get⟩
      obtain ⟨forest,auth,forestCell,authCell,ready⟩ := get
      simp only at forestCell authCell ready
      subst f t
      simp only [readCell,bind_ok,core.option.Option.expect,ofOption]
      let P := Shake.params p
      have valid : P.Valid := by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := hp.valid;constructor <;> assumption
      have d : (UScalar.cast .Usize p.d).val=P.d := by simp [P,Shake.params,paramsS_d]
      have h : (UScalar.cast .Usize p.hp).val=P.hp := by simp [P,Shake.params,paramsS_hp]
      have forestOk := ready.forestRows.trans (ParallelCached.fors_bytes P _ _ _ _)
      have treeOk := layers_fips valid leafLt ready
      step with sig_bytes_spec p hp.valid as ⟨size,capacity,sizes⟩
      have rl : r.to_slice.length=N.val := by simp
      have ll : (through (layers auth w P.hp) P.d).length = P.d*P.xmssSigBytes := by
        rw [← bytes_length,treeOk,Spec.htSign_length P valid]
      have fl : forest.deref.length=P.forsSigBytes := by
        change forest.deref.val.length=_
        rw [vec_deref_val,← bytes_length,forestOk,Spec.forsSign_length P valid]
      have bound : N.val+P.forsSigBytes+P.d*P.xmssSigBytes ≤ Usize.max := by
        have actual : size.val≤Usize.max := by scalar_tac
        rw [sizes] at actual
        change _ ≤ _ at actual
        change N.val+ (paramsS p).forsSigBytes + (paramsS p).d * (paramsS p).xmssSigBytes ≤ _
        rw [←hp.n_eq]
        exact actual
      have empty : (alloc.vec.Vec.with_capacity U8 size).length=0 := rfl
      have emptyVal : (alloc.vec.Vec.with_capacity U8 size).val=[] := rfl
      step with util_extend_from_slice_u8_spec (alloc.vec.Vec.with_capacity U8 size) r.to_slice (by rw [empty,rl]; omega) as ⟨init,head,il⟩
      step with util_extend_from_slice_u8_spec init forest.deref (by rw [il,empty,rl,fl];omega) as ⟨base,baseVal,bl⟩
      have fit : base.length+(through (layers auth w P.hp) P.d).length≤Usize.max := by
        rw [bl,il,empty,rl,fl,ll]
        omega
      step with layer_copy (UScalar.cast .Usize p.hp) (UScalar.cast .Usize p.d) auth w base
        (by rw [d,h];exact ready.authSize) (by rw [d];exact ready.wotsSize)
        (by intro j jl;obtain ⟨row,pub,_⟩ := ready.wotsRow j (d ▸ jl);exact ⟨row,pub⟩) (by rwa [d,h]) as ⟨out,layout⟩
      obtain ⟨expected,published,shape⟩ := constructed P valid (bytes md.val) (bytes sk.val) (bytes seed.val)
        (adrsS a) (bytes r.val) tree.val leaf.val 1 leafLt (by decide)
      have equal : bytes out.val=expected := by
        rw [shape,layout,baseVal,head,d,h]
        rw [emptyVal,List.nil_append,Array.val_to_slice,vec_deref_val]
        simp only [bytes,List.map_append] at treeOk forestOk ⊢
        rw [treeOk,forestOk]
      rw [equal]
      exact published

theorem result (threads : Usize) (join : Join) {N : Usize}
    (p : params.Params) (hp : PN p N) (joined : JoinLawAt join N p)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N)
    (tree : U64) (leaf : U32) (mdLen : md.length=(Shake.params p).mdBytes)
    (treeLt : tree.val<2^(p.h.val-p.hp.val)) (leafLt : leaf.val<2^p.hp.val)
    (address : adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear Spec.FORS_TREE with keypair:=leaf.val}) :
    (worker threads join).run p md sk seed a r tree leaf ⦃ res => match res with
      | none => threads < 2#usize ∨ p.hp=0#u32
      | some out => Output (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)
          (bytes r.val) tree.val leaf.val (bytes out.val) ⦄ := by
  exact result_at threads join p hp md sk seed a r tree leaf leafLt
    (fun enough => joined md sk seed a r tree leaf threads enough mdLen treeLt leafLt address)

theorem worker_correct (threads : Usize) (join : Join) {N : Usize}
    (p : params.Params) (hp : PN p N) (joined : JoinLawAt join N p) :
    ParallelCaller.WorkerCorrect (worker threads join) (N:=N) p (Shake.params p) (fun s => bytes s.val) (fun _ => True) := by
  intro md sk seed a r tree leaf _ mdLen treeLt leafLt address
  apply WP.spec_mono (result threads join p hp joined md sk seed a r tree leaf mdLen treeLt leafLt address)
  intro ret value
  cases ret <;> simp_all

def linuxPublished (threads : Usize) (join : Join) (joined : ∀ {N} p, PN p N → JoinLawAt join N p) : WidthThree.PublishedWorker :=
  ⟨worker threads join,fun p hp => worker_correct threads join p hp (joined p hp)⟩

end slhdsa.ParallelSignJoin

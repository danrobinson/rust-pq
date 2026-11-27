import Buffered.SmallWotsProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered.SmallWots
open ShakeBatch NativeVerify Spec.Keccak
set_option linter.concreteInstances false
set_option maxHeartbeats 1300000
variable [kernel : Fused.Kernel]
local instance initMachine : Machine := Fused.machine kernel

theorem tags (K : Usize) (first : U32) (a : address.Adrs) (n : Usize) (pk : Matrix 8#usize)
    (width : K.val≤8) (room : first.val+K.val≤512) (size : n.val≤4) :
    leaves_loop1 ⟨0#usize,K⟩ first n pk ⦃ out => ∀ k l, l<K.val → cell out k l =
      if k=n.val+2 then addressWord (Fused.laneAddress a address.WOTS_PK first.val l) 2 else cell pk k l ⦄ := by
  unfold leaves_loop1
  apply WP.spec_mono (range_fold (leaves_loop1.body first n) K pk (fun count s =>
    ∀ k l, l<K.val → cell s k l = if k=n.val+2 ∧ l<count then addressWord
      (Fused.laneAddress a address.WOTS_PK first.val l) 2 else cell pk k l) (by simp) ?_ ?_)
  · intro out h k l hl; simpa only [hl,and_true] using h k l hl
  · intro it st stop live prior
    unfold leaves_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag,ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
    have cast : (UScalar.cast .U32 it.start).val=it.start.val := by scalar_tac
    step as ⟨x,xval⟩
    step as ⟨top,_,bits⟩
    step as ⟨r,rval⟩
    step as ⟨row,back,read,store⟩
    step as ⟨row',update⟩
    have xeq : x.val=first.val+it.start.val := by omega
    have xword : (⟨BitVec.ofNat 32 (first.val+it.start.val)⟩ : U32)=x := by
      rw [←xeq]; cases x; simp [UScalar.val,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    refine ⟨next,back row',rfl,ends.trans stop,inc,?_⟩
    intro k l hl
    rw [store,update,read,←getElem!_pos,cell_write _ _ _ _ (by omega) (by change it.start.val<8;omega),rval,prior k l hl,inc]
    by_cases hit : k=n.val+2 ∧ l=it.start.val
    · obtain ⟨rfl,rfl⟩ := hit
      simp only [and_self,ite_true,Nat.lt_succ_self,true_and,Fused.address_tag,xword]
      exact congrArg (fun z : BitVec 64 => cache.builder.nativeShake.Vector.Fused.addressLow address.WOTS_PK ||| z) bits
    · have agree : (k=n.val+2 ∧ l < it.start.val+1) ↔ k=n.val+2 ∧ l < it.start.val := by omega
      simp only [hit,ite_false,agree]
  · intro it st last stop
    unfold leaves_loop1.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last,stop]))
    simp [no,tag]

def front (n : Usize) (sw : Array U64 4#usize) (w0 w1 : U64) := do
  let zero := Array.repeat 25#usize (Array.repeat 8#usize 0#u64)
  let base ← leaves_loop0 ⟨0#usize,n⟩ sw zero
  let low ← Array.update base n (Array.repeat 8#usize w0)
  let r ← n + 1#usize
  Array.update low r (Array.repeat 8#usize w1)

def init (K : Usize) (first : U32) (n : Usize) (sw : Array U64 4#usize) (w0 w1 : U64) := do
  let body ← front n sw w0 w1
  leaves_loop1 ⟨0#usize,K⟩ first n body

private theorem reference_row (initialRows : Matrix 8#usize) (r0 : Usize) (t : Array U64 8#usize) (size : r0.val≤4) :
    (do let r ← r0 + 2#usize
        Array.update initialRows r t) ⦃ s => ∀ k l, cell s k l =
      if k=r0.val+2 then t.val[l]!.bv else cell initialRows k l ⦄ := by
    step as ⟨r,rv⟩
    step as ⟨s,store⟩
    rename_i k l
    rw [store,Fused.Stream.row _ _ _ _ _ (by omega),rv]

theorem init_keys {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N) (a : address.Adrs)
    (first : U32) (K n pos : Usize) (sw : Array U64 4#usize) (w0 w1 : U64)
    (width : K.val≤8) (room : first.val+K.val≤512) (nval : n.val=N.val/8) (off : pos.val=n.val+4)
    (seedWords : ∀ k<n.val, sw.val[k]!.bv=inputWord seed.val k)
    (lo : w0.bv=addressWord a 0) (hi : w1.bv=addressWord a 1) :
    init K first n sw w0 w1 ⦃ out => ∀ l<K.val, (ShakeBatch.lane out l,8*pos.val)=
      (bytes seed.val ++ (Spec.wotsPkAdrs (adrsS (Fused.laneAddress a address.WOTS_HASH first.val l))).bytes).foldl feed initial ⦄ := by
  obtain ⟨t,_,words⟩ := spec_imp_exists (Fused.pk_lanes N a first (by omega))
  have ref := Fused.Stream.init_keys p hp seed a first.val n pos sw w0 w1 t nval off seedWords lo hi words
  have size : n.val≤4 := by have := hp.le32; omega
  have frontReady : front n sw w0 w1 ⦃ _ => True ⦄ := by
    unfold front
    have seedOK := Fused.seed_prefix n sw (Array.repeat 25#usize (Array.repeat 8#usize 0#u64)) size
    change leaves_loop0 _ _ _ ⦃ _ ⦄ at seedOK
    step with seedOK
    step*
  obtain ⟨initialRows,got,_⟩ := spec_imp_exists frontReady
  have equiv : Fused.Stream.init n sw w0 w1 t = (do let b ← front n sw w0 w1
                                                    let r ← n + 2#usize
                                                    Array.update b r t) := by
    simp only [Fused.Stream.init,front,bind_tc_eq,Std.bind_assoc,bind_ok]
    rfl
  rw [equiv,got] at ref
  simp only [bind_ok] at ref
  obtain ⟨refRows,run,values⟩ := spec_imp_exists ref
  unfold init
  simp only [got,bind_tc_eq,bind_ok]
  apply WP.spec_mono (tags K first a n initialRows width room size)
  intro out writes l hl
  refine Eq.trans ?_ (values l (hl.trans_le width))
  refine Prod.ext ?_ rfl
  change ShakeBatch.lane out l=ShakeBatch.lane refRows l
  apply ext25 _ _ (by simp [ShakeBatch.lane]) (by simp [ShakeBatch.lane])
  intro k hk
  have reference := reference_row initialRows n t size
  rw [run] at reference
  simp only [WP.spec_ok] at reference
  rw [show (ShakeBatch.lane out l)[k]! = _ from ofFnAt _ k hk,
      show (ShakeBatch.lane refRows l)[k]! = _ from ofFnAt _ k hk,writes k l hl,reference k l,words l (by omega)]

end slhdsa.Buffered.SmallWots

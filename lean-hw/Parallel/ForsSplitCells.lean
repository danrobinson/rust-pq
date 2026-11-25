import Parallel.ForsReducedReceipt
import Parallel.RawChunkLayout
import Parallel.SignJoinInterpreter
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors
open ParallelRawChunks (collect collect_ok)

def physical {N} (n : Nat) (row : Nat → Cell N) : Cells N :=
  ParallelSignJoin.boxed ((List.range n).map (fun i => if (row i).1.val=i then some (row i).2 else none))

private theorem physical_spec {N} (n : Nat) (row : Nat → Cell N) (bound : n≤Usize.max)
    (dest : ∀ i<n, (row i).1.val=i) :
    (physical n row).length=n ∧ ∀ i<n, (physical n row).val[i]! = some (row i).2 := by
  have len : ((List.range n).map (fun i => if (row i).1.val=i then some (row i).2 else none)).length≤Usize.max := by simpa using bound
  simp only [physical,ParallelSignJoin.boxed,List.take_of_length_le len,alloc.vec.Vec.length,alloc.vec.Vec.from_val,List.length_map,List.length_range,true_and]
  intro i hi
  rw [getElem!_pos _ i (by simpa using hi),List.getElem_map,List.getElem_range,if_pos (dest i hi)]

def indexSize (c : Nat) : Usize := ⟨BitVec.ofNat _ c⟩
def indexWord (c : Nat) : U32 := ⟨BitVec.ofNat 32 c⟩

theorem chunk_small {N} (d : Data N) (v : Valid d) (j sub : U32) (field : j.val<d.p.a.val) :
    2^(j.val-sub.val)≤16384 := by
  have h : d.p.a.val≤14 := v.pn.valid.a_le
  exact Nat.pow_le_pow_right (by decide : 0<2) (show j.val-sub.val≤14 by omega)

private theorem size_exact (c : Nat) (small : c≤49152) : (indexSize c).val=c := by
  apply Nat.mod_eq_of_lt
  have h := System.Platform.le_numBits
  exact lt_of_lt_of_le (show c<2^32 by omega) (Nat.pow_le_pow_right (by decide) h)

noncomputable def scalarJob {N} (host : ParallelScalarFors.Platform) (d : Data N) (sat : Bool) (t j sub : U32) (c : Usize) :=
  ParallelScalarFors.run (ParallelScalarFors.actions host d.p d.sk d.seed d.addr).2
    ((if sat then ParallelScalarFors.prepare_saturating else ParallelScalarFors.prepare_split)
      t d.p.a j d.choices.val[t.val]! sub 0#usize c)

noncomputable def buildScalarMerge {N} (host : ParallelScalarFors.Platform) (d : Data N) (sat : Bool) (t j sub : U32) :
    Result (ScalarMerge N) := do
  let count := 2^(j.val-sub.val)
  let jobs ← collect (fun i => scalarJob host d sat t j sub (indexSize i)) (List.range count)
  ok ⟨t,j,sub,0#usize,alloc.vec.Vec.new _,physical count (fun i => jobs[i]!)⟩

theorem scalarJob_runs {N} (host : ParallelScalarFors.Platform) (d : Data N) (valid : Valid d) (sat : Bool)
    (t j sub : U32) (tree : t.val<d.p.k.val) (field : j.val<d.p.a.val) (lower : sub.val<j.val)
    (i : Nat) (hi : i<2^(j.val-sub.val)) : ∃ row, scalarJob host d sat t j sub (indexSize i)=ok row ∧ row.1.val=i := by
  have small := chunk_small d valid j sub field
  have mx : 2^32-1≤Usize.max := by agrind
  have iv := size_exact i (by omega)
  obtain ⟨w,call,dest,_⟩ := spec_imp_exists (ParallelScalarFors.split_published host d.p valid.pn d.sk d.seed d.addr
    valid.domain sat t d.p.a j d.choices.val[t.val]! sub 0#usize (indexSize i) (tree.trans_le valid.pn.valid.k_le)
    valid.pn.valid.a_le field (valid.digits _ (valid.count ▸ tree)) lower (by rw [iv];exact hi) (by scalar_tac))
  exact ⟨w,call,by simpa [iv] using dest⟩

theorem buildScalarMerge_spec {N} (host : ParallelScalarFors.Platform) (d : Data N) (valid : Valid d) (sat : Bool)
    (t j sub : U32) (tree : t.val<d.p.k.val) (field : j.val<d.p.a.val) (lower : sub.val<j.val) :
    buildScalarMerge host d sat t j sub ⦃ m => m.Ready host d sat ∧ m.t=t ∧ m.j=j ∧ m.sub=sub ⦄ := by
  let count := 2^(j.val-sub.val)
  have small : count≤16384 := chunk_small d valid j sub field
  have mx : 2^32-1≤Usize.max := by agrind
  let f := fun i => scalarJob host d sat t j sub (indexSize i)
  have total := scalarJob_runs host d valid sat t j sub tree field lower
  obtain ⟨jobs,run,len,each⟩ := collect_ok f (List.range count) (fun i mem => by
    obtain ⟨w,call,_⟩ := total i (List.mem_range.mp mem);exact ⟨w,call⟩)
  have atJob (i : Nat) (hi : i<count) : f i=ok jobs[i]! := by
    have v := each i (by simpa using hi)
    rwa [getElem!_pos (List.range count) i (by simpa using hi),List.getElem_range] at v
  have dest (i : Nat) (hi : i<count) : jobs[i]!.1.val=i := by
    obtain ⟨w,call,whereAt⟩ := total i hi
    change f i=ok w at call
    rw [atJob i hi] at call
    exact (Result.ok_injective call).symm ▸ whereAt
  obtain ⟨size,slots⟩ := physical_spec count (fun i => jobs[i]!) (by omega) dest
  unfold buildScalarMerge
  change (do let jobs ← collect f (List.range count);ok (ScalarMerge.mk t j sub 0#usize (alloc.vec.Vec.new _) (physical count (fun i => jobs[i]!)))) ⦃ _ ⦄
  rw [run,bind_ok,WP.spec_ok]
  refine ⟨⟨tree,field,lower,?_,?_,?_⟩,rfl,rfl,rfl⟩
  · simpa [count] using size.ge
  · change 0<Usize.max;omega
  · intro c part w call
    have hi : c.val<count := part
    have eq : indexSize c.val=c := UScalar.eq_of_val_eq (size_exact _ (by omega))
    have actual := atJob c.val hi
    change scalarJob host d sat t j sub (indexSize c.val)=ok jobs[c.val]! at actual
    rw [eq] at actual
    have same := Result.ok_injective (actual.symm.trans call)
    rw [←same];unfold Writes
    rw [dest _ hi];exact slots _ hi

noncomputable def groupJob {N} (d : Data N) (first : U16) (active height low : U8) (chunks : Usize) (c : U32) :=
  @ParallelForsTicket.split_ticket unreachableHigh N d.sk d.seed d.addr d.choices d.p.a first active height low c 0#usize chunks

noncomputable def buildGroupMerge {N} (d : Data N) (first : U16) (active height low : U8) (j sub : U32) :
    Result (GroupMerge N) := do
  let count := 2^(j.val-sub.val)
  let chunks := indexSize count
  let jobs ← collect (fun i => groupJob d first active height low chunks (indexWord i)) (List.range count)
  let cells := physical (active.val*count) (fun i => jobs[i%count]!.val[i/count]!)
  ok ⟨first,active,height,low,j,sub,0#usize,chunks,alloc.vec.Vec.new _,cells⟩

theorem groupJob_runs {N} (d : Data N) (valid : Valid d) (first : U16) (active height low : U8) (j sub : U32)
    (field : height.val<d.p.a.val) (lower : low.val<height.val) (hj : j.val=height.val) (hs : sub.val=low.val)
    (on : 0<active.val) (width : active.val≤3) (range : first.val+active.val≤d.choices.length)
    (i : Nat) (hi : i<2^(j.val-sub.val)) : ∃ rows, groupJob d first active height low (indexSize (2^(j.val-sub.val))) (indexWord i)=ok rows ∧
      ∀ lane<active.val, rows.val[lane]!.1.val=lane*2^(j.val-sub.val)+i := by
  let count := 2^(j.val-sub.val)
  let chunks := indexSize count
  have small : count≤16384 := chunk_small d valid j sub (by rwa [hj])
  have cv : chunks.val=count := size_exact _ (by omega)
  have maxCount := Nat.mul_le_mul width small
  have mx : 2^32-1≤Usize.max := by agrind
  have fits : active.val*count≤Usize.max := by omega
  have iv : (indexWord i).val=i := Nat.mod_eq_of_lt (by change i<2^32;omega)
  obtain ⟨rows,call,values⟩ := spec_imp_exists (@ParallelForsTicket.split_ticket_spec unreachableHigh N d.p valid.pn
    d.sk d.seed d.addr d.choices first active height low (indexWord i) 0#usize chunks valid.domain valid.pn.valid.a_le field
    (valid.count ▸ valid.pn.valid.k_le) on width range valid.digits lower.le (by simpa [count,hj,hs] using cv)
    (by rwa [iv,cv]) (by simpa [cv] using fits))
  refine ⟨rows,call,fun lane hl => ?_⟩
  simpa [cv,iv] using (values lane hl).1

theorem buildGroupMerge_spec {N} (d : Data N) (valid : Valid d) (first : U16) (active height low : U8) (j sub : U32)
    (field : height.val<d.p.a.val) (lower : low.val<height.val) (hj : j.val=height.val) (hs : sub.val=low.val)
    (on : 0<active.val) (width : active.val≤3) (range : first.val+active.val≤d.choices.length) :
    buildGroupMerge d first active height low j sub ⦃ m => m.Ready d ∧ m.first=first ∧ m.active=active ∧ m.j=j ∧ m.sub=sub ⦄ := by
  let count := 2^(j.val-sub.val)
  let chunks := indexSize count
  let f := fun i => groupJob d first active height low chunks (indexWord i)
  have small : count≤16384 := chunk_small d valid j sub (by rwa [hj])
  have positive : 0<count := Nat.two_pow_pos _
  have cv : chunks.val=count := size_exact _ (by omega)
  have maxCount := Nat.mul_le_mul width small
  have mx : 2^32-1≤Usize.max := by agrind
  have fits : active.val*count≤Usize.max := by omega
  have total := groupJob_runs d valid first active height low j sub field lower hj hs on width range
  obtain ⟨jobs,run,len,each⟩ := collect_ok f (List.range count) (fun i mem => by
    obtain ⟨r,call,_⟩ := total i (List.mem_range.mp mem);exact ⟨r,call⟩)
  have atJob (i : Nat) (hi : i<count) : f i=ok jobs[i]! := by
    have v := each i (by simpa using hi)
    rwa [getElem!_pos (List.range count) i (by simpa using hi),List.getElem_range] at v
  have dest (i : Nat) (hi : i<count) (l : Nat) (hl : l<active.val) : jobs[i]!.val[l]!.1.val=l*count+i := by
    obtain ⟨r,call,whereAt⟩ := total i hi
    change f i=ok r at call
    rw [atJob i hi] at call
    exact (Result.ok_injective call).symm ▸ whereAt l hl
  let row := fun i => jobs[i%count]!.val[i/count]!
  have physicalDest (i : Nat) (hi : i<active.val*count) : (row i).1.val=i := by
    rw [show (row i).1.val=(i/count)*count+i%count from dest _ (Nat.mod_lt _ positive) _ ((Nat.div_lt_iff_lt_mul positive).2 hi)]
    exact Nat.div_add_mod' i count
  obtain ⟨size,slots⟩ := physical_spec _ row fits physicalDest
  unfold buildGroupMerge
  change (do let js ← collect f (List.range count); ok (GroupMerge.mk first active height low j sub 0#usize chunks (alloc.vec.Vec.new _)
       (physical (active.val*count) (fun i => js[i%count]!.val[i/count]!)))) ⦃ _ ⦄
  rw [run,bind_ok,WP.spec_ok]
  refine ⟨⟨field,lower,hj,hs,width,range,?_,cv,?_,?_⟩,rfl,rfl,rfl,rfl⟩
  · change 0+active.val≤Usize.max;omega
  · simpa [cv,row] using size.ge
  · intro c hc r call l hl
    change l<active.val at hl
    have hi : c.val<count := by simpa only [cv] using hc
    have eq : indexWord c.val=c := UScalar.eq_of_val_eq (Nat.mod_eq_of_lt c.bv.isLt)
    have actual := atJob c.val hi
    change groupJob d first active height low chunks (indexWord c.val)=ok jobs[c.val]! at actual
    rw [eq] at actual
    have same := Result.ok_injective (actual.symm.trans call)
    rw [←same];unfold Writes
    rw [dest _ hi _ hl]
    have upper := Nat.mul_le_mul_right count (show l+1≤active.val by omega)
    rw [Nat.add_one_mul] at upper
    have read := slots (l*count+c.val) (by omega)
    have mod : (l*count+c.val)%count=c.val := by rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hi]
    have div : (l*count+c.val)/count=l := by rw [Nat.mul_comm l count,Nat.mul_add_div positive,Nat.div_eq_of_lt hi,Nat.add_zero]
    change (physical _ row).val[l*count+c.val]! = _
    simpa only [row,mod,div] using read

end slhdsa.RawFors

import Parallel.ReduceNativeRounds
import Slhdsa.Proofs.Xmss
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelReduceNative

private theorem map_reads {N} (xs : List (Array U8 N)) :
    (xs.map some).mapM (fun slot => do
      let (v,_) ← reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N.call_mut (N:=N) () slot
      ok v) = ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.mapM_cons,reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N.call_mut,
      getCell,core.option.Option.expect,Result.ofOption,bind_ok,bind_tc_eq] at ih ⊢
    rw [ih]; simp [bind_tc_eq,bind_ok,pure_tc_eq]

theorem collect_ready {N} (slots : Slice (Option (Array U8 N))) (rows : Rows N)
    (ready : slots.val=rows.val.map some) : collectRows slots=ok rows := by
  unfold collectRows
  rw [ready,map_reads]
  simp [rows.property]

/-- A completed ticket for each physical slot suffices to construct the vector
consumed by the native reducer, regardless of the order of publication. -/
theorem published_layer {N : Usize} (slots : Slice (Option (Array U8 N)))
    (node : Nat → Nat → Spec.Bytes) (root height sub : Nat)
    (size : slots.length=2^(height-sub))
    (ready : ∀ j<slots.length, ∃ v, slots.val[j]! = some v ∧
      bytes v.val=node sub (root*2^(height-sub)+j)) :
    ∃ rows : Rows N, slots.val=rows.val.map some ∧ Layer node root height sub rows := by
  let xs := slots.val.map (fun x => x.getD default)
  have bound : xs.length≤Usize.max := by simpa [xs] using slots.property
  let rows := alloc.vec.Vec.from xs bound
  have length : rows.length=slots.length := by simp [rows,xs,alloc.vec.Vec.length]
  have get (j : Nat) (hj : j<slots.length) : rows.val[j]! = slots.val[j]!.getD default := by
    simp (disch := simpa using hj) [rows,xs,getElem!_pos]
  refine ⟨rows,?_,length.trans size,?_⟩
  · apply List.ext_getElem (by simpa using length.symm)
    intro j left right
    obtain ⟨v,read,_⟩ := ready j left
    rw [List.getElem_map,←getElem!_pos slots.val j left,←getElem!_pos rows.val j (by simpa [length] using left),get j left,read]
    rfl
  · intro j hj
    obtain ⟨v,read,val⟩ := ready j (length ▸ hj)
    rw [get j (length ▸ hj),read];exact val

theorem reduce_spec [family : Family] {N} (seed : family.Seed N) (a : address.Adrs)
    (root sub height : U32) (node : Nat → Nat → Spec.Bytes)
    (slots : Slice (Option (Array U8 N))) (rows : Rows N)
    (hash : ∀ (h idx : U32) (l r : Array U8 N), 0<h.val →
      bytes l.val=node (h.val-1) (2*idx.val) → bytes r.val=node (h.val-1) (2*idx.val+1) →
      family.hash seed {a with word2:=h,word3:=idx} l r ⦃ out => bytes out.val=node h.val idx.val ⦄)
    (bound : (root.val+1)*2^(height.val-sub.val)≤2^32) (short : height.val-sub.val<32)
    (low : sub.val≤height.val) (inc : sub.val+1<2^32)
    (published : slots.val=rows.val.map some) (ready : Layer node root.val height.val sub.val rows) :
    reduce_tree slots seed a root sub height ⦃ out => bytes out.val=node height.val root.val ⦄ := by
  unfold reduce_tree
  rw [collect_ready slots rows published]
  simp only [bind_ok]
  step as ⟨start,first⟩
  simp only [core.ops.range.RangeInclusive.new,bind_ok]
  step with rounds seed a root height start sub.val node rows hash bound short low first ready as ⟨out,done⟩
  obtain ⟨len,values⟩ := done
  simp at len values
  step as ⟨row,read⟩
  rw [read,←getElem!_pos]
  simpa using values 0 (by omega)

def shakeFamily : Family := ⟨fun N => Array U8 N,shake.xmss.hash2⟩
def sha2Family : Family := ⟨hash.Seed,xmss.hash2⟩

theorem shake_xmss {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (sk : Spec.Bytes) (a : address.Adrs) (tree : (adrsS a).setTypeAndClear Spec.TREE=adrsS a) (root sub height : U32)
    (slots : Slice (Option (Array U8 N))) (rows : Rows N)
    (bound : (root.val+1)*2^(height.val-sub.val)≤2^32) (short : height.val-sub.val<32)
    (low : sub.val≤height.val) (inc : sub.val+1<2^32) (published : slots.val=rows.val.map some)
    (ready : Layer (fun h i => Spec.xmssNode (Shake.params p) sk i h (bytes seed.val) (adrsS a))
      root.val height.val sub.val rows) :
    @reduce_tree shakeFamily N slots seed a root sub height ⦃ out =>
      bytes out.val=Spec.xmssNode (Shake.params p) sk root.val height.val (bytes seed.val) (adrsS a) ⦄ := by
  apply @reduce_spec shakeFamily _ seed a root sub height
    (fun h i => Spec.xmssNode (Shake.params p) sk i h (bytes seed.val) (adrsS a)) slots rows _ bound short low inc published ready
  intro h idx l r positive left right
  apply WP.spec_mono (Shake.hash2_spec p hp seed {a with word2:=h,word3:=idx} l r)
  intro out eq
  have address : adrsS {a with word2:=h,word3:=idx}={adrsS a with word2:=h.val,word3:=idx.val} := rfl
  rw [eq,left,right,address]
  generalize h.val=z at positive ⊢
  cases z with
  | zero => omega
  | succ z =>
    rw [Spec.xmssNode,tree];rfl

theorem shake_fors {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (sk : Spec.Bytes) (a : address.Adrs) (root sub height : U32)
    (slots : Slice (Option (Array U8 N))) (rows : Rows N)
    (bound : (root.val+1)*2^(height.val-sub.val)≤2^32) (short : height.val-sub.val<32)
    (low : sub.val≤height.val) (inc : sub.val+1<2^32) (published : slots.val=rows.val.map some)
    (ready : Layer (fun h i => Spec.forsNode (Shake.params p) sk i h (bytes seed.val) (adrsS a))
      root.val height.val sub.val rows) :
    @reduce_tree shakeFamily N slots seed a root sub height ⦃ out =>
      bytes out.val=Spec.forsNode (Shake.params p) sk root.val height.val (bytes seed.val) (adrsS a) ⦄ := by
  apply @reduce_spec shakeFamily _ seed a root sub height
    (fun h i => Spec.forsNode (Shake.params p) sk i h (bytes seed.val) (adrsS a)) slots rows _ bound short low inc published ready
  intro h idx l r positive left right
  apply WP.spec_mono (Shake.hash2_spec p hp seed {a with word2:=h,word3:=idx} l r)
  intro out eq
  have address : adrsS {a with word2:=h,word3:=idx}={adrsS a with word2:=h.val,word3:=idx.val} := rfl
  rw [eq,left,right,address]
  generalize h.val=z at positive ⊢
  cases z with
  | zero => omega
  | succ z =>
    rw [Spec.forsNode];rfl

theorem sha2_xmss {N : Usize} (p : params.Params) (hp : PN p N) (seed : hash.Seed N) (hs : SeedOk seed)
    (sk : Spec.Bytes) (a : address.Adrs) (tree : (adrsS a).setTypeAndClear Spec.TREE=adrsS a) (root sub height : U32)
    (slots : Slice (Option (Array U8 N))) (rows : Rows N)
    (bound : (root.val+1)*2^(height.val-sub.val)≤2^32) (short : height.val-sub.val<32)
    (low : sub.val≤height.val) (inc : sub.val+1<2^32) (published : slots.val=rows.val.map some)
    (ready : Layer (fun h i => Spec.xmssNode (paramsS p) sk i h (bytes seed.pk_seed.val) (adrsS a))
      root.val height.val sub.val rows) :
    @reduce_tree sha2Family N slots seed a root sub height ⦃ out =>
      bytes out.val=Spec.xmssNode (paramsS p) sk root.val height.val (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  apply @reduce_spec sha2Family _ seed a root sub height
    (fun h i => Spec.xmssNode (paramsS p) sk i h (bytes seed.pk_seed.val) (adrsS a)) slots rows _ bound short low inc published ready
  intro h idx l r positive left right
  apply WP.spec_mono (hash2_spec p hp seed hs {a with word2:=h,word3:=idx} l r)
  intro out eq
  have address : adrsS {a with word2:=h,word3:=idx}={adrsS a with word2:=h.val,word3:=idx.val} := rfl
  rw [eq,left,right,address]
  generalize h.val=z at positive ⊢
  cases z with
  | zero => omega
  | succ z =>
    rw [Spec.xmssNode,tree];rfl

theorem sha2_fors {N : Usize} (p : params.Params) (hp : PN p N) (seed : hash.Seed N) (hs : SeedOk seed)
    (sk : Spec.Bytes) (a : address.Adrs) (root sub height : U32)
    (slots : Slice (Option (Array U8 N))) (rows : Rows N)
    (bound : (root.val+1)*2^(height.val-sub.val)≤2^32) (short : height.val-sub.val<32)
    (low : sub.val≤height.val) (inc : sub.val+1<2^32) (published : slots.val=rows.val.map some)
    (ready : Layer (fun h i => Spec.forsNode (paramsS p) sk i h (bytes seed.pk_seed.val) (adrsS a))
      root.val height.val sub.val rows) :
    @reduce_tree sha2Family N slots seed a root sub height ⦃ out =>
      bytes out.val=Spec.forsNode (paramsS p) sk root.val height.val (bytes seed.pk_seed.val) (adrsS a) ⦄ := by
  apply @reduce_spec sha2Family _ seed a root sub height
    (fun h i => Spec.forsNode (paramsS p) sk i h (bytes seed.pk_seed.val) (adrsS a)) slots rows _ bound short low inc published ready
  intro h idx l r positive left right
  apply WP.spec_mono (hash2_spec p hp seed hs {a with word2:=h,word3:=idx} l r)
  intro out eq
  have address : adrsS {a with word2:=h,word3:=idx}={adrsS a with word2:=h.val,word3:=idx.val} := rfl
  rw [eq,left,right,address]
  generalize h.val=z at positive ⊢
  cases z with
  | zero => omega
  | succ z =>
    rw [Spec.forsNode];rfl

end slhdsa.ParallelReduceNative

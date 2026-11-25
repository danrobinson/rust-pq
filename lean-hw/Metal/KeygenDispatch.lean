import Metal.SigningSchedule

namespace MetalKeygenDispatch
open Spec MetalPipeline MetalCommand MetalChainDispatch MetalLeafDispatch

abbrev Batch := List (Bytes × Bytes × Bytes)
def keys (batch : Batch) : Keys := fun i => (batch[i]!.1,batch[i]!.2.2)
def trees (p : Params) : Trees := fun i => ⟨0,i,p.d-1,none,0⟩
def top (p : Params) : Adrs := {Adrs.zero with layer:=p.d-1}

def unpack (shake : Bool) (n : Nat) (node : Bytes) : Bytes :=
  (List.range n).map fun i => MetalWotsOutput.storeByte shake node i

theorem unpack_spec (shake : Bool) (n : Nat) (node : Bytes) (len : node.length=n) : unpack shake n node=node := by
  apply List.ext_getElem (by simp [unpack,len])
  intro i hi hj
  simp only [unpack,List.getElem_map,List.getElem_range,MetalWotsOutput.storeByte_eq,getElem!_pos node i hj]

def pack (batch : Batch) (shake : Bool) (n words : Nat) (roots : Memory) :=
  (List.range batch.length).map fun i =>
    let item := batch[i]!
    let root := unpack shake n (readNode words roots i)
    (item.1 ++ item.2.1 ++ item.2.2 ++ root,item.2.2 ++ root)

theorem root_value (p : Params) (hv : p.Valid) (mode : XmssMode) (batch : Batch)
    (words size : Nat) (geom : p.n=words*size) (mem : Memory)
    (ok : Matches (batch.length*2^p.hp) words size mem (metalXmssLeaves mode p (keys batch) (trees p)))
    (s : Fin batch.length) :
    MetalXmssDispatch.rootVal p (keys batch) (trees p) words mem s =
      xmssNode p batch[s].1 0 p.hp batch[s].2.2 (top p) := by
  have leaf (i : Nat) (hi : i<2^p.hp) :
      MetalXmssDispatch.leaves p words mem s i = xmssNode p batch[s].1 i 0 batch[s].2.2 (top p) := by
    let gid := s.val*2^p.hp+i
    have hash := metalXmssLeaves_eq_fips mode p hv (keys batch) (trees p) s i hi
    simp only [keys,trees,top,getElem!_pos batch s.val s.isLt,Fin.getElem_fin] at hash ⊢
    have len : (metalXmssLeaves mode p (keys batch) (trees p) gid).length=words*size := by
      rw [hash,xmssNode_length p hv,geom]
    exact (readNode_spec _ _ _ _ _ ok gid (MetalCommandValues.active _ _ _ _ s.isLt hi) len).trans hash
  unfold MetalXmssDispatch.rootVal MetalXmssDispatch.state
  simp only [keys,trees,getElem!_pos batch s.val s.isLt,Fin.getElem_fin]
  exact metal_xmss_reduce_level_eq_fips p batch[s].1 batch[s].2.2 (top p) _ leaf p.hp (by omega) 0 (by simp)

theorem pack_spec (p : Params) (hv : p.Valid) (batch : Batch) (shake : Bool) (words size : Nat)
    (geom : p.n=words*size) (root : Nat → Bytes)
    (linked : ∀ s : Fin batch.length, root s = xmssNode p batch[s].1 0 p.hp batch[s].2.2 (top p))
    (buf : Execution) (order : buf.schedule.Perm (grid batch.length words)) :
    pack batch shake p.n words (run batch.length words size root buf) =
      batch.map (fun (sk,prf,pk) => slhKeygenInternal p sk prf pk) := by
  have written := matches_run batch.length words size root root buf (covers_grid order) (fun _ _ => rfl)
  apply List.ext_getElem (by simp [pack])
  intro i hi hj
  have hb : i<batch.length := by simpa using hj
  have h := linked ⟨i,hb⟩
  simp only [Fin.getElem_fin] at h
  have len : (root i).length = p.n := by rw [h,xmssNode_length p hv]
  simp only [pack,List.getElem_map,List.getElem_range,getElem!_pos batch i hb]
  rw [readNode_spec _ _ _ _ _ written i hb (len.trans geom),unpack_spec _ _ _ len,h]
  rfl

inductive Op | host | tips | leaves | roots | read
  deriving DecidableEq

def op (a : Access) : Option Op :=
  if .keys ∈ a.writes then some .host else
  if .chain_tips ∈ a.writes then some .tips else
  if .xmss_leaves ∈ a.writes then some .leaves else
  if .xmss_roots ∈ a.writes then some .roots else
  if .xmss_roots ∈ a.reads then some .read else none

structure State where
  tips : Memory
  leaves : Memory
  roots : Memory
  result : List (Bytes × Bytes)

def step (tip : Memory) (leaf root : Memory → Memory) (cpu : Memory → List (Bytes × Bytes))
    (s : State) : Op → State
  | .host => s
  | .tips => {s with tips:=tip}
  | .leaves => {s with leaves:=leaf s.tips}
  | .roots => {s with roots:=root s.leaves}
  | .read => {s with result:=cpu s.roots}

def replay (trace : List Access) (tip : Memory) (leaf root : Memory → Memory)
    (cpu : Memory → List (Bytes × Bytes)) (start : State) :=
  ((trace.filterMap op).foldl (step tip leaf root cpu) start).result

end MetalKeygenDispatch

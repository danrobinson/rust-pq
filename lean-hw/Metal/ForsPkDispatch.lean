import Metal.WotsOutput

namespace MetalForsPkDispatch
open Spec MetalPipeline MetalCommand MetalCommandValues MetalChainDispatch MetalLeafDispatch
open MetalWotsOutput (Context context)

structure Job where
  tree : Nat
  leaf : Nat
  key : Nat

def treeAddress (x : Context) : Adrs := ⟨0,x.tree,FORS_TREE,x.leaf,0,0⟩
def treeRoot (p : Params) (x : Context) (i : Nat) := forsNode p x.sk i p.a x.pk (treeAddress x)

theorem pk_spec (p : Params) (hv : p.Valid) (r : BatchSignReq) :
    let x := context p r
    T p x.pk ⟨0,x.tree,FORS_ROOTS,x.leaf,0,0⟩ ((List.range p.k).flatMap (treeRoot p x)) = x.pkFors := by
  dsimp only [context,treeRoot,treeAddress]
  rw [fors_correct p hv]
  rfl

def hash (p : Params) (keys : Keys) (jobs : Nat → Job) (sig : Nat) (input : Bytes) :=
  let j := jobs sig
  T p (keys j.key).2 ⟨0,j.tree,FORS_ROOTS,j.leaf,0,0⟩ input

def payload (k words : Nat) (roots : Memory) (sig : Nat) :=
  (List.range k).flatMap fun i => readNode words roots (sig*k+i)

def flat (k words : Nat) (roots : Memory) (sig : Nat) :=
  (List.range (k*words)).flatMap fun i => roots (sig*k*words+i)

def packed (k words groups width : Nat) (roots : Memory) (sig : Nat) :=
  (List.range k).flatMap fun i => grouped groups width (fun j => roots (sig*k*words+i*words+j))

theorem flat_eq (k words : Nat) (roots : Memory) (sig : Nat) :
    flat k words roots sig = payload k words roots sig := contiguous_words k words (sig*k) roots

theorem packed_eq (k words groups width : Nat) (roots : Memory) (sig : Nat) (geom : groups*width=words) :
    packed k words groups width roots sig = payload k words roots sig := by
  simp only [packed, payload, grouped_flat, geom, readNode, Nat.add_mul]

def Jobs (p : Params) (rs : List BatchSignReq) (keys : Keys) (jobs : Nat → Job) : Prop :=
  ∀ s : Fin rs.length, let j := jobs s
    let x := context p rs[s]
    j.tree = x.tree ∧ j.leaf = x.leaf ∧ (keys j.key).2 = x.pk

def Roots (p : Params) (rs : List BatchSignReq) (words size : Nat) (roots : Memory) : Prop :=
  ∀ s : Fin rs.length, ∀ i < p.k, ∀ w < words,
    roots ((s.val*p.k+i)*words+w) = readWord (treeRoot p (context p rs[s]) i) size w

theorem value_spec (p : Params) (hv : p.Valid) (rs : List BatchSignReq) (keys : Keys)
    (jobs : Nat → Job) (roots : Memory) (words size : Nat) (geom : p.n = words*size)
    (hjob : Jobs p rs keys jobs) (hroot : Roots p rs words size roots) (s : Fin rs.length) :
    hash p keys jobs s (payload p.k words roots s) = (context p rs[s]).pkFors := by
  obtain ⟨ht,hl,hk⟩ := hjob s
  rw [← pk_spec p hv rs[s]]
  simp only [hash,ht,hl,hk,payload]
  apply congrArg (T p _ _)
  apply flatMap_congr'
  intro i hi
  change (List.range words).flatMap _ = _
  calc
    _ = (List.range words).flatMap (readWord (treeRoot p (context p rs[s]) i) size) :=
      flatMap_congr' fun w hw => hroot s i (List.mem_range.mp hi) w (List.mem_range.mp hw)
    _ = _ := by rw [collectWords, ← geom, List.take_of_length_le (by
                  rw [treeRoot, forsNode_length p hv])]

def readPk (count words size : Nat) (value : Nat → Bytes) (output : Execution) (sig : Nat) :=
  readNode words (run count words size value output) sig

theorem readPk_spec (p : Params) (hv : p.Valid) (rs : List BatchSignReq)
    (keys : Keys) (jobs : Nat → Job) (roots : Memory) (words size : Nat) (geom : p.n = words*size)
    (hjob : Jobs p rs keys jobs) (hroot : Roots p rs words size roots)
    (value : Nat → Bytes) (source : ∀ s, value s = hash p keys jobs s (payload p.k words roots s))
    (out : Execution) (order : out.schedule.Perm (grid rs.length words)) (s : Fin rs.length) :
    readPk rs.length words size value out s = (context p rs[s]).pkFors := by
  let target := fun (i : Nat) => (context p rs[i]!).pkFors
  have eq (i) (hi : i < rs.length) : value i = target i := by
    rw [source]
    simpa only [target,getElem!_pos rs i hi,Fin.getElem_fin] using value_spec p hv rs keys jobs roots words size geom hjob hroot ⟨i,hi⟩
  have allWords := matches_run rs.length words size value target out (covers_grid order) eq
  have len : (target s.val).length = words*size := (T_length p hv _ _ _).trans geom
  have h := readNode_spec _ _ _ _ _ allWords _ s.isLt len
  simpa only [target,getElem!_pos rs s.val s.isLt,Fin.getElem_fin,readPk] using h

def region (split : Bool) : Region := if split then .fors_roots else .fors_sub_roots

def scratch (p : Params) (rs : List BatchSignReq) (keys : Keys) (jobs : Nat → Job)
    (words size : Nat) (roots : Memory) (split : Bool) (other : Region → Prop) (r : Region) : Prop :=
  if r = .fors_jobs then Jobs p rs keys jobs else
  if r = region split then Roots p rs words size roots else other r

theorem local_rule (p : Params) (hv : p.Valid) (rs : List BatchSignReq) (split : Bool)
    (cmd : Access) (reads : cmd.reads = [.keys,.fors_jobs,region split]) (writes : cmd.writes=[.pk_fors])
    (actual keys : Keys) (jobs : Nat → Job) (roots : Memory) (words size : Nat) (geom : p.n=words*size)
    (value : Nat → Bytes) (source : ∀ s, value s = hash p actual jobs s (payload p.k words roots s))
    (buffer : Execution) (order : buffer.schedule.Perm (grid rs.length words))
    (g : MetalSignatureLayout.Geometry) (n : Nat) (out expected : Bytes) (s : Region → Prop)
    (hk : s .keys → actual = keys) (hj : s .fors_jobs → Jobs p rs keys jobs)
    (hr : s (region split) → Roots p rs words size roots)
    (dest : (∀ sig : Fin rs.length, readPk rs.length words size value buffer sig = (context p rs[sig]).pkFors) → s .pk_fors) :
    let pred := correct g n out expected s
    (∀ r ∈ cmd.reads, pred r) → ∀ r ∈ cmd.writes, pred r := by
  intro pred inputs r hw
  rw [writes,List.mem_singleton] at hw
  subst r
  have keyEq := hk (inputs .keys (by simp [reads])).1
  have job := hj (inputs .fors_jobs (by simp [reads])).1
  have root := hr (inputs (region split) (by simp [reads])).1
  constructor
  · apply dest
    apply readPk_spec _ hv _ keys jobs roots words size geom job root value _ _ order
    simpa only [keyEq] using source
  · rintro ⟨_, b, _⟩ own
    rcases b with x | ⟨t, z | (l | a)⟩ | ⟨j, c | a⟩ <;> cases own

end MetalForsPkDispatch

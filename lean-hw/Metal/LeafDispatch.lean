import Metal.ChainDispatch

namespace MetalLeafDispatch
open MetalChainDispatch MetalCommand MetalCommandValues MetalPipeline Spec

/-- Canonical byte interpretation of a leaf-producing kernel's hash transcript.
Both source projections instantiate the chain callback (streaming) or read it
from a native-word chain-tip buffer (two-phase). -/
def compressHash (p : Params) (keys : Keys) (trees : Trees) (leafIdx treeIdx : Nat)
    (payload : Bytes) : Bytes :=
  let desc := trees treeIdx
  let address : Adrs := ⟨desc.layer, desc.tree, WOTS_PK, leafIdx, 0, 0⟩
  T p (keys desc.keyIdx).2 address payload

def compress (p : Params) (keys : Keys) (trees : Trees) (leafIdx treeIdx : Nat)
    (chainAt : Nat → Bytes) : Bytes :=
  compressHash p keys trees leafIdx treeIdx ((List.range p.len).flatMap chainAt)

theorem append_flatMap (xs : List α) (f : α → Bytes) (base : Bytes) :
    xs.foldl (fun s x => s ++ f x) base = base ++ xs.flatMap f := by
  induction xs generalizing base with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

def streaming (p : Params) (keys : Keys) (trees : Trees) (leafIdx treeIdx steps : Nat) : Bytes :=
  let desc := trees treeIdx
  let k := keys desc.keyIdx
  compress p keys trees leafIdx treeIdx
    (fun c => chainLoop p k.1 k.2 desc.layer desc.tree leafIdx c steps)

theorem streaming_spec (p : Params) (keys : Keys) (trees : Trees) (gid : Nat) :
    streaming p keys trees (gid % (2^p.hp)) (gid / (2^p.hp)) 15 =
      metalXmssLeavesStreaming p keys trees gid := by
  simp only [streaming, compress, compressHash, chainLoop_spec, metalXmssLeavesStreaming, append_flatMap,
    Adrs.setTypeAndClear, List.nil_append]

/-- Remaining producers need only establish local rules for their own entries.
This lift works for any uniquely bound output and input invariant. -/
theorem insert_rule (trace : List Access) (cmd : Access) (pred : Region → Prop)
    (rule : (∀ r ∈ cmd.reads, pred r) → ∀ r ∈ cmd.writes, pred r)
    (remaining : ∀ a ∈ trace, a ≠ cmd → (∀ r ∈ a.reads, pred r) → ∀ r ∈ a.writes, pred r) :
    Local trace pred := by
  intro a ha
  by_cases eq : a = cmd
  · exact eq ▸ rule
  · exact remaining a ha eq

/-- A completed grid writes the entire checked native-word interpretation of a
buffer, for any value-producing kernel that uses the contiguous MSL store loop. -/
def Matches (total words wordSize : Nat) (mem : Memory) (target : Nat → Bytes) : Prop :=
  ∀ gid < total, ∀ i < words, mem (gid * words + i) = readWord (target gid) wordSize i

def run (n w size : Nat) (value : Nat → Bytes) (e : Execution) : Memory :=
  e.schedule.foldl (store n w size value) e.initial

theorem matches_run (total words size : Nat) (value target : Nat → Bytes) (e : Execution)
    (covered : ∀ g < total, ∀ i < words, (g,i) ∈ e.schedule)
    (same : ∀ g < total, value g = target g) :
    Matches total words size (run total words size value e) target := by
  intro gid hg i hi
  simp only [run, replay_word _ _ _ _ _ _ _ _ hg hi, covered _ hg _ hi, ↓reduceIte, same _ hg]

def scratch (n words size : Nat) (e : Execution) (value target : Nat → Bytes)
    (keys : Keys) (trees : Trees) (other : Region → Prop) : Region → Prop
  | .keys => e.keys = keys
  | .xmss_trees => e.trees = trees
  | .xmss_leaves => Matches n words size (run n words size value e) target
  | r => other r

theorem streaming_rule (cmd : Access) (reads : cmd.reads = [.keys, .xmss_trees])
    (writes : cmd.writes = [.xmss_leaves]) (p : Params) (count words size : Nat)
    (e : Execution) (keys : Keys) (trees : Trees) (other : Region → Prop)
    (value : Nat → Bytes) (projection : ∀ gid, value gid = metalXmssLeavesStreaming p e.keys e.trees gid)
    (order : e.schedule.Perm (grid count words))
    (g : MetalSignatureLayout.Geometry) (batch : Nat) (out expected : Bytes) :
    let pred := correct g batch out expected
      (scratch count words size e value (metalXmssLeavesStreaming p keys trees) keys trees other)
    (∀ r ∈ cmd.reads, pred r) → ∀ r ∈ cmd.writes, pred r := by
  intro pred inputs r hr
  rw [writes, List.mem_singleton] at hr
  subst r
  have hk : e.keys = keys := (inputs .keys (by simp [reads])).1
  have ht : e.trees = trees := (inputs .xmss_trees (by simp [reads])).1
  constructor
  · apply matches_run _ _ _ _ _ _ (covers_grid order)
    intro gid _
    rw [projection, hk, ht]
  · rintro ⟨_, node, _⟩ h
    rcases node with x | ⟨t, s | (l | h')⟩ | ⟨d, c | a⟩ <;> cases h

def readNode (words : Nat) (mem : Memory) (node : Nat) : Bytes :=
  (List.range words).flatMap fun i => mem (node * words + i)

theorem collectWords (data : Bytes) (words size : Nat) :
    (List.range words).flatMap (readWord data size) = data.take (words * size) := by
  induction words with
  | zero => simp
  | succ w ih => simp only [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton,
      Nat.succ_mul, List.take_add, readWord]

theorem readNode_spec (total words size : Nat) (mem : Memory) (target : Nat → Bytes)
    (matchWords : Matches total words size mem target) (gid : Nat) (hg : gid < total)
    (len : (target gid).length = words * size) :
    readNode words mem gid = target gid := by
  unfold readNode
  calc
    _ = (List.range words).flatMap (readWord (target gid) size) :=
      flatMap_congr' fun i hi => matchWords gid hg i (List.mem_range.mp hi)
    _ = _ := by rw [collectWords, ← len, List.take_length]

def twoPhase (p : Params) (keys : Keys) (trees : Trees) (words : Nat) (mem : Memory)
    (gid leafIdx treeIdx : Nat) : Bytes :=
  compress p keys trees leafIdx treeIdx (fun c => readNode words mem (gid * p.len + c))

/-- SHAKE absorbs a single contiguous sequence of lanes. Regrouping the source
loop at the chain boundaries preserves its transcript even for empty ranges. -/
theorem contiguous_words (n words base : Nat) (mem : Memory) :
    (List.range (n * words)).flatMap (fun i => mem (base * words + i)) =
      (List.range n).flatMap (fun c => readNode words mem (base + c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, List.flatMap_append, ih, List.range_succ,
      List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
    simp only [readNode, Nat.add_mul, Nat.add_assoc]

/-- Consecutive native words in each stream call: SHA-256 emits four
push_word calls, SHA-512 groups two 32-bit halves per push_word64, SHAKE
absorbs one 64-bit lane at a time. -/
def grouped (groups width : Nat) (word : Nat → Bytes) : Bytes :=
  (List.range groups).flatMap fun group => (List.range width).flatMap fun i => word (group*width+i)

theorem grouped_flat (groups width : Nat) (word : Nat → Bytes) :
    grouped groups width word = (List.range (groups*width)).flatMap word := by
  simpa only [grouped, readNode, Nat.zero_mul, Nat.zero_add] using
    (contiguous_words groups width 0 word).symm

def nativeStream (p : Params) (keys : Keys) (trees : Trees)
    (leaf tree steps groups width size : Nat) : Bytes :=
  let desc := trees tree
  let key := keys desc.keyIdx
  compress p keys trees leaf tree (fun c =>
    let tip := chainLoop p key.1 key.2 desc.layer desc.tree leaf c steps
    grouped groups width (readWord tip size))

theorem nativeStream_spec (p : Params) (hv : p.Valid) (keys : Keys) (trees : Trees)
    (gid groups width size : Nat) (geometry : p.n = groups * width * size) :
    nativeStream p keys trees (gid % 2^p.hp) (gid / 2^p.hp) 15 groups width size =
      metalXmssLeavesStreaming p keys trees gid := by
  rw [← streaming_spec]
  unfold nativeStream streaming compress
  apply congrArg (compressHash _ _ _ _ _)
  apply flatMap_congr'
  intro c _
  rw [grouped_flat, collectWords, chainLoop_spec]
  unfold metalRunWotsChain
  apply List.take_of_length_le
  rw [chain_length p hv _ (PRF_length p hv _ _ _) _ _ _ _, geometry]

def packedTwoPhase (p : Params) (keys : Keys) (trees : Trees) (words groups width : Nat) (mem : Memory)
    (gid leaf tree : Nat) : Bytes :=
  compress p keys trees leaf tree (fun c =>
    grouped groups width (fun i => mem (gid*p.len*words+c*words+i)))

theorem packedTwoPhase_eq (p : Params) (keys : Keys) (trees : Trees) (words groups width : Nat)
    (mem : Memory) (gid leaf tree : Nat) (geometry : groups*width = words) :
    packedTwoPhase p keys trees words groups width mem gid leaf tree = twoPhase p keys trees words mem gid leaf tree := by
  simp only [packedTwoPhase, grouped_flat, geometry, twoPhase, readNode, Nat.add_mul]

def flatTwoPhase (p : Params) (keys : Keys) (trees : Trees) (words : Nat) (mem : Memory)
    (gid leafIdx treeIdx : Nat) : Bytes :=
  compressHash p keys trees leafIdx treeIdx
    ((List.range (p.len * words)).flatMap (fun i => mem (gid * p.len * words + i)))

theorem flatTwoPhase_eq (p : Params) (keys : Keys) (trees : Trees) (words : Nat) (mem : Memory)
    (gid leafIdx treeIdx : Nat) :
    flatTwoPhase p keys trees words mem gid leafIdx treeIdx = twoPhase p keys trees words mem gid leafIdx treeIdx := by
  simp only [flatTwoPhase, contiguous_words, twoPhase, compress]

theorem twoPhase_spec (p : Params) (hv : p.Valid) (keys : Keys) (trees : Trees)
    (count words size : Nat) (width : p.n = words * size) (mem : Memory)
    (tips : Matches (count * p.len) words size mem (metalWotsChainsKernel p keys trees))
    (gid : Nat) (hg : gid < count) :
    twoPhase p keys trees words mem gid (gid % 2^p.hp) (gid / 2^p.hp) =
      metalWotsTwoPhaseLeaf p keys trees gid := by
  simp only [twoPhase, compress, compressHash, metalWotsTwoPhaseLeaf, metalWotsTlenKernel, append_flatMap,
    Adrs.setTypeAndClear, List.nil_append]
  apply congrArg (T p _ _)
  apply flatMap_congr'
  intro c hc
  apply readNode_spec _ _ _ _ _ tips _ (active gid c p.len count hg (List.mem_range.mp hc))
  unfold metalWotsChainsKernel metalRunWotsChain
  exact (chain_length p hv _ (PRF_length p hv _ _ _) _ _ _ _).trans width

def leafScratch (count words size : Nat) (leaf : Execution) (value target : Nat → Bytes)
    (other : Region → Prop) : Region → Prop
  | .xmss_leaves => Matches count words size (run count words size value leaf) target
  | r => other r

theorem twoPhase_rule (cmd : Access) (reads : cmd.reads = [.keys,.xmss_trees,.chain_tips])
    (writes : cmd.writes = [.xmss_leaves]) (p : Params) (hv : p.Valid) (count words size : Nat)
    (width : p.n = words * size) (e leaf : Execution) (tip value : Nat → Bytes)
    (keys : Keys) (trees : Trees) (other : Region → Prop)
    (projection : ∀ gid, value gid = twoPhase p e.keys e.trees words
      (run (count * p.len) words size tip e) gid (gid % 2^p.hp) (gid / 2^p.hp))
    (order : leaf.schedule.Perm (grid count words))
    (g : MetalSignatureLayout.Geometry) (batch : Nat) (out expected : Bytes) :
    let s := leafScratch count words size leaf value (metalWotsTwoPhaseLeaf p keys trees) other
    let pred := correct g batch out expected
      (invariant p (count * p.len) words size e tip keys trees s)
    (∀ r ∈ cmd.reads, pred r) → ∀ r ∈ cmd.writes, pred r := by
  intro s pred inputs r hr
  rw [writes,List.mem_singleton] at hr
  subst r
  have hk : e.keys = keys := (inputs .keys (by simp [reads])).1
  have ht : e.trees = trees := (inputs .xmss_trees (by simp [reads])).1
  have tips : Matches (count*p.len) words size (run (count*p.len) words size tip e)
      (metalWotsChainsKernel p keys trees) := (inputs .chain_tips (by simp [reads])).1
  constructor
  · apply matches_run _ _ _ _ _ _ (covers_grid order)
    intro gid hg
    rw [projection, hk, ht]
    exact twoPhase_spec p hv keys trees count words size width _ tips gid hg
  · rintro ⟨_, node, _⟩ h
    rcases node with x | ⟨t, s | (l | h')⟩ | ⟨d, c | a⟩ <;> cases h

end MetalLeafDispatch

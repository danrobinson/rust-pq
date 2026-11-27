import Metal.CommandValues

/-! Word stores of the two production WOTS chain-tip kernels. A schedule interleaves
the individual stores of any active threads. Each word has a single owning thread
and loop iteration, even in an oversized dispatch. -/

namespace MetalChainDispatch
open MetalCommand MetalCommandValues MetalPipeline Spec

abbrev Keys := Nat → Bytes × Bytes
abbrev Trees := Nat → XmssTreeDesc
abbrev Memory := Nat → Bytes
abbrev Lane := Nat × Nat

/-- Projection of run_wots_chain's initial short hash, zero-step exit and
in-place short-hash loop. The two address encodings are checked separately at
their compression/permutation boundary by the shader value replay. -/
def chainLoop (p : Params) (sk pk : Bytes) (layer tree pair c steps : Nat) : Bytes :=
  let secret := PRF p pk sk ⟨layer, tree, WOTS_PRF, pair, c, 0⟩
  if steps = 0 then secret else
    (List.range steps).foldl (fun v s => F p pk ⟨layer, tree, WOTS_HASH, pair, c, s⟩ v) secret

theorem chainLoop_spec (p : Params) (sk pk : Bytes) (layer tree pair c steps : Nat) :
    chainLoop p sk pk layer tree pair c steps = metalRunWotsChain p sk pk layer tree pair c steps := by
  cases steps <;> simp [chainLoop, metalRunWotsChain, chain, wotsSkAdrs, Adrs.setTypeAndClear]

/-- The host's checked buffer extent bounds each unsigned word address in MSL. -/
theorem word_address_fits (total words gid i : Nat) (extent : total * words ≤ 2^32)
    (thread : gid < total) (word : i < words) : gid * words + i < 2^32 :=
  lt_of_lt_of_le (active gid i words total thread word) extent

def readWord (bytes : Bytes) (wordSize i : Nat) := (bytes.drop (i * wordSize)).take wordSize

/-- Translation of the guarded store in either family, with family-specific seed
loading and native word encoding represented by the primitive and byte projection. -/
def store (total words wordSize : Nat) (tip : Nat → Bytes)
    (mem : Memory) (lane : Lane) : Memory := fun addr =>
  if lane.1 < total ∧ lane.2 < words ∧ addr = lane.1 * words + lane.2 then
    readWord (tip lane.1) wordSize lane.2
  else mem addr

theorem replay_word (total words wordSize : Nat) (tip : Nat → Bytes)
    (schedule : List Lane) (mem : Memory) (gid i : Nat)
    (active : gid < total) (inside : i < words) :
    (schedule.foldl (store total words wordSize tip) mem) (gid * words + i) =
      if (gid, i) ∈ schedule then readWord (tip gid) wordSize i else mem (gid * words + i) := by
  induction schedule generalizing mem with
  | nil => simp
  | cons lane rest ih =>
    rw [List.foldl_cons, ih]
    by_cases later : (gid,i) ∈ rest
    · simp [later]
    rcases lane with ⟨g,j⟩
    by_cases same : (gid,i) = (g,j)
    · cases same
      simp [later, store, active, inside]
    · have different : ¬ (g < total ∧ j < words ∧ gid * words + i = g * words + j) := by
        rintro ⟨_, hj, eq⟩
        have di := decode gid i words inside
        have dj := decode g j words hj
        rw [eq] at di
        exact same (Prod.ext (di.1.symm.trans dj.1) (di.2.symm.trans dj.2))
      simp [later, same, store, different]

def grid (count words : Nat) : List Lane :=
  (List.range count).flatMap fun gid => (List.range words).map fun i => (gid,i)

theorem covers_grid {count words : Nat} {schedule : List Lane}
    (order : schedule.Perm (grid count words)) :
    ∀ g < count, ∀ i < words, (g,i) ∈ schedule := by
  intro g hg i hi
  apply order.mem_iff.mpr
  apply List.mem_flatMap.mpr
  exact ⟨g, List.mem_range.mpr hg, List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩⟩

structure Execution where
  keys : Keys
  trees : Trees
  initial : Memory
  schedule : List Lane

/-- A command value predicate tying the actual input records to their intended
records and the final abstract chain-tip buffer to its specified native words. -/
def invariant (p : Params) (count words wordSize : Nat) (e : Execution)
    (tip : Nat → Bytes) (keys : Keys) (trees : Trees) (other : Region → Prop) : Region → Prop
  | .keys => e.keys = keys
  | .xmss_trees => e.trees = trees
  | .chain_tips => ∀ gid < count, ∀ i < words,
      (e.schedule.foldl (store count words wordSize tip) e.initial) (gid * words + i) =
        readWord (metalWotsChainsKernel p keys trees gid) wordSize i
  | r => other r

/-- All other producers may have their own rules. For this producer Lean derives
the local rule from the executable store schedule, projection and input records. -/
theorem local_of_dispatch (trace : List Access) (chainCmd : Access)
    (reads : chainCmd.reads = [.keys, .xmss_trees]) (writes : chainCmd.writes = [.chain_tips])
    (p : Params) (count words wordSize : Nat) (e : Execution)
    (keys : Keys) (trees : Trees) (other : Region → Prop)
    (tip : Nat → Bytes) (projection : ∀ gid < count, tip gid = metalWotsChainsKernel p e.keys e.trees gid)
    (covered : ∀ g < count, ∀ i < words, (g,i) ∈ e.schedule)
    (g : MetalSignatureLayout.Geometry) (batch : Nat) (out expected : Bytes)
    (remaining : ∀ a ∈ trace, a ≠ chainCmd →
      (∀ r ∈ a.reads, correct g batch out expected (invariant p count words wordSize e tip keys trees other) r) →
      ∀ r ∈ a.writes, correct g batch out expected (invariant p count words wordSize e tip keys trees other) r) :
    Local trace (correct g batch out expected (invariant p count words wordSize e tip keys trees other)) := by
  intro a ha inputs r hr
  by_cases eq : a = chainCmd
  · subst a
    rw [writes, List.mem_singleton] at hr
    subst r
    have hk : e.keys = keys := (inputs .keys (by simp [reads])).1
    have ht : e.trees = trees := (inputs .xmss_trees (by simp [reads])).1
    constructor
    · intro gid hg i hi
      simp only [replay_word _ _ _ _ _ _ _ _ hg hi, covered _ hg _ hi, ↓reduceIte, projection gid hg, hk, ht]
    · rintro ⟨_, node, _⟩ h
      rcases node with x | ⟨t, s | (l | h')⟩ | ⟨d, c | a⟩ <;> cases h
  · exact remaining a ha eq inputs r hr

end MetalChainDispatch

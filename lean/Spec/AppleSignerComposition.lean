import Spec.AppleShakeDigest
import Slhdsa.Proofs.Ht

/-! Pointwise composition of the successful SHAKE signer call equations. The
    observations below contain intermediate values; they are not an AArch64 execution
    relation. The external native checkers establish the individual equations under
    their own ISA, solver, memory-layout and runtime assumptions. -/
namespace LinkedArm.Signer
open Spec

abbrev Scratch := Keccak.Lane → ArmSha3Binary.Registers
abbrev LayerState := Bytes × Bytes × Nat × Nat

/-- A particular execution of an XMSS node. The child results on this call are
    sufficient; no property of WOTS at unrelated addresses is required. -/
inductive Node (p : Params) (sk pk : Bytes) (a : Adrs) : Nat → Nat → Bytes → Prop where
  | leaf (i : Nat) : Node p sk pk a i 0
      (wotsPkGen p sk pk { a.setTypeAndClear WOTS_HASH with keypair := i })
  | parent (i h : Nat) (l r : Bytes)
      (left : Node p sk pk a (2*i) h l) (right : Node p sk pk a (2*i+1) h r) :
      Node p sk pk a i (h+1)
        (H p pk { a.setTypeAndClear TREE with word2 := h+1, word3 := i } (l++r))

theorem Node.eq_spec {p sk pk a i h out} (v : Node p sk pk a i h out) :
    out = xmssNode p sk i h pk a := by
  induction v with
  | leaf => rfl
  | parent i h l r _ _ il ir => simp only [xmssNode, il, ir]

structure LayerSignature (p : Params) (msg sk pk : Bytes) (i : Nat) (a : Adrs)
    (out : Bytes) where
  wots : Bytes
  auth : Nat → Bytes
  wots_eq : wots = wotsSign p msg sk pk { a.setTypeAndClear WOTS_HASH with keypair := i }
  auth_eq : ∀ j < p.hp, Node p sk pk a ((i / 2^j) ^^^ 1) j (auth j)
  layout : out = wots ++ (List.range p.hp).flatMap auth

theorem LayerSignature.eq_spec {p msg sk pk i a out}
    (v : LayerSignature p msg sk pk i a out) : out = xmssSign p msg sk i pk a := by
  rw [v.layout, v.wots_eq, xmssSign]
  congr 1
  apply List.flatMap_congr
  intro j hj
  exact (v.auth_eq j (List.mem_range.mp hj)).eq_spec

def parent (p : Params) (pk auth : Bytes) (i : Nat) (a : Adrs)
    (st : Bytes × Nat) (j : Nat) : Bytes × Nat :=
  let sibling := block p auth j
  if (i / 2^j) % 2 = 0 then
    (H p pk { a with word2 := j+1, word3 := st.2/2 } (st.1 ++ sibling), st.2/2)
  else
    (H p pk { a with word2 := j+1, word3 := (st.2-1)/2 } (sibling ++ st.1), (st.2-1)/2)

/-- The states reached on this authentication path. The pair carries the node
    bytes and global node index. Each hash uses the corresponding signature block. -/
structure Path (p : Params) (i : Nat) (a : Adrs) (pk auth leaf out : Bytes) where
  state : Nat → Bytes × Nat
  initial : state 0 = (leaf,i)
  step : ∀ j < p.hp, state (j+1) = parent p pk auth i a (state j) j
  last : out = (state p.hp).1

theorem Path.eq_spec {p i a pk auth leaf out} (v : Path p i a pk auth leaf out) :
    out = climb p leaf i i auth p.hp pk a := by
  have eq (k : Nat) (h : k ≤ p.hp) :
      v.state k = (List.range k).foldl (parent p pk auth i a) (leaf,i) := by
    induction k with
    | zero => exact v.initial
    | succ k ih => rw [v.step _ (by omega), ih (by omega), List.range_succ]; simp
  rw [v.last,eq p.hp (by omega)]
  rfl

structure LayerRoot (p : Params) (msg pk sig : Bytes) (i : Nat) (a : Adrs) (out : Bytes) where
  leaf : Bytes
  wots_eq : leaf = wotsPkFromSig p (sig.take (p.len*p.n)) msg pk
    { a.setTypeAndClear WOTS_HASH with keypair := i }
  path : Path p i (a.setTypeAndClear TREE) pk ((sig.drop (p.len*p.n)).take (p.hp*p.n)) leaf out

theorem LayerRoot.eq_spec {p msg pk sig i a out} (v : LayerRoot p msg pk sig i a out) :
    out = xmssPkFromSig p i sig msg pk a := by
  rw [v.path.eq_spec, v.wots_eq]; rfl

/-- The output of each actually invoked XMSS operation, in layer order. -/
structure Layers where
  signature : Nat → Bytes
  root : Nat → Bytes

def advance (p : Params) (v : Layers) (st : LayerState) (j : Nat) : LayerState :=
  (st.1 ++ v.signature j, if j+1 < p.d then v.root j else st.2.1,
   st.2.2.1 >>> p.hp, st.2.2.1 % 2^p.hp)

def afterLayers (p : Params) (v : Layers) (initial : LayerState) (j : Nat) : LayerState :=
  (List.range j).foldl (advance p v) initial

def address (j : Nat) (st : LayerState) : Adrs :=
  { Adrs.zero with layer := j, tree := st.2.2.1 }

/-- Each premise refers only to the inputs at this iteration of this trace. -/
structure LayerCalls (p : Params) (sk pk : Bytes) (initial : LayerState) (v : Layers) where
  sign : ∀ j, j < p.d →
    let st := afterLayers p v initial j
    LayerSignature p st.2.1 sk pk st.2.2.2 (address j st) (v.signature j)
  recover : ∀ j, j+1 < p.d →
    let st := afterLayers p v initial j
    LayerRoot p st.2.1 pk (v.signature j) st.2.2.2 (address j st) (v.root j)

private theorem step_eq {p sk pk initial v} (calls : LayerCalls p sk pk initial v)
    (j : Nat) (hj : j < p.d) :
    let st := afterLayers p v initial j
    advance p v st j = slhdsa.signNext p.d (slhdsa.htSignStep p sk pk) st j := by
  dsimp only
  have sig := (calls.sign j hj).eq_spec
  by_cases recover : j+1 < p.d
  · have root := (calls.recover j recover).eq_spec
    simp only [advance, recover, ite_true, slhdsa.signNext, slhdsa.htSignStep, root, sig, address]
  · simp only [advance, recover, ite_false, slhdsa.signNext, slhdsa.htSignStep, sig, address]

theorem layers_eq {p sk pk msg tree leaf v}
    (h : LayerCalls p sk pk ([],msg,tree,leaf) v) :
    (afterLayers p v ([],msg,tree,leaf) p.d).1 = htSign p msg sk pk tree leaf := by
  let init : LayerState := ([],msg,tree,leaf)
  have prefix_eq (k : Nat) (hk : k ≤ p.d) :
      afterLayers p v init k = (List.range k).foldl
        (slhdsa.signNext p.d (slhdsa.htSignStep p sk pk)) init := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [afterLayers, List.range_succ, List.foldl_append, List.foldl_append]
      change advance p v (afterLayers p v init k) k =
        slhdsa.signNext p.d (slhdsa.htSignStep p sk pk) _ k
      rw [step_eq h k (by omega), ih (by omega)]
  rw [slhdsa.htSign_eq, ←slhdsa.signNext_signature]
  exact congrArg Prod.fst (prefix_eq p.d (by omega))

/-- The FORS routines receive the decoded digits rather than the encoded digest.
    These are their per-tree signature-layout and recovery equations. -/
def forsRows (p : Params) (ds : List Nat) (sk pk : Bytes) (a : Adrs) : Bytes :=
  (List.range p.k).flatMap fun i =>
    forsSkGen p sk pk a (i*2^p.a + ds[i]!) ++
      (List.range p.a).flatMap fun j =>
        forsNode p sk (i*2^(p.a-j) + ((ds[i]! / 2^j) ^^^ 1)) j pk a

def forsRoots (p : Params) (ds : List Nat) (sig pk : Bytes) (a : Adrs) : Bytes :=
  let roots := (List.range p.k).flatMap fun i =>
    let n := i*2^p.a + ds[i]!
    let node := F p pk { a with word2 := 0, word3 := n } (block p sig (i*(p.a+1)))
    let path := (sig.drop ((i*(p.a+1)+1)*p.n)).take (p.a*p.n)
    climb p node ds[i]! n path p.a pk a
  T p pk { a.setTypeAndClear FORS_ROOTS with keypair := a.keypair } roots

def sponge (scratch : Scratch) (data : Bytes) (n : Nat) :=
  Digest.finish scratch (data.foldl Keccak.feed Keccak.initial) n

private theorem sponge_eq (scratch : Scratch) (data : Bytes) (n : Nat) (h : n ≤ 136) :
    sponge scratch data n = shake256 data n := Digest.finish_eq _ _ _ h

def forsAddress (p : Params) (digest : Bytes) : Adrs :=
  { { Adrs.zero with tree := digestTree p digest }.setTypeAndClear FORS_TREE
      with keypair := digestLeaf p digest }

structure Signature (p : Params) (msg sk random out : Bytes) where
  scratch : Scratch
  r : Bytes
  digest : Bytes
  sigFors : Bytes
  pkFors : Bytes
  digits : List Nat
  layers : Layers
  randomness : r = sponge scratch (block p sk 1 ++ random ++ msg) p.n
  digest_eq : digest = sponge scratch (r ++ block p sk 2 ++ block p sk 3 ++ msg) p.m
  decode : digits = base2b (digest.take p.mdBytes) p.a p.k
  forest_sig : sigFors = forsRows p digits (block p sk 0) (block p sk 2) (forsAddress p digest)
  forest_pk : pkFors = forsRoots p digits sigFors (block p sk 2) (forsAddress p digest)
  layer_calls : LayerCalls p (block p sk 0) (block p sk 2)
    ([],pkFors,digestTree p digest,digestLeaf p digest) layers
  layout : out = r ++ sigFors ++
    (afterLayers p layers ([],pkFors,digestTree p digest,digestLeaf p digest) p.d).1

theorem internal_eq {p msg sk random out} (v : Signature p msg sk random out)
    (family : p.family = .shake) (hn : p.n ≤ 136) (hm : p.m ≤ 136) :
    out = slhSignInternal p msg sk random := by
  have r : v.r = PRFmsg p (block p sk 1) random msg := by
    simpa only [PRFmsg, family] using v.randomness.trans (sponge_eq _ _ _ hn)
  have dg : v.digest = Hmsg p v.r (block p sk 2) (block p sk 3) msg := by
    simpa only [Hmsg, family] using v.digest_eq.trans (sponge_eq _ _ _ hm)
  have fs : v.sigFors = forsSign p (v.digest.take p.mdBytes) (block p sk 0) (block p sk 2)
      (forsAddress p v.digest) := by rw [v.forest_sig, v.decode]; rfl
  have fr : v.pkFors = forsPkFromSig p v.sigFors (v.digest.take p.mdBytes) (block p sk 2)
      (forsAddress p v.digest) := by rw [v.forest_pk, v.decode]; rfl
  rw [v.layout, layers_eq v.layer_calls, fr, fs, dg, r]
  rfl

theorem pure_eq {p msg ctx sk random out} (valid : ctx.length ≤ 255)
    (v : Signature p (withContext msg ctx) sk random out) (family : p.family = .shake)
    (hn : p.n ≤ 136) (hm : p.m ≤ 136) : some out = slhSign p msg ctx sk random := by
  simp [slhSign, show ¬ctx.length > 255 by omega, internal_eq v family hn hm]

/-- The deterministic wrapper supplies PK.seed, i.e. the third n-byte key block. -/
theorem deterministic_eq {p msg ctx sk out} (valid : ctx.length ≤ 255)
    (v : Signature p (withContext msg ctx) sk (block p sk 2) out)
    (family : p.family = .shake) (hn : p.n ≤ 136) (hm : p.m ≤ 136) :
    some out = slhSign p msg ctx sk (block p sk 2) :=
  pure_eq valid v family hn hm

def parameterSets : List Params :=
  [shake_128s, shake_128f, shake_192s, shake_192f, shake_256s, shake_256f]

private theorem supported {p} (h : p ∈ parameterSets) :
    p.family = .shake ∧ p.n ≤ 136 ∧ p.m ≤ 136 := by
  simp only [parameterSets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem supported_internal_eq {p msg sk random out} (h : p ∈ parameterSets)
    (v : Signature p msg sk random out) : out = slhSignInternal p msg sk random :=
  internal_eq v (supported h).1 (supported h).2.1 (supported h).2.2

theorem supported_pure_eq {p msg ctx sk random out} (h : p ∈ parameterSets)
    (valid : ctx.length ≤ 255) (v : Signature p (withContext msg ctx) sk random out) :
    some out = slhSign p msg ctx sk random :=
  pure_eq valid v (supported h).1 (supported h).2.1 (supported h).2.2

/-- Successful context-wrapper ABI projection. The native checker supplies the two
    prefix bytes, exact context and message slices, and optional randomness source. -/
theorem supported_wrapper_eq {p msg ctx sk supplied random frame out} (h : p ∈ parameterSets)
    (deterministic : Bool) (valid : ctx.length ≤ 255)
    (framed : frame = [0, BitVec.ofNat 8 ctx.length] ++ ctx ++ msg)
    (selected : random = if deterministic then block p sk 2 else supplied)
    (v : Signature p frame sk random out) :
    some out = slhSign p msg ctx sk (if deterministic then block p sk 2 else supplied) := by
  have form : frame = withContext msg ctx := framed
  subst frame
  subst random
  exact supported_pure_eq h valid v

theorem referenceNode (p sk pk a i h) : Node p sk pk a i h (xmssNode p sk i h pk a) := by
  induction h generalizing i with
  | zero => exact Node.leaf i
  | succ h ih => exact Node.parent i h _ _ (ih (2*i)) (ih (2*i+1))

private def referenceLayerSig (p msg sk pk i a) :
    LayerSignature p msg sk pk i a (xmssSign p msg sk i pk a) where
  wots := _
  auth := fun j => xmssNode p sk ((i / 2^j) ^^^ 1) j pk a
  wots_eq := rfl
  auth_eq _j _ := referenceNode _ _ _ _ _ _
  layout := rfl

private def referencePath (p i a pk auth leaf) :
    Path p i a pk auth leaf (climb p leaf i i auth p.hp pk a) where
  state := fun j => (List.range j).foldl (parent p pk auth i a) (leaf,i)
  initial := rfl
  step j _ := by simp [List.range_succ]
  last := rfl

def referenceLayerRoot (p msg pk sig i a) :
    LayerRoot p msg pk sig i a (xmssPkFromSig p i sig msg pk a) where
  leaf := _
  wots_eq := rfl
  path := referencePath _ _ _ _ _ _

private def referenceState (p : Params) (sk pk : Bytes) (init : LayerState) (j : Nat) :=
  (List.range j).foldl (slhdsa.signNext p.d (slhdsa.htSignStep p sk pk)) init

def referenceLayers (p : Params) (sk pk : Bytes) (init : LayerState) : Layers where
  signature j :=
    let st := referenceState p sk pk init j
    xmssSign p st.2.1 sk st.2.2.2 pk (address j st)
  root j :=
    let st := referenceState p sk pk init j
    let sig := xmssSign p st.2.1 sk st.2.2.2 pk (address j st)
    xmssPkFromSig p st.2.2.2 sig st.2.1 pk (address j st)

private theorem referenceLayers_state (p sk pk init j) :
    afterLayers p (referenceLayers p sk pk init) init j = referenceState p sk pk init j := by
  induction j with
  | zero => simp only [afterLayers, referenceState, List.range_zero, List.foldl_nil]
  | succ j ih =>
    rw [afterLayers, referenceState, List.range_succ, List.foldl_append, List.foldl_append]
    change advance p _ (afterLayers p _ init j) j = _
    rw [ih]
    rfl

def referenceCalls (p sk pk init) : LayerCalls p sk pk init (referenceLayers p sk pk init) where
  sign j _ := by
    dsimp only
    rw [referenceLayers_state]
    exact referenceLayerSig _ _ _ _ _ _
  recover j _ := by
    dsimp only
    rw [referenceLayers_state]
    exact referenceLayerRoot _ _ _ _ _ _

/-- The mathematical call equations have a witness at exactly the FIPS output.
    This existence construction runs the reference operations, independently of any
    claim that the execution of the native executable yields such a witness. -/
theorem trace_iff {p msg sk random out} (h : p ∈ parameterSets) :
    Nonempty (Signature p msg sk random out) ↔ out = slhSignInternal p msg sk random := by
  constructor
  · rintro ⟨v⟩; exact supported_internal_eq h v
  · rintro rfl
    let skSeed := block p sk 0
    let pkSeed := block p sk 2
    let r := PRFmsg p (block p sk 1) random msg
    let dg := Hmsg p r pkSeed (block p sk 3) msg
    let md := dg.take p.mdBytes
    let ad := forsAddress p dg
    let f := forsSign p md skSeed pkSeed ad
    let root := forsPkFromSig p f md pkSeed ad
    let init : LayerState := ([],root,digestTree p dg,digestLeaf p dg)
    let calls := referenceCalls p skSeed pkSeed init
    refine ⟨{ scratch := fun _ => fun _ => 0, r := r, digest := dg, sigFors := f,
              pkFors := root, digits := base2b md p.a p.k,
              layers := referenceLayers p skSeed pkSeed init,
              randomness := ?_, digest_eq := ?_, decode := rfl, forest_sig := rfl,
              forest_pk := rfl, layer_calls := calls, layout := ?_ }⟩
    · simp [r, PRFmsg, (supported h).1, sponge_eq _ _ _ (supported h).2.1]
    · simp [dg, Hmsg, (supported h).1, sponge_eq _ _ _ (supported h).2.2, pkSeed]
    · rw [layers_eq calls]; rfl

#print axioms trace_iff
#print axioms supported_internal_eq
#print axioms supported_pure_eq
#print axioms supported_wrapper_eq
#print axioms deterministic_eq
end LinkedArm.Signer

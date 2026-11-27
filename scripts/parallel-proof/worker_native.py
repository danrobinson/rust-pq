"""Instantiate the generated signer with the native kernels used in the checked public path."""

import re

from worker_control import completion_witness, control_witness, runtime_witness
from worker_copy import copy_witness
from worker_effects import effects_witness

# External functions reside one namespace above the generated Rust definitions.
# A separate namespace lets Lean import those definitions together with the
# canonical addresses, parameter types, and target-specific native kernels.
BINDINGS = {
    "core.array.Array.map": "_root_.ParallelWorkerIterators.arrayMap opsfunctionFnMutFTupleTUInst",
    "core.iter.traits.iterator.Iterator.map.default": "_root_.ParallelWorkerIterators.mapped",
    "core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next": "_root_.ParallelWorkerIterators.next traitsiteratorIteratorInst opsfunctionFnMutFTupleClause0_ItemBInst",
    "SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter": "_root_.ParallelWorkerIterators.borrowed",
    "shake.batch.available": "_root_.slhdsa.RawFors.probe _root_.slhdsa.WorkerCrypto.rootHost N",
    "util.base_2b": "_root_.slhdsa.util.base_2b",
    "shake.xmss.xmss_node": "fun sk i z pk addr => _root_.slhdsa.WorkerCrypto.xmss sk i z pk (nativeAddress addr)",
    "shake.fors.fors_node": "fun sk i z pk addr => _root_.slhdsa.WorkerCrypto.node sk i z pk (nativeAddress addr)",
    "shake.fors.fors_sk_gen": "fun sk pk addr i => _root_.slhdsa.WorkerCrypto.secret sk pk (nativeAddress addr) i",
    "shake.xmss.hash2": "fun pk addr l r => _root_.slhdsa.WorkerCrypto.hash pk (nativeAddress addr) l r",
    "shake.wots.wots_sign": "fun m sk pk addr => _root_.slhdsa.WorkerCrypto.wots m sk pk (nativeAddress addr)",
    "shake.fors.fors_pk_from_sig": "fun p sig md pk addr => _root_.slhdsa.WorkerCrypto.recover (nativeParams p) sig md pk (nativeAddress addr)",
}

CONVERSIONS = """
def nativeAddress (a : slhdsa.address.Adrs) : _root_.slhdsa.address.Adrs :=
  ⟨a.layer, a.tree, a.typ, a.keypair, a.word2, a.word3⟩

def stagedAddress (a : _root_.slhdsa.address.Adrs) : slhdsa.address.Adrs :=
  ⟨a.layer, a.tree, a.typ, a.keypair, a.word2, a.word3⟩

theorem address_roundtrip (a : slhdsa.address.Adrs) : stagedAddress (nativeAddress a) = a := rfl
theorem native_address_roundtrip (a : _root_.slhdsa.address.Adrs) : nativeAddress (stagedAddress a) = a := rfl

def nativeParams (p : slhdsa.params.Params) : _root_.slhdsa.params.Params :=
  ⟨p.n,p.h,p.d,p.hp,p.a,p.k,p.m⟩

def stagedParams (p : _root_.slhdsa.params.Params) : slhdsa.params.Params :=
  ⟨p.n,p.h,p.d,p.hp,p.a,p.k,p.m⟩

theorem params_roundtrip (p : slhdsa.params.Params) : stagedParams (nativeParams p) = p := rfl
theorem native_params_roundtrip (p : _root_.slhdsa.params.Params) : nativeParams (stagedParams p) = p := rfl
"""


# Each target gets the same machine and feature selection as its existing
# native ticket proof. The Linux width-three inner loop never takes the
# eight-lane horizontal fallback; its supplied kernel remains fully defined.
TARGET = {
    "aarch64-apple-darwin": (
        ".apple specialization.sha3",
        "(_root_.slhdsa.AppleHybrid.machine specialization.sha3)",
        "(_root_.slhdsa.ParallelLowFors.appleHost specialization.sha3)",
        "(_root_.slhdsa.ParallelLowFors.appleWide specialization.sha3 specialization.p)",
    ),
    "x86_64-unknown-linux-gnu": (
        ".x86",
        "_root_.slhdsa.Kxdispatch.machine",
        "_root_.slhdsa.ParallelLowFors.x86Host",
        "(_root_.slhdsa.ParallelLowFors.x86Wide specialization.p)",
    ),
    "aarch64-unknown-linux-gnu": (
        ".linuxArm",
        "_root_.slhdsa.Kldisp.machine",
        "_root_.slhdsa.ParallelLowFors.linuxHost",
        "⟨fun sk seed addr i z => _root_.slhdsa.WorkerCrypto.node sk i z seed addr⟩",
    ),
}


def ticket_witness(generated):
    # Reuse the source-produced computation verbatim. Factoring the expression
    # into its own definition is also checked against the complete loop body.
    found = re.search(
        r"def shake\.slh\.parallel\.phase_two_loop\.body\n(.*?)\n  := do\n(.*?)(?=\n\n)",
        generated,
        re.DOTALL,
    )
    if not found:
        raise ValueError("missing WOTS loop body")
    args, body = found.groups()
    start = body.index("    let (addr, index) ←")
    stop = body.index("    let r ← std.sync.once_lock.OnceLock.set slot sig")
    fragment = body[start:stop]
    # 'some slot' includes the computation from the two published tables.
    row = "\n".join(line[2:] for line in fragment.splitlines())
    return (
        """
namespace slhdsa
open Aeneas Aeneas.Std Result
def nativeLayers (layers : alloc.vec.Vec (address.Adrs × Std.U32)) :
    _root_.slhdsa.ParallelXmssTicket.Layers :=
  alloc.vec.Vec.from (layers.val.map (fun (a,k) => (nativeAddress a,k))) (by simp)
def extractedWotsRow {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (j : Std.Usize) : Result (alloc.vec.Vec Std.U8) := do
"""
        + row
        + "\n  ok sig\n"
        + (
            "def factoredWotsBody\n"
            + args
            + "\n  := do\n"
            + body[:start]
            + "    let sig ← extractedWotsRow sk seed layers roots j\n"
            + body[stop:]
        )
        + """
theorem generated_wots_factor {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (next slots) (roots : alloc.vec.Vec (Array Std.U8 N)) :
    shake.slh.parallel.phase_two_loop.body sk seed layers next slots roots =
      factoredWotsBody sk seed layers next slots roots := by
  unfold shake.slh.parallel.phase_two_loop.body factoredWotsBody
  congr 1
  funext j
  dsimp only
  congr 1
  funext dest
  cases dest with
  | none => rfl
  | some slot =>
    simp only [extractedWotsRow,Aeneas.Std.bind_assoc]
    congr 1
    funext pair
    cases pair
    simp [Aeneas.Std.bind_assoc,Aeneas.Std.bind_pure]

theorem generated_wots_native {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (j : Std.Usize) (valid : j.val<layers.length) :
    extractedWotsRow sk seed layers roots j =
      _root_.slhdsa.WorkerPayload.nativeTicket _root_.slhdsa.WorkerCrypto.Config.host
        _root_.slhdsa.WorkerCrypto.Config.p (nativeLayers layers) roots j sk seed := by
  rw [← _root_.slhdsa.WorkerCrypto.ticket_eq]
  have idx {T : Type} (xs : alloc.vec.Vec T) (hi : j.val < xs.length) :
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) xs j = ok xs.val[j.val] := by
    rw [alloc.vec.Vec.index_slice_index]
    obtain ⟨_,ran,rfl⟩ := _root_.slhdsa.spec_imp_exists (alloc.vec.Vec.index_usize_spec xs j hi)
    exact ran
  have nativeValid : j.val < (nativeLayers layers).length := by simpa [nativeLayers,alloc.vec.Vec.length] using valid
  unfold extractedWotsRow
  rw [idx layers valid,idx (nativeLayers layers) nativeValid,bind_ok,bind_ok]
  simp only [nativeLayers,alloc.vec.Vec.from_val,List.getElem_map]
  cases entry : layers.val[j.val] with
  | mk a k =>
    simp [address.Adrs.with_type,address.Adrs.with_keypair,address.WOTS_HASH,
      _root_.slhdsa.address.Adrs.with_type,_root_.slhdsa.address.Adrs.with_keypair,
      _root_.slhdsa.address.WOTS_HASH]
    rfl

omit specialization in
private theorem splitOk (x : Result α) (f : α → Result β) {b}
    (eq : (x >>= f) = ok b) : ∃ a, x=ok a ∧ f a=ok b := by
  cases x with
  | ret a => exact ⟨a,rfl,by simpa using eq⟩
  | div => simp_all
  | vis e k => cases e with | fail e => simp_all

/-- The exact successful native-call premise consumed by the concurrent WOTS loop.
Every value also comes with the preserved address, root and WOTS signature bytes. -/
theorem native_wots_values {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) (hp : _root_.slhdsa.PN _root_.slhdsa.WorkerCrypto.Config.p N)
    (size : len.val = _root_.slhdsa.WorkerCrypto.Config.p.d.val)
    (layerSize : len.val≤layers.length) (rootSize : len.val≤roots.length) :
    ∃ values : Std.Usize → alloc.vec.Vec Std.U8, ∀ j : Std.Usize, j.val<len.val →
      (∃ addr index root typed keyed,
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) layers j=ok (addr,index) ∧
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) roots j=ok root ∧
        address.Adrs.with_type addr address.WOTS_HASH=ok typed ∧
        address.Adrs.with_keypair typed index=ok keyed ∧
        shake.wots.wots_sign root sk seed keyed=ok (values j)) ∧
      _root_.slhdsa.WorkerPayload.nativeTicket _root_.slhdsa.WorkerCrypto.Config.host
        _root_.slhdsa.WorkerCrypto.Config.p (nativeLayers layers) roots j sk seed=ok (values j) ∧
      _root_.slhdsa.bytes (values j).val =
        Spec.wotsSign (_root_.slhdsa.Shake.params _root_.slhdsa.WorkerCrypto.Config.p)
          (_root_.slhdsa.bytes roots.val[j.val]!.val) (_root_.slhdsa.bytes sk.val) (_root_.slhdsa.bytes seed.val)
          { (_root_.slhdsa.adrsS (nativeLayers layers).val[j.val]!.1).setTypeAndClear Spec.WOTS_HASH with
            keypair := (nativeLayers layers).val[j.val]!.2.val } := by
  classical
  have law (j : Std.Usize) (live : j.val<len.val) := _root_.slhdsa.WorkerPayload.compute_succeeds
    _root_.slhdsa.WorkerCrypto.Config.host _root_.slhdsa.WorkerCrypto.Config.p hp sk seed (nativeLayers layers) roots j.val
    (size ▸ live) (by simpa [nativeLayers,alloc.vec.Vec.length] using live.trans_le layerSize) (live.trans_le rootSize)
  let values (j : Std.Usize) := if h : j.val<len.val then Classical.choose (law j h) else default
  refine ⟨values,?_⟩
  intro j live
  obtain ⟨native,data⟩ := Classical.choose_spec (law j live)
  have value : values j = Classical.choose (law j live) := by simp [values,live]
  rw [←value] at native data
  have small : j.val < 2^UScalarTy.Usize.numBits := j.bv.isLt
  simp only [_root_.slhdsa.WorkerPayload.compute,dite_eq_left small] at native
  have same : Usize.ofNatCore j.val small = j := UScalar.eq_of_val_eq rfl
  rw [same] at native
  refine ⟨?_,native,data⟩
  have exactRow := (generated_wots_native sk seed layers roots j (live.trans_le layerSize)).trans native
  unfold extractedWotsRow at exactRow
  obtain ⟨⟨addr,index⟩,layer,rest⟩ := splitOk _ _ exactRow
  obtain ⟨root,rootRead,rest⟩ := splitOk _ _ rest
  obtain ⟨typed,tag,rest⟩ := splitOk _ _ rest
  obtain ⟨keyed,key,rest⟩ := splitOk _ _ rest
  obtain ⟨row,sign,ret⟩ := splitOk _ _ rest
  cases Result.ok_injective ret
  exact ⟨addr,index,root,typed,keyed,layer,rootRead,tag,key,sign⟩

end slhdsa
#print axioms NativeSigner.slhdsa.generated_wots_native
#print axioms NativeSigner.slhdsa.native_wots_values
"""
    )


def native_package(package, target):
    host, machine, perm, wide = TARGET[target]
    bindings = dict(BINDINGS)
    for name, op in (("secrets", "secrets"), ("nodes_active", "nodes")):
        args = (machine, perm) if name == "secrets" else (machine, perm, wide)
        kernel = " ".join(("@_root_.slhdsa.ParallelLowFors." + op, *args, "_"))
        bindings["shake.slh.parallel.shake_fors_simd." + name] = (
            "fun sk pk addr => " + kernel + " sk pk (nativeAddress addr)"
        )
    generated = (package / "Funs.lean").read_text()
    effects = effects_witness(generated, package.name)
    extracted_imports = [
        line for line in effects.splitlines() if line.startswith("import Parallel.")
    ]
    source = [
        "import Parallel.WorkerCrypto",
        "import Parallel.WorkerIterators",
        "import Parallel.WorkerPoolRuntime",
        "import Parallel.WorkerWotsHistory",
        "import Parallel.WorkerCounterSafety",
        *extracted_imports,
        "import Parallel.WorkerActualReturn",
        "set_option linter.unusedSectionVars false",
        "set_option linter.ambiguousOpen false",
        "namespace NativeSigner",
        "noncomputable section",
        "set_option linter.concreteInstances false",
    ]
    for module in ("TypesExternal", "Types", "FunsExternal", "Funs"):
        body = (package / (module + ".lean")).read_text()
        body = body.split("@[expose] public section\n", 1)[1]
        if module == "FunsExternal":
            source.append(CONVERSIONS)
            source.append(
                "class Specialization where\n  p : _root_.slhdsa.params.Params\n"
                + ("  sha3 : Bool\n" if ".sha3" in host else "")
                + "variable [specialization : Specialization]\n"
                + "local instance : _root_.slhdsa.WorkerCrypto.Config := ⟨"
                + host
                + ", specialization.p⟩"
            )
            body = body.replace("open slhdsa", "open NativeSigner.slhdsa")
            for name, impl in bindings.items():
                pattern = r"^axiom " + re.escape(name) + r"(?=\s)(.*?)(?=\n\n)"
                body, count = re.subn(
                    pattern,
                    lambda m, name=name, impl=impl: (
                        "def " + name + m[1] + " :=\n  " + impl
                    ),
                    body,
                    flags=re.MULTILINE | re.DOTALL,
                )
                if count != 1:
                    raise ValueError("unexpected generated native interface: " + name)
        source.append(body.replace("noncomputable section\n", ""))
    # Reuse the identical effect and callback generator on the instantiated code.
    # Imports have to precede the namespace, and its file-level anonymous
    # section ends at the import boundary in the standalone version.
    local_effects = "\n".join(
        line for line in effects.splitlines() if not line.startswith("import ")
    )
    source.extend(
        (
            copy_witness(generated),
            ticket_witness(generated),
            local_effects,
            "end",
            control_witness(generated),
            runtime_witness(generated),
            completion_witness(),
            NATIVE_SCHEDULE,
            "end",
            "end NativeSigner",
        )
    )
    return "\n".join(source)


NATIVE_SCHEDULE = """
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std Result ControlFlow ParallelWorkerHeap ParallelWorkerRuntime ParallelWorkerInterleave

/-- The WOTS byte computed by the complete instantiated native signer is invariant
under arbitrary scheduled steps of the extracted interaction tree. -/
theorem native_wots_schedules {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) (hp : _root_.slhdsa.PN _root_.slhdsa.WorkerCrypto.Config.p N)
    (size : len.val=_root_.slhdsa.WorkerCrypto.Config.p.d.val)
    (layerSize : len.val≤layers.length) (rootSize : len.val≤roots.length) :
    ∃ values : Std.Usize → alloc.vec.Vec Std.U8,
      (∀ j : Std.Usize, j.val<len.val →
        _root_.slhdsa.WorkerPayload.nativeTicket _root_.slhdsa.WorkerCrypto.Config.host
          _root_.slhdsa.WorkerCrypto.Config.p (nativeLayers layers) roots j sk seed=ok (values j)) ∧
      ∀ (h h' : Shared N) (workers : Nat) (threads : List (Program (Shared N) Unit)),
        Steps h (List.replicate workers
          ((interpreted.phase_two_loop (certifiedOps N) (certifiedSync N) sk seed layers .phase2Next
            (ParallelWorkerCounterSafety.physicalTable N Key.wotsSigs _ (fun _ => rfl) len) roots).raw)) h' threads →
        Wots.Correct len values h → Wots.Correct len values h' := by
  obtain ⟨values,law⟩ := native_wots_values sk seed layers roots len hp size layerSize rootSize
  refine ⟨values,fun j live => (law j live).2.1,?_⟩
  intro h h' workers threads run initial
  rw [certified_wots_loop] at run
  exact all_wots_schedules sk seed layers roots len values (fun j live => (law j live).1) h h' workers threads run initial

def stagedLayers (layers : _root_.slhdsa.ParallelXmssTicket.Layers) :
    alloc.vec.Vec (address.Adrs × Std.U32) :=
  alloc.vec.Vec.from (layers.val.map (fun (a,k) => (stagedAddress a,k))) (by simp)

theorem layers_roundtrip (xs : _root_.slhdsa.ParallelXmssTicket.Layers) :
    nativeLayers (stagedLayers xs)=xs := by
  apply alloc.vec.Vec.ext
  simp [nativeLayers,stagedLayers,alloc.vec.Vec.from_val,List.map_map,Function.comp_def,native_address_roundtrip]

/-- Every normal schedule of the actual phase-two interaction tree, using the
same roots accepted by the wait, yields FIPS signature bytes when the extracted
post-join Rust caller reads its final heap. The native phase-one program
constructs all of the supplied message, address and root values. -/
theorem native_joined_signature {N : Std.Usize}
    (hp : _root_.slhdsa.PN specialization.p N) (runs : _root_.slhdsa.WorkerFetch.SigningRuns specialization.p)
    (md : Slice Std.U8) (sk seed : Array Std.U8 N) (a : _root_.slhdsa.address.Adrs) (r : Array Std.U8 N)
    (tree : Std.U64) (leaf : Std.U32) (threads : Std.Usize) (enabled : 2≤threads.val)
    (mdLen : md.length=(_root_.slhdsa.Shake.params specialization.p).mdBytes)
    (treeLt : tree.val<2^(specialization.p.h.val-specialization.p.hp.val))
    (leafLt : leaf.val<2^specialization.p.hp.val)
    (address : _root_.slhdsa.adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear Spec.FORS_TREE with keypair:=leaf.val}) :
    let p := specialization.p
    let target := _root_.slhdsa.WorkerCrypto.Config.host
    let len := UScalar.cast .Usize p.d
    ∃ s, _root_.slhdsa.WorkerPayload.prepare target runs.toSession.schedules p md sk seed a r tree leaf threads = ok s ∧
      ∀ (base : Heap N) {h : Monitor N} {g decode facts pc seen} (_cert : _root_.slhdsa.WorkerBarrierMir.Certified g decode facts),
        _root_.slhdsa.WorkerBarrierMir.Interleaved s.forest s.auth s.roots g decode h pc seen →
        ∀ (valid : pc<g.length), decode g[pc].ops=.accept →
        let initial : Shared N := ⟨barrierHeap base h,true⟩
        ∀ (final : Shared N) (workers : Nat) (out : List (Program (Shared N) Unit)),
          0<workers → len.val+workers < 2^UScalarTy.Usize.numBits →
          initial.counts .phase2Next=0 → (∀ j,initial.cells (.wotsSigs j)=none) →
          Steps initial (List.replicate workers
            ((interpreted.phase_two_loop (certifiedOps N) (certifiedSync N) sk seed (stagedLayers s.layers)
              .phase2Next (ParallelWorkerCounterSafety.physicalTable N Key.wotsSigs _ (fun _ => rfl) len) s.roots).raw)) final out →
          (∀ w∈out,w=pure ()) →
          ∃ sig, final.cells .roots=some s.roots ∧
            _root_.slhdsa.ParallelSignJoin.run (ok threads) (_root_.slhdsa.WorkerPayload.heapJoin final.toHeap)
              p md sk seed a r tree leaf = ok (some sig) ∧
            _root_.slhdsa.bytes sig.val = _root_.slhdsa.bytes r.val ++
              Spec.forsSign (_root_.slhdsa.Shake.params p) (_root_.slhdsa.bytes md.val) (_root_.slhdsa.bytes sk.val)
                (_root_.slhdsa.bytes seed.val) (_root_.slhdsa.adrsS a) ++
              Spec.htSign (_root_.slhdsa.Shake.params p)
                (Spec.forsPkFromSig (_root_.slhdsa.Shake.params p)
                  (Spec.forsSign (_root_.slhdsa.Shake.params p) (_root_.slhdsa.bytes md.val) (_root_.slhdsa.bytes sk.val)
                    (_root_.slhdsa.bytes seed.val) (_root_.slhdsa.adrsS a))
                  (_root_.slhdsa.bytes md.val) (_root_.slhdsa.bytes seed.val) (_root_.slhdsa.adrsS a))
                (_root_.slhdsa.bytes sk.val) (_root_.slhdsa.bytes seed.val) tree.val leaf.val := by
  intro p target len
  obtain ⟨s,prepared,correct,_⟩ := _root_.slhdsa.WorkerPayload.prepare_native
    target runs.toSession.schedules p hp md sk seed a r tree leaf threads enabled mdLen treeLt leafLt address
  refine ⟨s,prepared,?_⟩
  intro base h g decode facts pc seen cert wait valid accept initial final workers out positive cap zero fresh run normal
  have published := _root_.slhdsa.WorkerBarrierMir.accepts_installed cert wait valid accept
  have size : len.val=p.d.val := by dsimp only [len]; scalar_tac
  have layerSize : len.val≤(stagedLayers s.layers).length := by
    rw [size]
    simpa [stagedLayers,alloc.vec.Vec.length,alloc.vec.Vec.from_val] using correct.2.2.2.1.1.ge
  obtain ⟨values,law⟩ := native_wots_values sk seed (stagedLayers s.layers) s.roots len hp size layerSize
      (by rw [size]; exact correct.2.2.2.2.1)
  have computed : WotsValues sk seed (stagedLayers s.layers) s.roots len values := fun j live => (law j live).1
  have cells := completed_wots_schedules sk seed (stagedLayers s.layers) s.roots len values computed
    initial final workers positive cap out run zero fresh normal
  rw [certified_wots_loop,wots_worker_eq _ _ _ _ _ _ computed] at run
  have clear : Wots.Correct len values initial := by intro j v found; rw [fresh] at found; contradiction
  have unchanged := Wots.untouched values initial final workers out run clear
  have f := (unchanged .sigFors (by simp)).trans (congrArg _root_.slhdsa.WorkerBarrier.Cells.fors published)
  have a' := (unchanged .xmssAuth (by simp)).trans (congrArg _root_.slhdsa.WorkerBarrier.Cells.auth published)
  have roots := (unchanged .roots (by simp)).trans (congrArg _root_.slhdsa.WorkerBarrier.Cells.roots published)
  obtain ⟨sig,returned,data⟩ := _root_.slhdsa.WorkerPayload.actual_return target p hp md sk seed a r tree leaf
    leafLt threads enabled s correct final.toHeap f a' (fun j hj => by
      have live : j.val<len.val := size.symm ▸ hj
      refine ⟨values j,cells j live,?_⟩
      have agreement := (law j live).2.1
      rw [layers_roundtrip] at agreement
      exact agreement)
  exact ⟨sig,roots,returned,data⟩

end slhdsa.WorkerEffects
#print axioms NativeSigner.slhdsa.WorkerEffects.native_wots_schedules
#print axioms NativeSigner.slhdsa.WorkerEffects.native_joined_signature
"""

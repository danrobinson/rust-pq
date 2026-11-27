"""Link the generated native reduction loops to their byte-level specifications."""

REDUCER_VALUES = """
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std ControlFlow Result

theorem frozen_fors_pack {N : Usize} (ops : Ops Option Result)
    (get : ∀ {T : Type} (v : Option T), ops.get v = ok v)
    (loops : ∀ {A B : Type} (f : A → Result (ControlFlow A B)), ops.runLoop f = loop f)
    (iter : core.slice.iter.Iter (Option (Array U8 N))) (v : alloc.vec.Vec U8) :
    interpreted.reduce_loop1 ops iter v = _root_.slhdsa.ParallelForestPack.pack_fors_loop iter v := by
  simp [interpreted.reduce_loop1, _root_.slhdsa.ParallelForestPack.pack_fors_loop,
    loops, interpreted.reduce_loop1.body, _root_.slhdsa.ParallelForestPack.pack_fors_loop.body,
    get, _root_.slhdsa.ParallelSignJoin.readCell]
  congr 1
  funext x
  congr 1
  funext pair
  rcases pair with ⟨o,it⟩
  cases o <;> rfl

/-- One generated root-walk iteration, including its native hash and address fields. -/
theorem native_root_climb_body {Cell : Type → Type} (ops : Ops Cell Result)
    {N : Usize} (hp : Usize) (seed : Array U8 N) (auth : alloc.vec.Vec (Array U8 N))
    (j : Usize) (a : address.Adrs) (it : core.ops.range.Range U32) (node : Array U8 N) (idx : U32) :
    interpreted.reduce_loop3_loop0.body ops hp seed auth j a it node idx =
      @_root_.slhdsa.ParallelRootWalk.all_roots_loop0_loop0.body
        (_root_.slhdsa.ParallelRootWalk.hosted _root_.slhdsa.WorkerCrypto.rootHost)
        N hp seed auth j (nativeAddress a) it node idx := by
  unfold interpreted.reduce_loop3_loop0.body _root_.slhdsa.ParallelRootWalk.all_roots_loop0_loop0.body
  congr 1
  funext pair
  rcases pair with ⟨o,next⟩
  cases o with
  | none => rfl
  | some h =>
    have same {T : Type} (x : Result T) : (liftM x : Result T) = x := rfl
    have unwrap {A B : Type} (x : A) (f : A → Result B) : (ok x >>= f) = f x := by simp
    simp only [unwrap,same,address.Adrs.with_word2,address.Adrs.with_word3,
      _root_.slhdsa.address.Adrs.with_word2,_root_.slhdsa.address.Adrs.with_word3,
      shake.xmss.hash2,_root_.slhdsa.WorkerCrypto.hash,nativeAddress,bind_ok]
    rfl

theorem native_root_climb {Cell : Type → Type} (ops : Ops Cell Result)
    (loops : ∀ {A B : Type} (f : A → Result (ControlFlow A B)), ops.runLoop f = loop f)
    {N : Usize} (it : core.ops.range.Range U32) (hp : Usize) (seed : Array U8 N)
    (auth : alloc.vec.Vec (Array U8 N)) (j : Usize) (a : address.Adrs) (node : Array U8 N) (idx : U32) :
    interpreted.reduce_loop3_loop0 ops it hp seed auth j a node idx =
      @_root_.slhdsa.ParallelRootWalk.all_roots_loop0_loop0
        (_root_.slhdsa.ParallelRootWalk.hosted _root_.slhdsa.WorkerCrypto.rootHost)
        N it hp seed auth j (nativeAddress a) node idx := by
  simp only [interpreted.reduce_loop3_loop0,_root_.slhdsa.ParallelRootWalk.all_roots_loop0_loop0,
    loops,native_root_climb_body]

/-- Packing a snapshot of the published direct slots produces the FIPS FORS signature. -/
theorem frozen_fors_fips {N : Usize} (ops : Ops Option Result)
    (get : ∀ {T : Type} (v : Option T), ops.get v = ok v)
    (loops : ∀ {A B : Type} (f : A → Result (ControlFlow A B)), ops.runLoop f = loop f)
    (p : _root_.slhdsa.params.Params) (hp : _root_.slhdsa.PN p N)
    (cells : alloc.vec.Vec (Option (Array U8 N))) (md sk pk : Spec.Bytes) (a : Spec.Adrs)
    (count : cells.length=p.k.val*(1+p.a.val))
    (published : ∀ j<cells.length, ∃ row, cells.val[j]! = some row ∧
      _root_.slhdsa.bytes row.val=(_root_.ParallelCached.forsRows (_root_.slhdsa.Shake.params p) md sk pk a)[j]!) :
    (do let cap ← _root_.slhdsa.params.Params.fors_sig_bytes p
        let it ← core.slice.Slice.iter cells.deref
        interpreted.reduce_loop1 ops it (alloc.vec.Vec.with_capacity U8 cap))
      ⦃ out => _root_.slhdsa.bytes out.val=Spec.forsSign (_root_.slhdsa.Shake.params p) md sk pk a ⦄ := by
  simp only [frozen_fors_pack ops get loops]
  exact _root_.slhdsa.ParallelForestPack.pack_fips p hp cells md sk pk a count published
end slhdsa.WorkerEffects
#print axioms NativeSigner.slhdsa.WorkerEffects.frozen_fors_fips
#print axioms NativeSigner.slhdsa.WorkerEffects.native_root_climb
"""

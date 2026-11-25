import Parallel.ScalarForsLow
import Parallel.ScalarForsPublish

open Lean Elab Command
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (dst,prior,bindings) in [
      (`LowTicketApple,`ScalarTicketApple,← Cachepath.NativeHashReplay.appleBindings),
      (`LowTicketX86,`ScalarTicketX86,Cachepath.NativeHashReplay.bindings `KxouterRust `slhdsa.ShakeBatch.X86),
      (`LowTicketLinux,`ScalarTicketLinux,Cachepath.NativeHashReplay.bindings `KspongeLRust `slhdsa.ShakeBatch.Linux)] do
    let node := `slhdsa.ParallelScalarFors.node
    PlatformProof.replay dst ((node,prior ++ node)::bindings) #[`slhdsa.ParallelScalarFors.low_spec]
      [`Parallel.ScalarForsLowProgram,`Parallel.ScalarForsLow,`Parallel.ScalarForsProgram,`Cachepath,`Shakeopt]

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelScalarFors
noncomputable def hostedLow {N : Usize} (host : Platform) (p : params.Params) :=
  match host with
  | .apple sha3 => @LowTicketApple.slhdsa.ParallelScalarFors.low_ticket (wide (.apple sha3) p) N
  | .x86 => @LowTicketX86.slhdsa.ParallelScalarFors.low_ticket (wide .x86 p) N
  | .linux => @LowTicketLinux.slhdsa.ParallelScalarFors.low_ticket narrow N

set_option maxHeartbeats 1100000 in
theorem low_published {N : Usize} (host : Platform) (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (domain : ForsHorizontal.Domain a) (choices : alloc.vec.Vec U32)
    (t h low : U32) (stride : Usize) (journal : Journal N)
    (existsDigit : t.val<choices.length) (tree : t.val<35) (height : h.val≤14)
    (selected : choices.val[t.val]!.val<2^h.val) (bound : low.val≤h.val) (size : stride.val=h.val+1) :
    hostedLow host p sk seed a choices t h low stride journal ⦃ out =>
      LowValues p sk seed a t.val h.val choices.val[t.val]!.val low.val out ⦄ := by
  have laws := (native_laws host p hp sk seed a domain).1
  cases host with
  | apple sha3 =>
    apply @LowTicketApple.slhdsa.ParallelScalarFors.low_spec (wide (.apple sha3) p) N p hp sk seed a choices t h low stride journal _ existsDigit tree height selected bound size
    intro i j hi room
    obtain ⟨v,call,cell,bytesEq⟩ := spec_imp_exists (laws i j 0#usize hi room)
    simp only [actions,ScalarTicketApple.slhdsa.ParallelScalarFors.direct_node_ticket] at call
    cases eq : @ScalarTicketApple.slhdsa.ParallelScalarFors.node (wide (.apple sha3) p) _ sk i j seed a <;>
      simp [eq,bind_ok] at call ⊢ <;> grind
  | x86 =>
    apply @LowTicketX86.slhdsa.ParallelScalarFors.low_spec (wide .x86 p) N p hp sk seed a choices t h low stride journal _ existsDigit tree height selected bound size
    intro i j hi room
    obtain ⟨v,call,cell,bytesEq⟩ := spec_imp_exists (laws i j 0#usize hi room)
    simp only [actions,ScalarTicketX86.slhdsa.ParallelScalarFors.direct_node_ticket] at call
    cases eq : @ScalarTicketX86.slhdsa.ParallelScalarFors.node (wide .x86 p) _ sk i j seed a <;>
      simp [eq,bind_ok] at call ⊢ <;> grind
  | linux =>
    apply @LowTicketLinux.slhdsa.ParallelScalarFors.low_spec narrow N p hp sk seed a choices t h low stride journal _ existsDigit tree height selected bound size
    intro i j hi room
    obtain ⟨v,call,cell,bytesEq⟩ := spec_imp_exists (laws i j 0#usize hi room)
    simp only [actions,ScalarTicketLinux.slhdsa.ParallelScalarFors.direct_node_ticket] at call
    cases eq : @ScalarTicketLinux.slhdsa.ParallelScalarFors.node narrow _ sk i j seed a <;>
      simp [eq,bind_ok] at call ⊢ <;> grind

/-- Queue selection from the signer's actual message-digest decoder. -/
theorem low_from_message {N : Usize} (host : Platform) (p : params.Params) (hp : PN p N)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (domain : ForsHorizontal.Domain a)
    (t low : U32) (stride : Usize) (journal : Journal N) (bits : p.k.val*p.a.val≤8*md.length)
    (tree : t.val<p.k.val) (bound : low.val≤p.a.val) (size : stride.val=p.a.val+1) :
    Std.bind (util.base_2b md p.a (UScalar.cast .Usize p.k)) (fun digits =>
      hostedLow host p sk seed a digits t p.a low stride journal) ⦃ out =>
      LowValues p sk seed a t.val p.a.val (Spec.base2b (bytes md.val) p.a.val p.k.val)[t.val]! low.val out ⦄ := by
  have height : p.a.val≤14 := hp.valid.a_le
  have positive : 1≤p.a.val := hp.valid.a_pos
  have count : p.k.val≤35 := hp.valid.k_le
  obtain ⟨digits,read,indices,len,valid⟩ := spec_imp_exists (base_2b_spec md p.a (UScalar.cast .Usize p.k)
    (by omega) (by simpa using bits))
  simp only [U32.cast_Usize_val_eq] at indices len
  have inside : t.val<digits.length := len.symm ▸ tree
  have selected : digits.val[t.val]!.val<2^p.a.val := by
    apply valid
    rw [getElem!_pos digits.val t.val inside]
    exact List.getElem_mem _
  have pick : (Spec.base2b (bytes md.val) p.a.val p.k.val)[t.val]! = digits.val[t.val]!.val := by
    rw [←indices,fors_nats_getElem! _ _ inside,getElem!_pos digits.val t.val inside]
  rw [read,bind_ok,pick]
  exact low_published host p hp sk seed a domain digits t p.a low stride journal inside (by omega) height selected bound size

end slhdsa.ParallelScalarFors

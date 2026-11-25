import Parallel.LowForsTicket
import ForsDriver.HostedTree
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelLowFors
open NativeVerify
noncomputable section

@[instance_reducible] def linuxHost : Host Kldisp.machine :=
  ⟨fullActive Kldisp.machine KldispRust.shake256.parallel.available⟩
@[instance_reducible] def appleHost (sha3 : Bool) : Host (AppleHybrid.machine sha3) := ⟨appleActive sha3⟩
@[instance_reducible] def x86Host : Host Kxdispatch.machine :=
  ⟨fullActive Kxdispatch.machine KxdispatchRust.shake256.parallel.available⟩

@[instance_reducible] def appleWide (sha3 : Bool) (p : params.Params) : Wide :=
  ⟨@ForsTreeApple.slhdsa.ForsHorizontal.subtree (BufferedApple.slhdsa.Buffered.Host.apple sha3 p)⟩
@[instance_reducible] def x86Wide (p : params.Params) : Wide :=
  ⟨@ForsTreeX86.slhdsa.ForsHorizontal.subtree (BufferedX86.slhdsa.Buffered.Host.x86 p)⟩

theorem linux_spec [wide : Wide] {N} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (addr : address.Adrs)
    (choices : alloc.vec.Vec U32) (first : U16) (active low : U8) (stride : Usize)
    (domain : addr.typ=address.FORS_TREE ∧ addr.word2=0#u32 ∧ addr.word3=0#u32)
    (ha : p.a.val≤14) (count : choices.length≤35) (digits : ∀ t<choices.length, choices.val[t]!.val<2^p.a.val)
    (enabled : 0<active.val) (width : active.val≤3) (capacity : first.val+active.val≤choices.length)
    (height : low.val≤p.a.val) (shape : stride.val=p.a.val+1) :
    @ticket Kldisp.machine linuxHost wide N sk seed addr choices p.a first active low stride ⦃ out =>
      Fields first.val active.val stride.val (low.val+1) (field p sk seed addr choices) out ⦄ :=
  @ticket_spec Kldisp.machine linuxHost wide N p hp sk seed addr choices first active low stride
    NativeVerify.linux domain ha count digits enabled width capacity height (Or.inl (by decide)) shape

theorem apple_spec (sha3 : Bool) {N} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (addr : address.Adrs)
    (choices : alloc.vec.Vec U32) (first : U16) (active low : U8) (stride : Usize)
    (domain : addr.typ=address.FORS_TREE ∧ addr.word2=0#u32 ∧ addr.word3=0#u32)
    (ha : p.a.val≤14) (count : choices.length≤35) (digits : ∀ t<choices.length, choices.val[t]!.val<2^p.a.val)
    (enabled : 0<active.val) (width : active.val≤8) (capacity : first.val+active.val≤choices.length)
    (height : low.val≤p.a.val) (small : low.val≤3) (shape : stride.val=p.a.val+1) :
    @ticket (AppleHybrid.machine sha3) (appleHost sha3) (appleWide sha3 p) N sk seed addr choices p.a first active low stride ⦃ out =>
      Fields first.val active.val stride.val (low.val+1) (field p sk seed addr choices) out ⦄ :=
  @ticket_spec (AppleHybrid.machine sha3) (appleHost sha3) (appleWide sha3 p) N p hp sk seed addr choices first active low stride
    (NativeVerify.apple sha3) domain ha count digits enabled width capacity height (Or.inr small) shape

theorem x86_spec (avx512 : GatherRust.avx512Available=true) {N} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (addr : address.Adrs)
    (choices : alloc.vec.Vec U32) (first : U16) (active low : U8) (stride : Usize)
    (domain : addr.typ=address.FORS_TREE ∧ addr.word2=0#u32 ∧ addr.word3=0#u32)
    (ha : p.a.val≤14) (count : choices.length≤35) (digits : ∀ t<choices.length, choices.val[t]!.val<2^p.a.val)
    (enabled : 0<active.val) (width : active.val≤8) (capacity : first.val+active.val≤choices.length)
    (height : low.val≤p.a.val) (small : low.val≤3) (shape : stride.val=p.a.val+1) :
    @ticket Kxdispatch.machine x86Host (x86Wide p) N sk seed addr choices p.a first active low stride ⦃ out =>
      Fields first.val active.val stride.val (low.val+1) (field p sk seed addr choices) out ⦄ :=
  @ticket_spec Kxdispatch.machine x86Host (x86Wide p) N p hp sk seed addr choices first active low stride
    (NativeVerify.x86 avx512) domain ha count digits enabled width capacity height (Or.inr small) shape
end
end slhdsa.ParallelLowFors

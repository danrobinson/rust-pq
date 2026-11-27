import Parallel.ForsMetaGroup
import Parallel.ForsMergeHosted
import Parallel.ScalarForsPublish
import Parallel.ForsTickets
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsMetadata
open ParallelForsMerge (Meta)
abbrev Cells (N : Usize) := alloc.vec.Vec (Option (Array U8 N))

noncomputable def merge (host : ParallelScalarFors.Platform) {N : Usize} (m : Meta) (slots : Cells N)
    (seed : Array U8 N) (addr : address.Adrs) (stride : Usize) : Result (Usize × Array U8 N) :=
  match host with
  | .apple _ => RootTableApple.ForsMerge.slhdsa.ParallelForsMerge.merge_fors m slots seed addr stride
  | .linux => RootTableArm.ForsMerge.slhdsa.ParallelForsMerge.merge_fors m slots seed addr stride
  | .x86 => RootTableX86.ForsMerge.slhdsa.ParallelForsMerge.merge_fors m slots seed addr stride

def ChunkCells {N} (p : params.Params) (sk : Spec.Bytes) (seed : Array U8 N) (addr : address.Adrs)
    (choices : alloc.vec.Vec U32) (t : Nat) (j sub : U32) (start : Nat) (slots : Cells N) :=
  ∀ c<2^(j.val-sub.val), ∃ v, slots.val[start+c]! = some v ∧
    bytes v.val=Spec.forsNode (Shake.params p) sk
      (ForsDriver.sibling choices.slice p.a t j.val*2^(j.val-sub.val)+c) sub.val (bytes seed.val) (adrsS addr)

theorem record_merge {N} (host : ParallelScalarFors.Platform) (p : params.Params) (hp : PN p N)
    (m : Meta) (slots : Cells N) (sk : Spec.Bytes) (seed : Array U8 N) (addr : address.Adrs)
    (stride : Usize) (choices : alloc.vec.Vec U32) (t start : Nat) (j sub : U32)
    (record : Record choices p.a j sub t start m) (tree : t<p.k.val) (size : choices.length=p.k.val)
    (selected : choices.val[t]!.val<2^p.a.val) (field : j.val<p.a.val) (lower : sub.val≤j.val)
    (shape : stride.val=1+p.a.val) (fits : start+2^(j.val-sub.val)≤slots.length)
    (children : ChunkCells p sk seed addr choices t j sub start slots) :
    merge host m slots seed addr stride ⦃ (dest,r) => dest.val=t*(1+p.a.val)+1+j.val ∧
      bytes r.val=Spec.forsNode (Shake.params p) sk (ForsDriver.sibling choices.slice p.a t j.val) j.val (bytes seed.val) (adrsS addr) ⦄ := by
  obtain ⟨tv,hv,rv,sv,pv,cv⟩ := record
  have lim := ParallelForsTicket.sibling_room choices p.a j t hp.valid.a_le field (by rw [size];exact hp.valid.k_le) (by omega) selected
  change (ForsDriver.sibling choices.slice p.a t j.val+1)*2^j.val≤1048576 at lim
  have small := Nat.mul_le_mul_left (ForsDriver.sibling choices.slice p.a t j.val+1)
    (Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le j.val sub.val))
  have room : (m.root_idx.val+1)*2^(m.height.val-m.sub_h.val)≤2^32 := by rw [rv,hv,sv];omega
  have stored : ∀ c<m.chunks.val, ∃ v, slots.val[m.slot_start.val+c]! = some v ∧
      bytes v.val=Spec.forsNode (Shake.params p) sk (m.root_idx.val*m.chunks.val+c) m.sub_h.val (bytes seed.val) (adrsS addr) := by
    intro c hc;rw [rv,cv,pv,sv];exact children _ (by omega)
  have cap : m.slot_start.val+m.chunks.val≤slots.length := by rwa [pv,cv]
  have count : m.chunks.val=2^(m.height.val-m.sub_h.val) := by rwa [hv,sv]
  have tr : m.tree.val<p.k.val := tv ▸ tree
  have fld : m.height.val<p.a.val := hv ▸ field
  have lo : m.sub_h.val≤m.height.val := by rwa [sv,hv]
  cases host
  · simpa only [merge,tv,hv,rv] using RootTableApple.ForsMerge.slhdsa.ParallelForsMerge.merge_spec p hp m slots seed sk addr stride tr fld shape lo count cap room stored
  · simpa only [merge,tv,hv,rv] using RootTableArm.ForsMerge.slhdsa.ParallelForsMerge.merge_spec p hp m slots seed sk addr stride tr fld shape lo count cap room stored
  · simpa only [merge,tv,hv,rv] using RootTableX86.ForsMerge.slhdsa.ParallelForsMerge.merge_spec p hp m slots seed sk addr stride tr fld shape lo count cap room stored

/-- Publication is stated in terms of the returned Rust worker row. Its payload and
destination are derived from the scalar worker theorem. -/
theorem scalar_cells {N} (host : ParallelScalarFors.Platform) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (addr : address.Adrs) (domain : ForsHorizontal.Domain addr)
    (choices : alloc.vec.Vec U32) (t j sub : U32) (start : Usize) (sat : Bool) (slots : Cells N)
    (tree : t.val<p.k.val) (field : j.val<p.a.val) (lower : sub.val<j.val)
    (selected : choices.val[t.val]!.val<2^p.a.val) (fit : start.val+2^(j.val-sub.val)≤slots.length)
    (published : ∀ c : Usize, c.val<2^(j.val-sub.val) → ∀ w,
      ParallelScalarFors.run (ParallelScalarFors.actions host p sk seed addr).2
        ((if sat then ParallelScalarFors.prepare_saturating else ParallelScalarFors.prepare_split)
          t p.a j choices.val[t.val]! sub start c)=ok w → slots.val[w.1.val]! = some w.2) :
    ChunkCells p (bytes sk.val) seed addr choices t.val j sub start.val slots := by
  intro c hc
  have limit := slots.len_ineq
  change slots.length≤Usize.max at limit
  have sz : c<Usize.max := by omega
  have mx : Usize.max < 2^UScalarTy.Usize.numBits := by
    have raw := core.num.Usize.MAX.hmax
    rwa [show core.num.Usize.MAX.val=Usize.max from Usize.ofNatCore_val_eq ..] at raw
  let k := Usize.ofNatCore c (sz.trans mx)
  have kv : k.val=c := Usize.ofNatCore_val_eq ..
  obtain ⟨w,run,dest,value⟩ := spec_imp_exists (ParallelScalarFors.split_published host p hp sk seed addr domain sat
    t p.a j choices.val[t.val]! sub start k (lt_of_lt_of_le tree hp.valid.k_le) hp.valid.a_le field selected lower (kv ▸ hc) (by omega))
  refine ⟨w.2,?_,?_⟩
  · have cell := published k (kv ▸ hc) w run
    rwa [dest,kv] at cell
  · rw [ForsDriver.sibling_local _ _ _ _ field];simpa only [ParallelScalarFors.sibling,kv,alloc.vec.Vec.val] using value

theorem group_cells [wide : ParallelForsTicket.Wide] {N} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (addr : address.Adrs) (domain : ForsHorizontal.Domain addr)
    (choices : alloc.vec.Vec U32) (first : U16) (active height low : U8) (j sub : U32)
    (start chunks : Usize) (slots : Cells N) (lane : Nat) (hl : lane<active.val)
    (field : height.val<p.a.val) (lower : low.val≤height.val) (defs : j.val=height.val ∧ sub.val=low.val)
    (width : active.val≤3) (count : choices.length≤35) (capacity : first.val+active.val≤choices.length)
    (digits : ∀ t<choices.length, choices.val[t]!.val<2^p.a.val)
    (cv : chunks.val=2^(j.val-sub.val)) (space : start.val+active.val*chunks.val≤slots.length)
    (published : ∀ c : U32, c.val<chunks.val → ∀ rows, ParallelForsTicket.split_ticket sk seed addr choices p.a
      first active height low c start chunks = ok rows → ∀ l<active.val, slots.val[rows.val[l]!.1.val]! = some rows.val[l]!.2) :
    ChunkCells p (bytes sk.val) seed addr choices (first.val+lane) j sub (start.val+lane*chunks.val) slots := by
  intro c hc
  have depth : p.a.val≤14 := hp.valid.a_le
  obtain ⟨hj,hs⟩ := defs
  have small := Nat.pow_le_pow_right (by decide : 0<2) (show j.val-sub.val≤14 by omega)
  let k := U32.ofNatCore c (by scalar_tac)
  have kv : k.val=c := U32.ofNatCore_val_eq ..
  have limit := slots.len_ineq
  change slots.length≤Usize.max at limit
  obtain ⟨rows,run,vals⟩ := spec_imp_exists (ParallelForsTicket.split_ticket_spec p hp sk seed addr choices first active height low k start chunks
    domain depth field count (by omega) width capacity digits lower (by rwa [←hj,←hs]) (by omega) (by omega))
  obtain ⟨dest,value⟩ := vals lane hl
  have cell := published k (by omega) rows run lane hl
  refine ⟨rows.val[lane]!.2,?_,?_⟩
  · rwa [dest,kv] at cell
  · simpa only [←hj,←hs,kv,cv] using value
end slhdsa.ForsMetadata

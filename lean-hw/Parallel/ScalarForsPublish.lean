import Parallel.ScalarForsGeometry
import Parallel.ScalarForsHosted

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelScalarFors

abbrev Action (N : Usize) := U32 → U32 → Usize → Result (Usize × Array U8 N)

def run {N : Usize} (act : Action N) (record : Result (U32 × U32 × Usize)) :=
  Std.bind record (fun data => act data.1 data.2.1 data.2.2)

def Law {N : Usize} (act : Action N) (p : params.Params) (sk seed : Array U8 N) (a : address.Adrs) :=
  ∀ (i z : U32) (slot : Usize), z.val≤14 → (i.val+1)*2^z.val≤1048576 →
    act i z slot ⦃ w => Writes slot (Spec.forsNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a)) w ⦄

inductive Platform where
  | apple (sha3 : Bool)
  | linux
  | x86

noncomputable def actions {N : Usize} (host : Platform) (p : params.Params)
    (sk seed : Array U8 N) (a : address.Adrs) : Action N × Action N :=
  match host with
  | .apple sha3 =>
    let h := wide (.apple sha3) p
    (@ScalarTicketApple.slhdsa.ParallelScalarFors.direct_node_ticket h N sk seed a,
     @ScalarTicketApple.slhdsa.ParallelScalarFors.split_node_ticket h N sk seed a)
  | .x86 =>
    let h := wide .x86 p
    (@ScalarTicketX86.slhdsa.ParallelScalarFors.direct_node_ticket h N sk seed a,
     @ScalarTicketX86.slhdsa.ParallelScalarFors.split_node_ticket h N sk seed a)
  | .linux =>
    (@ScalarTicketLinux.slhdsa.ParallelScalarFors.direct_node_ticket narrow N sk seed a,
     @ScalarTicketLinux.slhdsa.ParallelScalarFors.split_node_ticket narrow N sk seed a)

theorem native_laws {N : Usize} (host : Platform) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (domain : ForsHorizontal.Domain a) :
    Law (actions host p sk seed a).1 p sk seed a ∧ Law (actions host p sk seed a).2 p sk seed a := by
  cases host with
  | apple sha3 =>
    constructor <;> intro i z slot hi room
    · exact (ScalarTicketApple.slhdsa.ParallelScalarFors.wide_tickets (.apple sha3) p hp sk seed a domain i z slot hi room).1
    · exact (ScalarTicketApple.slhdsa.ParallelScalarFors.wide_tickets (.apple sha3) p hp sk seed a domain i z slot hi room).2
  | x86 =>
    constructor <;> intro i z slot hi room
    · exact (ScalarTicketX86.slhdsa.ParallelScalarFors.wide_tickets .x86 p hp sk seed a domain i z slot hi room).1
    · exact (ScalarTicketX86.slhdsa.ParallelScalarFors.wide_tickets .x86 p hp sk seed a domain i z slot hi room).2
  | linux =>
    constructor <;> intro i z slot hi room
    · exact (ScalarTicketLinux.slhdsa.ParallelScalarFors.narrow_tickets p hp sk seed a i z slot hi room).1
    · exact (ScalarTicketLinux.slhdsa.ParallelScalarFors.narrow_tickets p hp sk seed a i z slot hi room).2

theorem direct_published {N : Usize} (host : Platform) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (domain : ForsHorizontal.Domain a)
    (t h j digit : U32) (tree : t.val<35) (height : h.val≤14) (below : j.val<h.val) (selected : digit.val<2^h.val) :
    run (actions host p sk seed a).1 (prepare_direct t h j digit) ⦃ w =>
      w.1.val=t.val*(h.val+1)+1+j.val ∧ bytes w.2.val=Spec.forsNode (Shake.params p) (bytes sk.val)
        (sibling t.val h.val j.val digit.val) j.val (bytes seed.val) (adrsS a) ⦄ := by
  obtain ⟨⟨i,z,slot⟩,rec,idx,level,pos⟩ := spec_imp_exists (direct_geometry t h j digit tree height below selected)
  unfold run
  rw [rec]
  simp only [bind_ok]
  have fit := sibling_room _ _ _ _ tree height below selected
  obtain ⟨out,call,cell,hash⟩ := spec_imp_exists ((native_laws host p hp sk seed a domain).1 i z slot
    (by rw [level];omega) (by rwa [idx,level]))
  rw [call];simp [cell,pos,hash,idx,level]

theorem split_published {N : Usize} (host : Platform) (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (domain : ForsHorizontal.Domain a) (sat : Bool)
    (t h j digit sub : U32) (start chunk : Usize) (tree : t.val<35) (height : h.val≤14) (below : j.val<h.val)
    (selected : digit.val<2^h.val) (lower : sub.val<j.val) (part : chunk.val<2^(j.val-sub.val))
    (slots : start.val+chunk.val≤Usize.max) :
    run (actions host p sk seed a).2 ((if sat then prepare_saturating else prepare_split) t h j digit sub start chunk)
      ⦃ w => w.1.val=start.val+chunk.val ∧ bytes w.2.val=Spec.forsNode (Shake.params p) (bytes sk.val)
        (sibling t.val h.val j.val digit.val*2^(j.val-sub.val)+chunk.val) sub.val (bytes seed.val) (adrsS a) ⦄ := by
  obtain ⟨⟨i,z,slot⟩,rec,idx,level,pos⟩ := spec_imp_exists (split_geometry t h j digit sub start chunk tree height below selected lower part slots)
  have eq : ((if sat then prepare_saturating else prepare_split) t h j digit sub start chunk) =
      prepare_split t h j digit sub start chunk := by cases sat <;> simp [saturating_eq _ _ _ _ _ _ _ lower.le]
  unfold run
  rw [eq,rec];simp only [bind_ok]
  have fit : (i.val+1)*2^z.val≤1048576 := by
    rw [idx,level]
    calc
      _ ≤ ((sibling t.val h.val j.val digit.val+1)*2^(j.val-sub.val))*2^sub.val :=
        Nat.mul_le_mul_right _ (by rw [Nat.add_mul,Nat.one_mul];omega)
      _ = _ := by rw [Nat.mul_assoc,←Nat.pow_add,Nat.sub_add_cancel lower.le]
      _ ≤ _ := sibling_room _ _ _ _ tree height below selected
  obtain ⟨out,call,cell,hash⟩ := spec_imp_exists ((native_laws host p hp sk seed a domain).2 i z slot (by rw [level];omega) fit)
  rw [call];simp [cell,pos,hash,idx,level]

end slhdsa.ParallelScalarFors

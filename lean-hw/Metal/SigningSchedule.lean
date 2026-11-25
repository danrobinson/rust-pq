import Metal.ForsDispatch

namespace MetalSigningSchedule
open Spec MetalChainDispatch MetalWotsOutput

private theorem grid_bounds {count words : Nat} {w : Lane} (h : w ∈ grid count words) :
    w.1 < count ∧ w.2 < words := by
  obtain ⟨r,hr,col⟩ := List.mem_flatMap.mp h
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp col
  exact ⟨List.mem_range.mp hr,List.mem_range.mp hc⟩

def coord (p : Params) (count : Nat) (hd : 0<p.d) (hc : 0<p.len)
    (w : { v : Lane // v ∈ grid (count*p.d*p.len) p.n }) : Coord p count :=
  let bound := grid_bounds w.property
  let row := w.val.1/p.len
  let rowBound : row < count*p.d := (Nat.div_lt_iff_lt_mul hc).2 bound.1
  ⟨⟨row/p.d,(Nat.div_lt_iff_lt_mul hd).2 rowBound⟩,⟨row%p.d,Nat.mod_lt _ hd⟩,
   ⟨w.val.1%p.len,Nat.mod_lt _ hc⟩,⟨w.val.2,bound.2⟩⟩

theorem lane_coord (p : Params) (count : Nat) (hd : 0<p.d) (hc : 0<p.len)
    (w : { v : Lane // v ∈ grid (count*p.d*p.len) p.n }) : lane (coord p count hd hc w) = w.val := by
  rcases w with ⟨⟨gid,i⟩,h⟩
  change (((gid/p.len/p.d*p.d+(gid/p.len)%p.d)*p.len+gid%p.len),i) = (gid,i)
  rw [Nat.div_add_mod' _ _,Nat.div_add_mod' _ _]

def wots (p : Params) (count : Nat) (hd : 0<p.d) (hc : 0<p.len) :=
  (grid (count*p.d*p.len) p.n).attach.map (coord p count hd hc)

theorem wots_order (p : Params) (count : Nat) (hd : 0<p.d) (hc : 0<p.len) :
    ((wots p count hd hc).map lane).Perm (grid (count*p.d*p.len) p.n) := by
  simp only [wots,List.map_map,Function.comp_def,lane_coord]
  rw [List.attach_map_subtype_val]

def execution (count words : Nat) (initial : Memory) : Execution :=
  ⟨fun _ => ([],[]),fun _ => ⟨0,0,0,none,0⟩,initial,grid count words⟩

end MetalSigningSchedule

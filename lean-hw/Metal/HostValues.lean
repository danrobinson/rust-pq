import Metal.ForsPkDispatch
import Mathlib.Data.List.Basic

namespace MetalHostValues
open Spec MetalPipeline MetalChainDispatch MetalCommand MetalCommandValues
open MetalWotsOutput (Context context)

def pair (p : Params) (r : BatchSignReq) := (block p r.sk 0, block p r.sk 2)
/-- The loop appends a slot only when position() misses. Already assigned slot
indices are stable as later requests extend the table. -/
def insertPair (slots : List (Bytes × Bytes)) (key : Bytes × Bytes) :=
  if key ∈ slots then slots else slots ++ [key]

theorem table_prefix (slots todo : List (Bytes × Bytes)) : slots <+: todo.foldl insertPair slots := by
  induction todo generalizing slots with
  | nil => exact ⟨[],by simp⟩
  | cons key rest ih =>
    have step : slots <+: insertPair slots key := by
      unfold insertPair; split
      · exact ⟨[],by simp⟩
      · exact ⟨[key],rfl⟩
    exact step.trans (ih _)

theorem table_contains (slots todo : List (Bytes × Bytes)) (key : Bytes × Bytes) (hk : key ∈ todo) :
    key ∈ todo.foldl insertPair slots := by
  induction todo generalizing slots with
  | nil => simp at hk
  | cons first rest ih =>
    rcases List.mem_cons.mp hk with same | later
    · subst first
      apply (table_prefix (insertPair slots key) rest).mem
      by_cases h : key ∈ slots <;> simp [insertPair,h]
    · exact ih _ later

theorem saved_index (slots rest : List (Bytes × Bytes)) (key : Bytes × Bytes) :
    (rest.foldl insertPair (insertPair slots key)).idxOf key = slots.idxOf key := by
  have inside : key ∈ insertPair slots key := by by_cases h : key ∈ slots <;> simp [insertPair,h]
  rw [← (table_prefix (insertPair slots key) rest).idxOf_eq_of_mem inside]
  by_cases seen : key ∈ slots
  · simp [insertPair,seen]
  · simp [insertPair,seen,List.idxOf_append]

def table (p : Params) (rs : List BatchSignReq) := (rs.map (pair p)).foldl insertPair []
def keyIndex (p : Params) (rs : List BatchSignReq) (r : BatchSignReq) := (table p rs).idxOf (pair p r)
def keys (p : Params) (rs : List BatchSignReq) : Keys := fun i => (table p rs)[i]!

theorem key_selected (p : Params) (rs : List BatchSignReq) (s : Fin rs.length) :
    keys p rs (keyIndex p rs rs[s]) = ((context p rs[s]).sk, (context p rs[s]).pk) := by
  have present : pair p rs[s] ∈ table p rs := by
    apply table_contains
    exact List.mem_map.mpr ⟨_,List.getElem_mem _,rfl⟩
  unfold keys keyIndex
  rw [List.getElem!_eq_getElem?_getD,List.getElem?_idxOf present]
  rfl

def index (p : Params) (rs : List BatchSignReq) (sig : Nat) := keyIndex p rs rs[sig]!
def job (p : Params) (rs : List BatchSignReq) (sig : Nat) : MetalForsPkDispatch.Job :=
  let x := context p rs[sig]!
  ⟨x.tree,x.leaf,index p rs sig⟩
def layer (p : Params) (rs : List BatchSignReq) (row : Nat) : MetalWotsOutput.Desc :=
  let sig := row / p.d
  let j := row % p.d
  let x := context p rs[sig]!
  let location := MetalWotsOutput.loc p x j
  ⟨sig,j,location.1,location.2,index p rs sig,
    sig*p.sigBytes+(p.n+p.forsSigBytes+j*p.xmssSigBytes)⟩
def trees (p : Params) (rs : List BatchSignReq) : Trees := fun row =>
  let d := layer p rs row
  ⟨d.tree,d.key,d.layer,some d.pair,d.outBase+p.len*p.n⟩

theorem layer_at (p : Params) (rs : List BatchSignReq) (s : Fin rs.length) (j : Fin p.d) :
    layer p rs (s.val*p.d+j.val) =
      ⟨s.val,j.val,(MetalWotsOutput.loc p (context p rs[s]) j).1,
       (MetalWotsOutput.loc p (context p rs[s]) j).2,keyIndex p rs rs[s],
       s.val*p.sigBytes+(p.n+p.forsSigBytes+j.val*p.xmssSigBytes)⟩ := by
  obtain ⟨sig,digit⟩ := decode s.val j.val p.d j.isLt
  simp only [layer,index,sig,digit,getElem!_pos rs s.val s.isLt,Fin.getElem_fin]

theorem jobs_spec (p : Params) (rs : List BatchSignReq) :
    MetalForsPkDispatch.Jobs p rs (keys p rs) (job p rs) := by
  intro s
  simp only [job,index,getElem!_pos rs s.val s.isLt,Fin.getElem_fin]
  exact ⟨trivial,trivial,congrArg Prod.snd (key_selected p rs s)⟩

theorem layers_spec (p : Params) (rs : List BatchSignReq) (inputs : MetalWotsOutput.Inputs)
    (packed : inputs.desc = layer p rs) :
    MetalWotsOutput.Descriptors p rs inputs (keys p rs) := by
  intro s j
  simp only [packed,layer_at p rs s j]
  exact ⟨trivial,trivial,trivial,trivial,key_selected p rs s,trivial⟩

def rand (p : Params) (r : BatchSignReq) := PRFmsg p (block p r.sk 1) r.addrnd r.msg

theorem rand_byte (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (s : Fin rs.length) (i : Fin p.n) :
    (metalBatchSignInternal mode p rs).flatten[s.val*p.sigBytes+i.val]? = (rand p rs[s])[i.val]? := by
  have len := sigBytes_parts p hv
  have fits : i.val < p.sigBytes := by have := i.isLt; omega
  rw [metal_batch_sign_internal_eq_fips mode p hv,MetalWotsOutput.batchByte _ _ _
    (fun _ => slhSignInternal_length p hv _ _ _) s _ fits]
  simp only [slhSignInternal,rand]
  rw [List.getElem?_append_left (by rw [List.length_append, PRFmsg_length p hv]; have := i.isLt; omega),
    List.getElem?_append_left (by rw [PRFmsg_length p hv]; exact i.isLt)]

/-- A later source-checked scatter preserves every address outside its writes. -/
theorem preserve {α : Type} (site : α → Nat) (value : α → Spec.Byte) (schedule : List α)
    (mem : Nat → Spec.Byte) (pos : Nat) (separate : ∀ w ∈ schedule, pos ≠ site w) :
    MetalWotsOutput.execute site value schedule mem pos = mem pos := by
  induction schedule generalizing mem with
  | nil => rfl
  | cons w ws ih =>
    change MetalWotsOutput.execute site value ws (fun a => if a=site w then value w else mem a) pos = _
    rw [ih _ (fun x hx => separate x (by simp [hx]))]
    simp [separate w (by simp)]

abbrev RandCoord (p : Params) (count : Nat) := Fin count × Fin p.n
def randAddr {p count} (w : RandCoord p count) := w.1.val*p.sigBytes+w.2.val
def randLayout (g : MetalSignatureLayout.Geometry) {count} (s : Fin count) (i : Fin g.n) :
    MetalSignatureLayout.Byte g count := ⟨s,.inl 0,i⟩

theorem rand_site {p n} (hv : p.Valid) : Function.Injective (@randAddr p n) := by
  intro u v h
  have fits (w : RandCoord p n) : w.2.val < p.sigBytes := by
    have := w.2.isLt; have := sigBytes_parts p hv; omega
  have du := decode u.1.val u.2.val p.sigBytes (fits u)
  have dv := decode v.1.val v.2.val p.sigBytes (fits v)
  unfold randAddr at h; rw [h] at du
  exact Prod.ext (Fin.ext (du.1.symm.trans dv.1)) (Fin.ext (du.2.symm.trans dv.2))

def initMemory (p : Params) (rs : List BatchSignReq) (initial : Nat → Spec.Byte) : Nat → Spec.Byte :=
  let stores := (List.finRange rs.length).flatMap (fun s => (List.finRange p.n).map fun i => (s,i))
  MetalWotsOutput.execute randAddr (fun w : RandCoord p rs.length => (rand p rs[w.1])[w.2.val]!) stores initial

theorem init_byte (p : Params) (hv : p.Valid) (rs : List BatchSignReq) (initial : Nat → Spec.Byte)
    (s : Fin rs.length) (i : Fin p.n) : initMemory p rs initial (randAddr (s,i)) = (rand p rs[s])[i.val]! := by
  unfold initMemory
  rw [MetalWotsOutput.scatter_byte _ (rand_site hv)]
  simp

/-- Events from FORS and XMSS signature stores between host initialization and
the final WOTS dispatch. The source-bound address layout gives each such event
its own signature node. Values are unconstrained here, and proved separately by
the commands responsible for each region. -/
structure Middle (g : MetalSignatureLayout.Geometry) (n : Nat) where
  field : MetalSignatureLayout.Byte g n
  foreign : owner g field.2.1 ≠ .randomizer
  byte : Spec.Byte

def afterMiddle {g n} (events : List (Middle g n)) (initial : Nat → Spec.Byte) :=
  MetalWotsOutput.execute (fun w : Middle g n => MetalSignatureLayout.address g w.field) Middle.byte events initial

theorem middle_keeps_randomizer {g n} (events : List (Middle g n)) (initial : Nat → Spec.Byte)
    (s : Fin n) (i : Fin g.n) :
    afterMiddle events initial (MetalSignatureLayout.address g (randLayout g s i)) =
      initial (MetalSignatureLayout.address g (randLayout g s i)) := by
  apply preserve
  intro w _ eq
  have clash := MetalSignatureLayout.disjoint g n eq
  exact w.foreign (by rw [← clash]; rfl)

theorem wots_keeps_randomizer (p : Params) (hv : p.Valid) (n : Nat)
    (w : MetalWotsOutput.Coord p n) (s : Fin n) (i : Fin p.n) :
    randAddr (s,i) ≠ MetalWotsOutput.addr w := by
  intro eq
  have fits : i.val < p.sigBytes := by have := i.isLt; have := sigBytes_parts p hv; omega
  have dr := decode s.val i.val p.sigBytes fits
  have dw := decode w.sig.val (MetalWotsOutput.offset p w.j w.c w.i) p.sigBytes
    (MetalWotsOutput.offset_bound p hv _ _ _ w.j.isLt w.c.isLt w.i.isLt)
  change s.val*p.sigBytes+i.val = _ at eq
  unfold MetalWotsOutput.addr at eq
  rw [eq] at dr
  have lo := dr.2.symm.trans dw.2
  unfold MetalWotsOutput.offset at lo
  have := i.isLt; omega

def initialized {p : Params} (rs : List BatchSignReq) (e : Execution) : Execution :=
  { e with keys := keys p rs, trees := trees p rs }

theorem final_randomizer (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (g : MetalSignatureLayout.Geometry) (width : g.n = p.n) (stride : MetalSignatureLayout.signatureBytes g = p.sigBytes)
    (events : List (Middle g rs.length)) (atByte : MetalWotsOutput.Coord p rs.length → Nat)
    (value : MetalWotsOutput.Coord p rs.length → Spec.Byte) (footprint : ∀ w, atByte w = MetalWotsOutput.addr w)
    (schedule : List (MetalWotsOutput.Coord p rs.length)) (memory : Nat → Spec.Byte) (capacity : Nat)
    (alloc : rs.length*p.sigBytes ≤ capacity) (scratch : Region → Prop) (scratchR : scratch .randomizer) :
    let initial := afterMiddle events (initMemory p rs memory)
    let pool := MetalWotsOutput.pool atByte value schedule initial capacity
    correct g rs.length (pool.take (rs.length*p.sigBytes)) (metalBatchSignInternal mode p rs).flatten scratch .randomizer := by
  intro initial pool
  refine ⟨scratchR, ?_⟩
  rintro ⟨s,b,i⟩ own
  rcases b with z | ⟨t, z | (l | a)⟩ | ⟨j, c | a⟩ <;> cases own
  have zr : z = 0 := Subsingleton.elim _ _
  subst z
  let pos := MetalSignatureLayout.address g (randLayout g s i)
  let ix := Fin.cast width i
  have addr : pos = @randAddr p rs.length (s,ix) := by simp [pos,randLayout,MetalSignatureLayout.address,randAddr,ix,stride]
  have bound : pos < rs.length*p.sigBytes := by rw [← stride]; exact MetalSignatureLayout.in_bounds g (randLayout g s i)
  change (pool.take _)[pos]? = _
  rw [List.getElem?_take_of_lt bound]
  change (List.ofFn _)[pos]? = _
  rw [List.getElem?_ofFn,dite_eq_left (by omega)]
  change some (MetalWotsOutput.execute atByte value schedule initial pos) = _
  rw [preserve _ _ _ _ pos (fun w _ => by rw [footprint,addr]; exact wots_keeps_randomizer p hv _ w s ix)]
  rw [show initial pos = initMemory p rs memory pos from middle_keeps_randomizer events _ s i,
    addr,init_byte p hv]
  change _ = (metalBatchSignInternal mode p rs).flatten[pos]?
  rw [addr]
  change _ = (metalBatchSignInternal mode p rs).flatten[s.val*p.sigBytes+ix.val]?
  rw [rand_byte p hv mode rs s ix]
  have fits : ix.val < (rand p rs[s]).length := by rw [rand,PRFmsg_length p hv]; exact ix.isLt
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem fits,Option.getD_some]

theorem host_rule (cmd : Access) (writes : cmd.writes =
    [.keys,.xmss_trees,.fors_jobs,.wots_layers,.randomizer])
    (g : MetalSignatureLayout.Geometry) (count : Nat) (out expected : Bytes) (inv : Region → Prop)
    (k : inv .keys) (trees : inv .xmss_trees) (jobs : inv .fors_jobs)
    (layers : inv .wots_layers) (rand : correct g count out expected inv .randomizer) :
    (∀ r ∈ cmd.reads, correct g count out expected inv r) →
    ∀ r ∈ cmd.writes, correct g count out expected inv r := by
  intro _ r hr
  rw [writes] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact rand | constructor
  all_goals
    first
    | assumption
    | rintro ⟨_, node, _⟩ own
      rcases node with x | ⟨t, s | (l | h')⟩ | ⟨d, c | a⟩ <;> cases own

end MetalHostValues

import Metal.LeafDispatch
import Armwide.Encoders
import Mathlib.Tactic.IntervalCases
import Std.Tactic.BVDecide

namespace MetalWotsOutput
open Spec MetalPipeline MetalCommandValues MetalCommand MetalSignatureLayout

structure Context where
  sk : Bytes
  pk : Bytes
  tree : Nat
  leaf : Nat
  pkFors : Bytes
  prefixBytes : Bytes

def context (p : Params) (r : BatchSignReq) : Context :=
  let sk := block p r.sk 0
  let pk := block p r.sk 2
  let rand := PRFmsg p (block p r.sk 1) r.addrnd r.msg
  let digest := Hmsg p rand pk (block p r.sk 3) r.msg
  let md := digest.take p.mdBytes
  let t := digestTree p digest
  let l := digestLeaf p digest
  let adrs := { { Adrs.zero with tree := t }.setTypeAndClear FORS_TREE with keypair := l }
  let sig := forsSign p md sk pk adrs
  ⟨sk, pk, t, l, forsPkFromSig p sig md pk adrs, rand ++ sig⟩

def loc (p : Params) (x : Context) (j : Nat) := htLoc p.hp x.tree x.leaf j
def adrs (p : Params) (x : Context) (j : Nat) : Adrs :=
  { Adrs.zero with layer := j, tree := (loc p x j).1 }
def root (p : Params) (x : Context) (j : Nat) := xmssNode p x.sk 0 p.hp x.pk (adrs p x j)
def msg (p : Params) (x : Context) (j : Nat) := metalLayerMsg x.pkFors (root p x) j
def layer (p : Params) (x : Context) (j : Nat) :=
  xmssSign p (msg p x j) x.sk (loc p x j).2 x.pk (adrs p x j)
def node (p : Params) (x : Context) (j c : Nat) :=
  metalWotsSignChain p x.sk x.pk (msg p x j) j (loc p x j).1 (loc p x j).2 c
def offset (p : Params) (j c i : Nat) :=
  p.n + p.forsSigBytes + j*p.xmssSigBytes + c*p.n + i

theorem flatByte (f : Nat → Bytes) (width count i j : Nat) (hlen : ∀ k, (f k).length = width)
    (hi : i < count) (hj : j < width) :
    ((List.range count).flatMap f)[i * width + j]? = (f i)[j]? := by
  have piece := flatMap_piece f width hlen count i j 1 hi (by omega)
  have eq := congrArg (fun xs : Bytes => xs[0]?) piece
  simp only [List.getElem?_take, show 0 < 1 by decide, ↓reduceIte, List.getElem?_drop, Nat.add_zero] at eq
  exact eq

theorem chain_length (p : Params) (hv : p.Valid) (x : Context) (j c : Nat) :
    (node p x j c).length = p.n := by
  unfold node metalWotsSignChain metalRunWotsChain
  exact Spec.chain_length p hv _ (PRF_length p hv _ _ _) _ _ _ _

theorem byteBound (p : Params) (c i : Nat) (hc : c < p.len) (hi : i < p.n) :
    c * p.n + i < p.xmssSigBytes := by
  have w := active c i p.n p.len hc hi
  simp only [Params.xmssSigBytes, Nat.add_mul]
  omega

theorem layer_byte (p : Params) (hv : p.Valid) (x : Context) (j c i : Nat)
    (hc : c < p.len) (hi : i < p.n) :
    (layer p x j)[c * p.n + i]? = (node p x j c)[i]? := by
  unfold layer xmssSign
  rw [List.getElem?_append_left (by rw [wotsSign_length p hv]; exact active c i _ _ hc hi)]
  apply Eq.trans (congrArg (fun xs : Bytes => xs[c*p.n+i]?)
    (metal_wots_sign_eq_fips p x.sk x.pk (msg p x j) j (loc p x j).1 (loc p x j).2).symm)
  exact flatByte (node p x j) _ _ _ _ (chain_length p hv x j) hc hi

theorem signature_byte (p : Params) (hv : p.Valid) (r : BatchSignReq) (j c i : Nat)
    (hj : j < p.d) (hc : c < p.len) (hi : i < p.n) :
    (slhSignInternal p r.msg r.sk r.addrnd)[offset p j c i]? = (node p (context p r) j c)[i]? := by
  let x := context p r
  have prefixLen : x.prefixBytes.length = p.n + p.forsSigBytes := by
    simp only [x, context, List.length_append, PRFmsg_length p hv, forsSign_length p hv]
  have leafBound : x.leaf < 2^p.hp := digestLeaf_lt p hv _
  have layers : (List.range p.d).flatMap (layer p x) = htSign p x.pkFors x.sk x.pk x.tree x.leaf :=
    ht_layers_eq_spec p hv _ _ _ _ _ leafBound
  change (x.prefixBytes ++ htSign p x.pkFors x.sk x.pk x.tree x.leaf)[_]? = _
  rw [← layers, List.getElem?_append_right (by unfold offset; omega)]
  rw [prefixLen, show offset p j c i - (p.n + p.forsSigBytes) = j*p.xmssSigBytes + (c*p.n+i) by
    unfold offset; omega]
  rw [flatByte (layer p x) _ _ _ _ (fun _ => xmssSign_length p hv _ _ _ _ _) hj (byteBound _ _ _ hc hi)]
  exact layer_byte p hv x j c i hc hi

/-- Selecting a batch element does not depend on preceding signatures' values. -/
theorem batchByte (rs : List α) (f : α → Bytes) (width : Nat)
    (len : ∀ r, (f r).length = width) (s : Fin rs.length) (offset : Nat) (within : offset < width) :
    (rs.map f).flatten[s.val*width+offset]? = (f rs[s])[offset]? := by
  induction rs with
  | nil => exact Fin.elim0 s
  | cons r rs ih =>
    refine Fin.cases ?_ (fun t => ?_) s
    · simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add, List.map_cons, List.flatten_cons,
        List.getElem?_append_left (show offset < (f r).length by rw [len]; exact within)]
      rfl
    · simp only [List.map_cons, List.flatten_cons, Fin.val_succ, Nat.succ_mul]
      rw [List.getElem?_append_right (by rw [len]; omega), len,
        show t.val*width+width+offset-width=t.val*width+offset by omega, ih t]
      rfl

theorem offset_bound (p : Params) (hv : p.Valid) (j c i : Nat)
    (hj : j < p.d) (hc : c < p.len) (hi : i < p.n) : offset p j c i < p.sigBytes := by
  have h := active j (c*p.n+i) p.xmssSigBytes p.d hj (byteBound p c i hc hi)
  have hlen := sigBytes_parts p hv
  unfold offset; omega

theorem batch_wots_byte (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (s : Fin rs.length) (j c i : Nat) (hj : j < p.d) (hc : c < p.len) (hi : i < p.n) :
    (metalBatchSignInternal mode p rs).flatten[s.val*p.sigBytes+offset p j c i]? =
      (node p (context p rs[s]) j c)[i]? := by
  rw [metal_batch_sign_internal_eq_fips mode p hv, batchByte _ _ _ (fun _ =>
    slhSignInternal_length p hv _ _ _) s _ (offset_bound p hv _ _ _ hj hc hi)]
  exact signature_byte p hv _ _ _ _ hj hc hi

structure Coord (p : Params) (count : Nat) where
  sig : Fin count
  j : Fin p.d
  c : Fin p.len
  i : Fin p.n
  deriving DecidableEq

def row {p n} (w : Coord p n) := w.sig.val * p.d + w.j.val
def gid {p n} (w : Coord p n) := row w * p.len + w.c.val
def addr {p n} (w : Coord p n) := w.sig.val*p.sigBytes+offset p w.j w.c w.i

private theorem fields {a b i j w : Nat} (hi : i < w) (hj : j < w)
    (eq : a*w+i = b*w+j) : a=b ∧ i=j := by
  have h := decode a i w hi
  rw [eq] at h
  have k := decode b j w hj
  exact ⟨h.1.symm.trans k.1,h.2.symm.trans k.2⟩

def lane {p n} (w : Coord p n) : MetalChainDispatch.Lane := (gid w,w.i.val)

theorem active_id {p n} (w : Coord p n) : gid w < (n*p.d)*p.len :=
  active _ _ _ _ (active _ _ _ _ w.sig.isLt w.j.isLt) w.c.isLt

theorem unique_lane {p n} : Function.Injective (@lane p n) := by
  rintro ⟨s,j,c,i⟩ ⟨t,k,d,b⟩ eq
  obtain ⟨hg,hi⟩ := Prod.ext_iff.mp eq
  obtain ⟨hr,hc⟩ := fields c.isLt d.isLt hg
  obtain ⟨hs,hj⟩ := fields j.isLt k.isLt hr
  cases Fin.ext hs; cases Fin.ext hj; cases Fin.ext hc; cases Fin.ext hi; rfl

theorem covered {p n} (schedule : List (Coord p n))
    (order : (schedule.map lane).Perm (MetalChainDispatch.grid (n*p.d*p.len) p.n)) :
    ∀ w, w ∈ schedule := by
  intro w
  have member := MetalChainDispatch.covers_grid order (gid w) (active_id w) w.i.val w.i.isLt
  rcases List.mem_map.mp member with ⟨a, ha, eq⟩
  exact (show a = w from unique_lane eq) ▸ ha

theorem unique_addr (p : Params) (hv : p.Valid) (n : Nat) : Function.Injective (@addr p n) := by
  rintro ⟨s,j,c,i⟩ ⟨t,k,d,b⟩ eq
  obtain ⟨hs,ho⟩ := fields (offset_bound p hv _ _ _ j.isLt c.isLt i.isLt)
    (offset_bound p hv _ _ _ k.isLt d.isLt b.isLt) eq
  dsimp only [offset] at ho
  have nested : j.val*p.xmssSigBytes+(c.val*p.n+i.val)=k.val*p.xmssSigBytes+(d.val*p.n+b.val) := by omega
  obtain ⟨hj,hc⟩ := fields (byteBound p _ _ c.isLt i.isLt) (byteBound p _ _ d.isLt b.isLt) nested
  obtain ⟨hc,hi⟩ := fields i.isLt b.isLt hc
  cases Fin.ext hs; cases Fin.ext hj; cases Fin.ext hc; cases Fin.ext hi; rfl

/-- Generic scatter of signature bytes from an arbitrary active-lane schedule. -/
def execute {α : Type} (whereAt : α → Nat) (value : α → Spec.Byte)
    (schedule : List α) (initial : Nat → Spec.Byte) : Nat → Spec.Byte :=
  schedule.foldl (fun mem w a => if a = whereAt w then value w else mem a) initial

theorem scatter_byte {α : Type} [DecidableEq α] (whereAt : α → Nat)
    (injective : Function.Injective whereAt) (value : α → Spec.Byte)
    (schedule : List α) (mem : Nat → Spec.Byte) (w : α) :
    execute whereAt value schedule mem (whereAt w) =
      if w ∈ schedule then value w else mem (whereAt w) := by
  induction schedule generalizing mem with
  | nil => simp [execute]
  | cons x xs ih =>
    change execute whereAt value xs (fun a => if a = whereAt x then value x else mem a) (whereAt w) = _
    rw [ih]
    by_cases hx : w ∈ xs <;> by_cases eq : w = x <;> simp [hx, eq, injective.eq_iff]

structure Desc where
  sig : Nat
  layer : Nat
  tree : Nat
  pair : Nat
  key : Nat
  outBase : Nat

structure Inputs where
  desc : Nat → Desc
  keys : MetalChainDispatch.Keys
  fors : Nat → Bytes
  roots : Nat → Bytes

def shaderAddr {p n} (inputs : Inputs) (w : Coord p n) :=
  (inputs.desc (gid w / p.len)).outBase + (gid w % p.len)*p.n + w.i.val

def checksum (ds : List Nat) := ds.foldl (fun sum d => sum + (15-d)) 0

def nativeDigits (m : Bytes) : List Nat :=
  let ds := slhdsa.Armwide.nibbles m
  let sum := checksum ds
  ds ++ [(sum >>> 8) &&& 15, (sum >>> 4) &&& 15, sum &&& 15]

private theorem sum_bound (ds : List Nat) (initial : Nat) :
    ds.foldl (fun sum d => sum + (15-d)) initial ≤ initial + 15*ds.length := by
  induction ds generalizing initial with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons,List.length_cons,Nat.mul_succ]
    have h := ih (initial+(15-d)); omega

theorem nativeDigits_eq (p : Params) (hv : p.Valid) (m : Bytes) (size : m.length = p.n) :
    nativeDigits m = wotsDigits p m := by
  obtain ⟨hw,h1,h2,_⟩ := valid_wots_params hv
  have nibble := slhdsa.Armwide.base2b_4_eq_nibbles m
  rw [size] at nibble
  have hlen : (slhdsa.Armwide.nibbles m).length = 2 * p.n := by
    rw [← nibble,base2b_length]
  have bound : checksum (slhdsa.Armwide.nibbles m) < 4096 := by
    unfold checksum
    have h := sum_bound (slhdsa.Armwide.nibbles m) 0
    rw [hlen] at h
    rcases hv.n_cases with a|a|a <;> omega
  simp only [nativeDigits,wotsDigits,h1,h2,hw,hv.lgw_eq,nibble]
  change _ = _ ++ base2b (toByte (checksum (slhdsa.Armwide.nibbles m) <<< 4) 2) 4 3
  rw [slhdsa.Armwide.base2b_checksum3 _ bound]

def digitAt (m : Bytes) (c : Nat) : Nat :=
  let ds := slhdsa.Armwide.nibbles m
  if c < ds.length then ds[c]! else (checksum ds >>> (8 - 4 * (c - ds.length))) &&& 15

theorem digitAt_eq (p : Params) (hv : p.Valid) (m : Bytes) (size : m.length = p.n)
    (c : Fin p.len) : digitAt m c = (wotsDigits p m)[c.val]! := by
  rw [← nativeDigits_eq p hv m size]
  let ds := slhdsa.Armwide.nibbles m
  have hlen : ds.length = 2*p.n := by
    rw [show ds = base2b m 4 (2*m.length) from (slhdsa.Armwide.base2b_4_eq_nibbles m).symm,
      base2b_length, size]
  change (if c.val < ds.length then ds[c.val]! else _) = (ds ++ _)[c.val]!
  by_cases before : c.val < ds.length
  · simp only [before, ↓reduceIte, List.getElem!_eq_getElem?_getD, List.getElem?_append_left before]
  · have len := (valid_wots_params hv).2.2.2
    have hc := c.isLt
    have three : c.val - ds.length = 0 ∨ c.val - ds.length = 1 ∨ c.val - ds.length = 2 := by omega
    simp only [before, ↓reduceIte, List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega : ds.length ≤ c.val)]
    change (checksum ds >>> (8 - 4 * (c.val - ds.length))) &&& 15 =
      ([(checksum ds >>> 8) &&& 15,(checksum ds >>> 4) &&& 15,checksum ds &&& 15][c.val-ds.length]?).getD _
    rcases three with a|a|a <;> rw [a] <;> rfl

theorem msg_length (p : Params) (hv : p.Valid) (r : BatchSignReq) (j : Nat) :
    (msg p (context p r) j).length = p.n := by
  cases j with
  | zero => exact T_length p hv _ _ _
  | succ j => exact xmssNode_length p hv _ _ _ _ _

def shaderNode (p : Params) (inputs : Inputs) (globalId : Nat) :=
  let c := globalId % p.len
  let d := inputs.desc (globalId / p.len)
  let k := inputs.keys d.key
  let m := if d.layer = 0 then inputs.fors d.sig else inputs.roots (d.sig*p.d + (d.layer-1))
  MetalChainDispatch.chainLoop p k.1 k.2 d.layer d.tree d.pair c (digitAt m c)

/-- Big-endian words for SHA-2 and little-endian lanes for SHAKE, followed by
the actual shift-and-cast done by store_be32 or store_le64. -/
def storeByte (shake : Bool) (bs : Bytes) (i : Nat) : Spec.Byte :=
  if shake then
    let b := fun k => bs[i/8*8+k]!
    let lane := b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0
    (lane >>> (8*(i%8))).setWidth 8
  else
    let b := fun k => bs[i/4*4+k]!
    let word := b 0 ++ b 1 ++ b 2 ++ b 3
    (word >>> (8*(3-i%4))).setWidth 8

theorem storeByte_eq (shake : Bool) (bs : Bytes) (i : Nat) : storeByte shake bs i = bs[i]! := by
  cases shake
  · have be (b : Nat → Spec.Byte) (k : Nat) (hk : k < 4) :
        ((b 0 ++ b 1 ++ b 2 ++ b 3) >>> (8*(3-k))).setWidth 8 = b k := by
      interval_cases k <;> bv_decide
    simp only [storeByte,Bool.false_eq_true,↓reduceIte]
    rw [be (fun k => bs[i/4*4+k]!) (i%4) (Nat.mod_lt _ (by decide))]
    congr 1
    omega
  · have le (b : Nat → Spec.Byte) (k : Nat) (hk : k < 8) :
        ((b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0) >>> (8*k)).setWidth 8 = b k := by
      interval_cases k <;> bv_decide
    simp only [storeByte,↓reduceIte]
    rw [le (fun k => bs[i/8*8+k]!) (i%8) (Nat.mod_lt _ (by decide))]
    congr 1
    omega

def shaderByte {p n} (inputs : Inputs) (w : Coord p n) : Spec.Byte :=
  (shaderNode p inputs (gid w))[w.i.val]!

/-- The descriptors may reuse a key slot for several requests. This relation
specifies the descriptor fields and meaning of the selected slot for each row. -/
def Descriptors (p : Params) (rs : List BatchSignReq) (inputs : Inputs) (keys : MetalChainDispatch.Keys) :=
  ∀ s : Fin rs.length, ∀ j : Fin p.d,
    let d := inputs.desc (s.val*p.d+j.val)
    let x := context p rs[s]
    d.sig = s.val ∧ d.layer = j.val ∧ d.tree = (loc p x j).1 ∧ d.pair = (loc p x j).2 ∧
    keys d.key = (x.sk,x.pk) ∧ d.outBase = s.val*p.sigBytes+(p.n+p.forsSigBytes+j.val*p.xmssSigBytes)

def ForsInputs (p : Params) (rs : List BatchSignReq) (inputs : Inputs) :=
  ∀ s : Fin rs.length, inputs.fors s.val = (context p rs[s]).pkFors

def RootInputs (p : Params) (rs : List BatchSignReq) (inputs : Inputs) :=
  ∀ s : Fin rs.length, ∀ j < p.d, inputs.roots (s.val*p.d+j) = root p (context p rs[s]) j

theorem shader_addr {p rs inputs keys} (desc : Descriptors p rs inputs keys) (w : Coord p rs.length) :
    shaderAddr inputs w = addr w := by
  obtain ⟨_,_,_,_,_,off⟩ := desc w.sig w.j
  obtain ⟨hr,hc⟩ := decode (row w) w.c.val p.len w.c.isLt
  unfold shaderAddr gid
  rw [hr, hc]
  dsimp [row] at *
  rw [off]; simp [addr, offset,Nat.add_assoc]

theorem shader_node {p rs inputs keys} (hv : p.Valid) (desc : Descriptors p rs inputs keys) (hk : inputs.keys = keys)
    (fors : ForsInputs p rs inputs) (roots : RootInputs p rs inputs) (w : Coord p rs.length) :
    shaderNode p inputs (gid w) = node p (context p rs[w.sig]) w.j w.c := by
  obtain ⟨hs,hl,ht,hp,hkey,_⟩ := desc w.sig w.j
  obtain ⟨hr,hc⟩ := decode (row w) w.c.val p.len w.c.isLt
  unfold shaderNode gid
  rw [hr,hc]
  dsimp only [row] at *
  simp only [hk,hkey,hs,hl,ht,hp,MetalChainDispatch.chainLoop_spec, node,metalWotsSignChain]
  congr 2
  have message : (if w.j.val = 0 then inputs.fors w.sig.val
      else inputs.roots (w.sig.val*p.d+(w.j.val-1))) = msg p (context p rs[w.sig]) w.j := by
    cases eq : w.j.val with
    | zero => simpa only [msg, metalLayerMsg, ↓reduceIte] using fors w.sig
    | succ k =>
      have hj := w.j.isLt
      simp [msg,metalLayerMsg,roots w.sig k (by omega)]
  rw [message, digitAt_eq p hv _ (msg_length p hv _ _) w.c]

/-- A physical signature pool may extend beyond the current batch prefix. -/
def pool {p count} (atByte : Coord p count → Nat) (byte : Coord p count → Spec.Byte)
    (schedule : List (Coord p count)) (initial : Nat → Spec.Byte) (capacity : Nat) : Bytes :=
  List.ofFn (fun i : Fin capacity => execute atByte byte schedule initial i.val)

def otherScratch (p : Params) (rs : List BatchSignReq) (inputs : Inputs)
    (keys : MetalChainDispatch.Keys) (rest : Region → Prop) : Region → Prop
  | .wots_layers => Descriptors p rs inputs keys
  | .pk_fors => ForsInputs p rs inputs
  | .xmss_roots => RootInputs p rs inputs
  | .wots => True
  | r => rest r

theorem wots_rule (p : Params) (hv : p.Valid) (rs : List BatchSignReq) (mode : XmssMode)
    (cmd : Access) (reads : cmd.reads = [.keys,.wots_layers,.pk_fors,.xmss_roots])
    (writes : cmd.writes = [.wots]) (inputs : Inputs) (keys : MetalChainDispatch.Keys)
    (atByte : Coord p rs.length → Nat) (byte : Coord p rs.length → Spec.Byte)
    (whereEq : ∀ w, atByte w = shaderAddr inputs w) (valueEq : ∀ w, byte w = shaderByte inputs w)
    (schedule : List (Coord p rs.length)) (cover : ∀ w, w ∈ schedule)
    (initial : Nat → Spec.Byte) (capacity : Nat) (alloc : rs.length*p.sigBytes ≤ capacity)
    (g : Geometry) (nEq : g.n = p.n) (dEq : g.d = p.d) (cEq : g.wots = p.len)
    (sigEq : signatureBytes g = p.sigBytes) (forsEq : forsBytes g = p.forsSigBytes)
    (xmssEq : xmssBytes g = p.xmssSigBytes)
    (scratch : Region → Prop) (key : scratch .keys → inputs.keys = keys)
    (desc : scratch .wots_layers → Descriptors p rs inputs keys)
    (fors : scratch .pk_fors → ForsInputs p rs inputs)
    (roots : scratch .xmss_roots → RootInputs p rs inputs) (written : scratch .wots) :
    let out := (pool atByte byte schedule initial capacity).take (rs.length*p.sigBytes)
    let pred := correct g rs.length out (metalBatchSignInternal mode p rs).flatten scratch
    (∀ r ∈ cmd.reads, pred r) → ∀ r ∈ cmd.writes, pred r := by
  intro out pred h r hr
  rw [writes, List.mem_singleton] at hr
  subst r
  have hk := key (h .keys (by simp [reads])).1
  have hd := desc (h .wots_layers (by simp [reads])).1
  have hf := fors (h .pk_fors (by simp [reads])).1
  have hm := roots (h .xmss_roots (by simp [reads])).1
  have ha : atByte = addr := funext fun w => (whereEq w).trans (shader_addr hd w)
  refine ⟨written, ?_⟩
  rintro ⟨s,b,i⟩ own
  rcases b with x | ⟨t, z | (l | a)⟩ | ⟨j, c | a⟩ <;> cases own
  let w : Coord p rs.length := ⟨s, Fin.cast dEq j, Fin.cast cEq c, Fin.cast nEq i⟩
  let coord : MetalSignatureLayout.Byte g rs.length := ⟨s,.inr (.inr (j,.inl c)),i⟩
  have pos : address g coord = addr w := by
    simp [coord,address,addr,w,offset,sigEq,forsEq,xmssEq,nEq,Nat.add_assoc]
  have bound : addr w < rs.length*p.sigBytes := by rw [← pos, ← sigEq]; exact in_bounds g coord
  change ((pool atByte byte schedule initial capacity).take _)[address g coord]? = _
  rw [pos, List.getElem?_take_of_lt bound, pool, List.getElem?_ofFn, dite_eq_left (by omega)]
  rw [ha, scatter_byte _ (unique_addr p hv _) _ _ _ w, ite_eq_left (cover w), valueEq]
  change some ((shaderNode p inputs (gid w))[w.i.val]!) = _
  rw [shader_node hv hd hk hf hm]
  have inNode : w.i.val < (node p (context p rs[w.sig]) w.j w.c).length := by
    rw [chain_length p hv]; exact w.i.isLt
  have expected := batch_wots_byte p hv mode rs w.sig w.j w.c w.i w.j.isLt w.c.isLt w.i.isLt
  change _ = (metalBatchSignInternal mode p rs).flatten[w.sig.val * p.sigBytes + offset p w.j w.c w.i]?
  rw [expected]
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem inNode,Option.getD_some]

end MetalWotsOutput

import Metal.XmssDispatch

namespace MetalForsDispatch
open Spec MetalPipeline MetalCommandValues MetalCommand MetalChainDispatch MetalLeafDispatch
open MetalWotsOutput (Context context)
open MetalReducerBytes (target)

/-- For an active signature, read both seeds through the slot named by its
FORS descriptor. Inactive rows have no submitted threadgroup. -/
def fetched (p : Params) (rs : List BatchSignReq) (sig : Nat) : Context :=
  let x := context p rs[sig]!
  if sig < rs.length then
    let j := MetalHostValues.job p rs sig
    let key := MetalHostValues.keys p rs j.key
    { x with sk := key.1, pk := key.2, tree := j.tree, leaf := j.leaf }
  else x

theorem fetched_spec (p : Params) (rs : List BatchSignReq) (sig : Nat) :
    fetched p rs sig = context p rs[sig]! := by
  by_cases h : sig < rs.length
  · have key := MetalHostValues.key_selected p rs ⟨sig,h⟩
    simp only [fetched,h,↓reduceIte,MetalHostValues.job,MetalHostValues.index,getElem!_pos rs sig h,
      Fin.getElem_fin] at key ⊢
    rw [key]
  · simp [fetched,h]

def subValue (p : Params) (rs : List BatchSignReq) (s1 s2 gid : Nat) :=
  let row := gid/2^s2
  let x := context p rs[row/p.k]!
  metalForsPass1SubRoot p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) (row%p.k) (gid%2^s2)

theorem sub_at (p : Params) (rs : List BatchSignReq) (s1 s2 : Nat)
    (s : Fin rs.length) (t : Fin p.k) (j : Fin (2^s2)) :
    let x := context p rs[s]
    subValue p rs s1 s2 ((s.val*p.k+t.val)*2^s2+j.val) =
      metalForsPass1SubRoot p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t j := by
  obtain ⟨r,sub⟩ := decode (s.val*p.k+t.val) j.val (2^s2) j.isLt
  obtain ⟨sig,tree⟩ := decode s.val t.val p.k t.isLt
  simp only [subValue,r,sub,sig,tree,Fin.getElem_fin,getElem!_pos rs s.val s.isLt]

def subBuffer (p : Params) (count s2 words size : Nat) (sub : Nat → Bytes) (out : Execution) :=
  run (count*p.k*2^s2) words size sub out

theorem sub_read (p : Params) (hv : p.Valid) (rs : List BatchSignReq) (s1 s2 words size : Nat)
    (split : s1+s2=p.a) (geom : p.n=words*size) (sub : Nat → Bytes) (source : ∀ i, sub i=subValue p rs s1 s2 i)
    (out : Execution) (order : out.schedule.Perm (grid (rs.length*p.k*2^s2) words))
    (s : Fin rs.length) (t : Fin p.k) (j : Fin (2^s2)) :
    let x := context p rs[s]
    readNode words (subBuffer p rs.length s2 words size sub out) ((s.val*p.k+t.val)*2^s2+j.val) =
      metalForsPass1SubRoot p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t j := by
  intro x
  let gid := (s.val*p.k+t.val)*2^s2+j.val
  have eq : sub gid = metalForsPass1SubRoot p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t j :=
    (source _).trans (sub_at p rs s1 s2 s t j)
  have len : (sub gid).length=words*size := by
    rw [eq, metal_fors_pass1_subroot_eq_fips p _ _ split]
    exact (forsNode_length p hv _ _ _ _ _).trans geom
  have writes := matches_run (rs.length*p.k*2^s2) words size sub sub out (covers_grid order) (fun _ _ => rfl)
  exact (readNode_spec _ _ _ _ _ writes gid (active _ _ _ _ (active _ _ _ _ s.isLt t.isLt) j.isLt) len).trans eq

/-- The second pass can only read one of this tree's actual published sub-roots. -/
theorem state_congr (p : Params) (s1 s2 : Nat) (pk : Bytes) (adrs : Adrs) (t : Nat) (left right : Nat → Bytes)
    (agree : ∀ i < 2^s2, left i = right i) (h : Nat) (hh : h ≤ s2) (i : Nat) (hi : i < 2^(s2-h)) :
    metalForsPass2State p s1 s2 pk adrs t left h i = metalForsPass2State p s1 s2 pk adrs t right h i := by
  induction h generalizing i with
  | zero => exact agree i (by simpa using hi)
  | succ h ih =>
    have pow : 2^(s2-h) = 2*2^(s2-(h+1)) := by rw [← Nat.pow_succ']; congr 1; omega
    simp only [metalForsPass2State,tgReduceStep,hi,↓reduceIte]
    rw [ih (by omega) (2*i) (by omega), ih (by omega) (2*i+1) (by omega)]

def second (p : Params) (rs : List BatchSignReq) (s1 s2 words : Nat) (mem : Memory)
    (row h i : Nat) :=
  let x := context p rs[row/p.k]!
  metalForsPass2State p s1 s2 x.pk (MetalForsPkDispatch.treeAddress x) (row%p.k)
    (fun j => readNode words mem (row*2^s2+j)) h i

def SubCorrect (p : Params) (rs : List BatchSignReq) (s1 s2 words : Nat) (mem : Memory) : Prop :=
  ∀ s : Fin rs.length, ∀ t : Fin p.k, ∀ j : Fin (2^s2),
    let x := context p rs[s]
    readNode words mem ((s.val*p.k+t.val)*2^s2+j.val) =
      metalForsPass1SubRoot p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t j

theorem second_at (p : Params) (rs : List BatchSignReq) (s1 s2 words : Nat) (mem : Memory)
    (valid : SubCorrect p rs s1 s2 words mem) (s : Fin rs.length) (t : Fin p.k)
    (h i : Nat) (hh : h≤s2) (hi : i<2^(s2-h)) :
    let x := context p rs[s]
    second p rs s1 s2 words mem (s.val*p.k+t.val) h i =
      metalForsPass2State p s1 s2 x.pk (MetalForsPkDispatch.treeAddress x) t
        (metalForsPass1SubRoot p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t) h i := by
  obtain ⟨sig,tree⟩ := decode s.val t.val p.k t.isLt
  simp only [second,sig,tree,Fin.getElem_fin,getElem!_pos rs s.val s.isLt]
  exact state_congr _ _ _ _ _ _ _ _ (fun i hi => valid s t ⟨i,hi⟩) _ hh _ hi

def rootVal (p : Params) (rs : List BatchSignReq) (s1 s2 words : Nat) (mem : Memory) (row : Nat) :=
  second p rs s1 s2 words mem row s2 0

theorem root_at (p : Params) (rs : List BatchSignReq) (s1 s2 words : Nat) (split : s1+s2=p.a)
    (mem : Memory) (valid : SubCorrect p rs s1 s2 words mem) (s : Fin rs.length) (t : Fin p.k) :
    rootVal p rs s1 s2 words mem (s.val*p.k+t.val) = MetalForsPkDispatch.treeRoot p (context p rs[s]) t := by
  let x := context p rs[s]
  exact (second_at p rs s1 s2 words mem valid s t s2 0 (by omega) (by simp)).trans
    (metal_fors_tree_root_eq_fips p _ _ split x.sk x.pk _ t)

theorem final_words (p : Params) (rs : List BatchSignReq) (words size : Nat) (f : Nat → Bytes)
    (out : Execution) (order : out.schedule.Perm (grid (rs.length*p.k) words))
    (eq : ∀ s : Fin rs.length, ∀ t : Fin p.k, f (s.val*p.k+t.val) = MetalForsPkDispatch.treeRoot p (context p rs[s]) t) :
    MetalForsPkDispatch.Roots p rs words size (run (rs.length*p.k) words size f out) := by
  intro s t ht w hw
  have h := matches_run (rs.length*p.k) words size f f out (covers_grid order) (fun _ _ => rfl)
  exact (h _ (active _ _ _ _ s.isLt ht) w hw).trans (congrArg (fun x => readWord x size w) (eq s ⟨t,ht⟩))

theorem unsplit_words (p : Params) (rs : List BatchSignReq) (words size : Nat)
    (out : Execution) (order : out.schedule.Perm (grid (rs.length*p.k) words)) :
    MetalForsPkDispatch.Roots p rs words size (subBuffer p rs.length 0 words size (subValue p rs p.a 0) out) := by
  simp only [subBuffer,pow_zero,Nat.mul_one]
  apply final_words p rs words size _ out order
  intro s t
  have h := sub_at p rs p.a 0 s t ⟨0,by decide⟩
  dsimp only at h
  rw [metal_fors_pass1_subroot_eq_fips p p.a 0 (by omega)] at h
  simpa [MetalForsPkDispatch.treeRoot] using h

theorem split_words (p : Params) (rs : List BatchSignReq) (s1 s2 words size : Nat) (split : s1+s2=p.a)
    (mem : Memory) (valid : SubCorrect p rs s1 s2 words mem) (out : Execution)
    (order : out.schedule.Perm (grid (rs.length*p.k) words)) :
    MetalForsPkDispatch.Roots p rs words size (run (rs.length*p.k) words size (rootVal p rs s1 s2 words mem) out) :=
  final_words _ _ _ _ _ _ order (root_at _ _ _ _ _ split _ valid)

def SecretFn := Nat → Nat → Bytes
def AuthFn := Nat → Nat → Nat → Bytes

def secretVal (p : Params) (rs : List BatchSignReq) (s1 sig t : Nat) :=
  let r := rs[sig]!
  let x := context p r
  metalForsPass1Secret p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t (target p r t)

def authVal (p : Params) (rs : List BatchSignReq) (s1 s2 words : Nat) (mem : Memory) (sig t h : Nat) :=
  let r := rs[sig]!
  let x := context p r
  let tgt := target p r t
  if h < s1 then metalForsPass1AuthNode p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t tgt h
  else second p rs s1 s2 words mem (sig*p.k+t) (h-s1) ((tgt >>> h) ^^^ 1)

theorem auth_at (p : Params) (rs : List BatchSignReq) (s1 s2 words : Nat) (split : s1+s2=p.a)
    (mem : Memory) (valid : SubCorrect p rs s1 s2 words mem) (s : Fin rs.length) (t : Fin p.k)
    (h : Nat) (hh : h<p.a) :
    let r := rs[s]
    let x := context p r
    authVal p rs s1 s2 words mem s t h =
      metalForsAuthNode p s1 s2 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t (target p r t) h := by
  intro r x
  simp only [authVal,getElem!_pos rs s.val s.isLt,metalForsAuthNode]
  by_cases low : h<s1
  · simp [low,r,x]
  · simp only [low,↓reduceIte,metalForsPass2AuthNode]
    have limit : target p rs[s] t < 2^p.a := base2b_getElem!_lt _ _ _ _ t.isLt
    have shifted : target p rs[s] t >>> h < 2^(p.a-h) := by
      rw [Nat.shiftRight_eq_div_pow,Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),← Nat.pow_add]
      simpa [Nat.sub_add_cancel (by omega : h≤p.a)] using limit
    have sib : ((target p rs[s] t >>> h) ^^^ 1) < 2^(p.a-h) :=
      MetalPipeline.xor_one_lt_two_pow (by omega) shifted
    apply second_at _ _ _ _ _ _ valid s t _ _ (by omega)
    simpa only [show s2-(h-s1) = p.a-h by omega,Fin.getElem_fin] using sib

def values {g : MetalSignatureLayout.Geometry} {n : Nat} (secret : SecretFn) (auth : AuthFn)
    (w : MetalReducerBytes.Field g n) : Spec.Byte :=
  match w.val.2.1 with
  | .inr (.inl (t,.inl _)) => (secret w.val.1 t)[w.val.2.2.val]!
  | .inr (.inl (t,.inr (.inl h))) => (auth w.val.1 t h)[w.val.2.2.val]!
  | .inr (.inl (t,.inr (.inr h))) => (auth w.val.1 t (g.s1+h.val))[w.val.2.2.val]!
  | _ => 0

/-- Both the thread-private and threadgroup writers serialize the owning
native word with the family's byte order before storing this signature byte. -/
def serialized {p : Params} {rs : List BatchSignReq} {g : MetalSignatureLayout.Geometry} (shake : Bool)
    (xmss : Nat → Nat → Bytes) (secret : SecretFn) (auth : AuthFn) (w : MetalReducerBytes.Field g rs.length) : Spec.Byte :=
  let store := fun (x : Bytes) => MetalWotsOutput.storeByte shake x w.val.2.2.val
  match w.val.2.1 with
  | .inr (.inl (t,.inl _)) => store (secret w.val.1 t)
  | .inr (.inl (t,.inr (.inl h))) => store (auth w.val.1 t h)
  | .inr (.inl (t,.inr (.inr h))) => store (auth w.val.1 t (g.s1+h.val))
  | .inr (.inr (j,.inr h)) => store (xmss (w.val.1.val*p.d+j.val) h)
  | _ => 0

theorem serialized_eq {p : Params} {rs : List BatchSignReq} {g : MetalSignatureLayout.Geometry} (shake : Bool)
    (xmss : Nat → Nat → Bytes) (secret : SecretFn) (auth : AuthFn) :
    serialized (p:=p) (rs:=rs) (g:=g) shake xmss secret auth =
      MetalXmssDispatch.values (p:=p) (rs:=rs) xmss (values secret auth) := by
  funext w
  rcases w with ⟨⟨s,n,b⟩,valid⟩
  rcases n with z | ⟨t,z|(l|u)⟩ | ⟨j,c|h⟩ <;>
    simp only [serialized,MetalWotsOutput.storeByte_eq,MetalXmssDispatch.values,values]

theorem batch_byte (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (s : Fin rs.length) (t : Fin p.k) (k : Fin (p.a+1)) (i : Fin p.n) (node : Bytes)
    (value : (slhSignInternal p rs[s].msg rs[s].sk rs[s].addrnd)[MetalReducerBytes.forsOffset p t k i]? = node[i.val]?) :
    (metalBatchSignInternal mode p rs).flatten[s.val*p.sigBytes+MetalReducerBytes.forsOffset p t k i]? = some node[i.val]! := by
  let offset := MetalReducerBytes.forsOffset p t k i
  have inTree := active _ _ _ _ k.isLt i.isLt
  have inForest := active _ _ _ _ t.isLt inTree
  have within : offset < p.sigBytes := by
    have total := sigBytes_parts p hv
    simp only [Params.forsSigBytes,Nat.mul_assoc,Nat.add_comm 1 p.a] at total
    unfold offset MetalReducerBytes.forsOffset; omega
  rw [metal_batch_sign_internal_eq_fips mode p hv]
  change (rs.map _).flatten[_]? = _
  rw [MetalWotsOutput.batchByte _ _ _ (fun _ => slhSignInternal_length p hv _ _ _) s _ within]
  have present : MetalReducerBytes.forsOffset p t k i < (slhSignInternal p rs[s].msg rs[s].sk rs[s].addrnd).length := by
    rw [slhSignInternal_length p hv]; exact within
  rw [List.getElem!_eq_getElem?_getD,← value,List.getElem?_eq_getElem present,Option.getD_some]

theorem sig_field (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (g : MetalSignatureLayout.Geometry) (hn : g.n=p.n) (hk : g.k=p.k) (one : 1≤g.s1)
    (split : g.s1+g.s2=p.a) (sig : MetalSignatureLayout.signatureBytes g=p.sigBytes)
    (words : Nat) (mem : Memory) (ok : SubCorrect p rs g.s1 g.s2 words mem)
    (sec : SecretFn) (auth : AuthFn) (hs : ∀ s t, sec s t=secretVal p rs g.s1 s t)
    (ha : ∀ s t h, auth s t h=authVal p rs g.s1 g.s2 words mem s t h)
    (xmss : Nat → Nat → Bytes) (w : MetalReducerBytes.Field g rs.length)
    (own : owner g w.val.2.1 = .forsLow ∨ owner g w.val.2.1 = .forsHigh) :
    (metalBatchSignInternal mode p rs).flatten[MetalSignatureLayout.address g w.val]? =
      some (MetalXmssDispatch.values (p:=p) (rs:=rs) xmss (values sec auth) w) := by
  rcases w with ⟨⟨s,node,b⟩,valid⟩
  rcases node with z | ⟨t, z | (l | u)⟩ | ⟨j, c | h⟩
  all_goals try (rcases own with a|a <;> contradiction)
  all_goals
    let tree := Fin.cast hk t
    let i := Fin.cast hn b
  · have res := batch_byte p hv mode rs s tree ⟨0,by omega⟩ i _
        (MetalReducerBytes.secret_byte p hv rs[s] g.s1 tree i tree.isLt i.isLt)
    simp only [Fin.getElem_fin] at res
    simpa only [MetalSignatureLayout.address,sig,hn,split,MetalReducerBytes.forsOffset,
      MetalXmssDispatch.values,values,hs,secretVal,getElem!_pos rs s.val s.isLt,Fin.getElem_fin,tree,i,Fin.val_cast,
      Nat.add_comm 1 p.a,Nat.mul_assoc,Nat.add_assoc,Nat.zero_mul,Nat.zero_add] using res
  · let height : Fin p.a := ⟨l.val,by have := l.isLt; omega⟩
    have link := auth_at p rs g.s1 g.s2 words split mem ok s tree height height.isLt
    have res := batch_byte p hv mode rs s tree ⟨height.val+1,by have := height.isLt; omega⟩ i _
      (MetalReducerBytes.auth_byte p hv rs[s] g.s1 g.s2 tree height i one split tree.isLt height.isLt i.isLt)
    rw [← link] at res
    simpa only [MetalSignatureLayout.address,sig,hn,split,MetalReducerBytes.forsOffset,
      MetalXmssDispatch.values,values,ha,tree,i,height,Fin.val_cast,
      Nat.add_comm 1 p.a,Nat.add_comm 1 l.val,Nat.mul_assoc,Nat.add_assoc] using res
  · let height : Fin p.a := ⟨g.s1+u.val,by have := u.isLt; omega⟩
    have link := auth_at p rs g.s1 g.s2 words split mem ok s tree height height.isLt
    have res := batch_byte p hv mode rs s tree ⟨height.val+1,by have := height.isLt; omega⟩ i _
      (MetalReducerBytes.auth_byte p hv rs[s] g.s1 g.s2 tree height i one split tree.isLt height.isLt i.isLt)
    rw [← link] at res
    simpa only [MetalSignatureLayout.address,sig,hn,split,MetalReducerBytes.forsOffset,
      MetalXmssDispatch.values,values,ha,tree,i,height,Fin.val_cast,Nat.add_comm 1 p.a,
      show 1+g.s1+u.val=g.s1+u.val+1 by omega,Nat.mul_assoc,Nat.add_assoc] using res

theorem signature_region (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (g : MetalSignatureLayout.Geometry) (hn : g.n=p.n) (hk : g.k=p.k) (one : 1≤g.s1)
    (split : g.s1+g.s2=p.a) (hd : g.d=p.d) (hc : g.wots=p.len)
    (sig : MetalSignatureLayout.signatureBytes g=p.sigBytes)
    (fors : MetalSignatureLayout.forsBytes g=p.forsSigBytes) (xmssBytes : MetalSignatureLayout.xmssBytes g=p.xmssSigBytes)
    (words : Nat) (mem : Memory) (ok : SubCorrect p rs g.s1 g.s2 words mem)
    (sec : SecretFn) (auth : AuthFn) (hs : ∀ s t, sec s t=secretVal p rs g.s1 s t)
    (ha : ∀ s t h, auth s t h=authVal p rs g.s1 g.s2 words mem s t h)
    (xmss : Nat → Nat → Bytes) (order : List (MetalReducerBytes.Field g rs.length))
    (orderOk : order.Perm (MetalReducerBytes.grid g rs.length))
    (atByte : MetalWotsOutput.Coord p rs.length → Nat) (toByte : MetalWotsOutput.Coord p rs.length → Spec.Byte)
    (schedule : List (MetalWotsOutput.Coord p rs.length)) (site : ∀ w, atByte w=MetalWotsOutput.addr w)
    (initial : Nat → Spec.Byte) (capacity : Nat) (bound : rs.length*p.sigBytes≤capacity)
    (scratch : Region → Prop) (region : Region) (own : region=.forsLow ∨ region=.forsHigh) (scratchOk : scratch region) :
    let bytes := MetalXmssDispatch.values (p:=p) (rs:=rs) xmss (values sec auth)
    let prev := MetalHostValues.afterMiddle (MetalReducerBytes.events order bytes) initial
    let pool := MetalWotsOutput.pool atByte toByte schedule prev capacity
    correct g rs.length (pool.take (rs.length*p.sigBytes)) (metalBatchSignInternal mode p rs).flatten scratch region := by
  intro bytes prev pool
  refine ⟨scratchOk,?_⟩
  intro b hb
  have fo : owner g b.2.1 = .forsLow ∨ owner g b.2.1 = .forsHigh := hb ▸ own
  have okF : owner g b.2.1 ≠ .randomizer ∧ owner g b.2.1 ≠ .wots := by rcases fo with e|e <;> simp [e]
  let f : MetalReducerBytes.Field g rs.length := ⟨b,okF⟩
  exact (MetalReducerBytes.survives g hn hd hc sig fors xmssBytes atByte toByte schedule site order bytes initial capacity bound f
    (MetalReducerBytes.complete _ orderOk f)).trans
    (sig_field p hv mode rs g hn hk one split sig words mem ok sec auth hs ha xmss f fo).symm

theorem scratch_region {g : MetalSignatureLayout.Geometry} {n} {out expected : Bytes} {inv : Region → Prop} {r : Region}
    (sub : r=.fors_sub_roots ∨ r=.fors_roots) (h : inv r) : correct g n out expected inv r := by
  refine ⟨h,?_⟩
  rintro ⟨s,node,i⟩ own
  rcases node with z | ⟨t,z|(l|u)⟩ | ⟨j,c|a⟩ <;> rcases sub with rfl|rfl <;> contradiction

def residual (trace excluded : List Access) (outputs : List Region) :=
  trace.all fun a => excluded.contains a || (a.writes.all fun r => outputs.contains r)

theorem residual_outputs {trace excluded : List Access} {outputs : List Region} {a : Access} {r : Region}
    (checked : residual trace excluded outputs = true) (ha : a∈trace) (others : a∉excluded) (hr : r∈a.writes) :
    r∈outputs := by
  have step := List.all_eq_true.mp checked a ha
  simp only [Bool.or_eq_true,List.contains_iff_mem] at step
  simpa using List.all_eq_true.mp (step.resolve_left others) r hr

end MetalForsDispatch

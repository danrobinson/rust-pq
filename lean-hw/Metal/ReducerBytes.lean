import Metal.HostValues

namespace MetalReducerBytes
open Spec MetalPipeline MetalCommandValues MetalCommand
open MetalWotsOutput (Context context flatByte)

def digest (p : Params) (r : BatchSignReq) :=
  Hmsg p (MetalHostValues.rand p r) (block p r.sk 2) (block p r.sk 3) r.msg
def target (p : Params) (r : BatchSignReq) (tree : Nat) :=
  (base2b ((digest p r).take p.mdBytes) p.a p.k)[tree]!

def piece (p : Params) (r : BatchSignReq) (t : Nat) :=
  let x := context p r
  forsPiece p x.sk x.pk (MetalForsPkDispatch.treeAddress x)
    (base2b ((digest p r).take p.mdBytes) p.a p.k) t

def forsOffset (p : Params) (t k i : Nat) := p.n+t*((p.a+1)*p.n)+(k*p.n+i)
def xmssOffset (p : Params) (j h i : Nat) :=
  p.n+p.forsSigBytes+j*p.xmssSigBytes+(p.len*p.n+(h*p.n+i))

theorem sigFors_byte (p : Params) (hv : p.Valid) (r : BatchSignReq) (t k i : Nat)
    (ht : t < p.k) (hk : k < p.a+1) (hi : i < p.n) :
    (slhSignInternal p r.msg r.sk r.addrnd)[forsOffset p t k i]? =
      (piece p r t)[k*p.n+i]? := by
  let x := context p r
  have key : slhSignInternal p r.msg r.sk r.addrnd =
      (MetalHostValues.rand p r ++ (List.range p.k).flatMap (piece p r)) ++
      htSign p x.pkFors x.sk x.pk x.tree x.leaf := rfl
  have lengths (t : Nat) : (piece p r t).length = (p.a+1)*p.n := forsPiece_length p hv _ _ _ _ _
  have within := active k i p.n (p.a+1) hk hi
  have forest := active t (k*p.n+i) ((p.a+1)*p.n) p.k ht within
  have randLen : (MetalHostValues.rand p r).length=p.n := PRFmsg_length p hv _ _ _
  rw [key,List.getElem?_append_left (by simp only [List.length_append,randLen,
    length_flatMap_const _ _ lengths, forsOffset]; omega)]
  rw [List.getElem?_append_right (by rw [randLen]; unfold forsOffset; omega),randLen]
  rw [show forsOffset p t k i - p.n = t*((p.a+1)*p.n)+(k*p.n+i) by unfold forsOffset; omega]
  exact flatByte (piece p r) _ _ _ _ lengths ht within

theorem secret_byte (p : Params) (hv : p.Valid) (r : BatchSignReq) (s1 t i : Nat)
    (ht : t < p.k) (hi : i < p.n) :
    let x := context p r
    (slhSignInternal p r.msg r.sk r.addrnd)[forsOffset p t 0 i]? =
      (metalForsPass1Secret p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t (target p r t))[i]? := by
  intro x
  rw [sigFors_byte p hv r t 0 i ht (by omega) hi,metal_fors_pass1_secret_eq_fips]
  simp only [piece,forsPiece,Nat.zero_mul,Nat.zero_add]
  rw [List.getElem?_append_left (by unfold forsSkGen; rw [PRF_length p hv]; exact hi)]
  rfl

theorem auth_byte (p : Params) (hv : p.Valid) (r : BatchSignReq) (s1 s2 t h i : Nat)
    (one : 1 ≤ s1) (split : s1+s2=p.a) (ht : t < p.k) (hh : h < p.a) (hi : i < p.n) :
    let x := context p r
    (slhSignInternal p r.msg r.sk r.addrnd)[forsOffset p t (h+1) i]? =
      (metalForsAuthNode p s1 s2 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t (target p r t) h)[i]? := by
  intro x
  have bound : target p r t < 2^p.a := base2b_getElem!_lt ((digest p r).take p.mdBytes) _ _ _ ht
  rw [sigFors_byte p hv r t (h+1) i ht (by omega) hi,metal_fors_auth_node_eq_fips p _ _ one split x.sk x.pk
    (MetalForsPkDispatch.treeAddress x) t (target p r t) h bound hh]
  simp only [piece,forsPiece,Nat.succ_mul]
  rw [List.getElem?_append_right (by unfold forsSkGen; rw [PRF_length p hv]; omega)]
  simp only [forsSkGen, PRF_length p hv]
  rw [show h*p.n+p.n+i-p.n=h*p.n+i by omega]
  exact flatByte _ _ _ _ _ (fun _ => forsNode_length p hv _ _ _ _ _) hh hi

def auth (p : Params) (x : Context) (j h : Nat) :=
  xmssNode p x.sk (((MetalWotsOutput.loc p x j).2 / 2^h) ^^^ 1) h x.pk (MetalWotsOutput.adrs p x j)

theorem sigXmss_byte (p : Params) (hv : p.Valid) (r : BatchSignReq) (j h i : Nat)
    (hj : j < p.d) (hh : h < p.hp) (hi : i < p.n) :
    (slhSignInternal p r.msg r.sk r.addrnd)[xmssOffset p j h i]? = (auth p (context p r) j h)[i]? := by
  let x := context p r
  have prefixLen : x.prefixBytes.length = p.n+p.forsSigBytes := by
    simp only [x,context,List.length_append,PRFmsg_length p hv,forsSign_length p hv]
  have layers := ht_layers_eq_spec p hv x.pkFors x.sk x.pk x.tree x.leaf
    (show x.leaf < 2^p.hp from digestLeaf_lt p hv _)
  change (x.prefixBytes ++ htSign p x.pkFors x.sk x.pk x.tree x.leaf)[_]? = _
  rw [← layers,List.getElem?_append_right (by unfold xmssOffset; omega),prefixLen]
  have atLevel := active h i p.n p.hp hh hi
  have within : p.len*p.n+(h*p.n+i) < p.xmssSigBytes := by simp only [Params.xmssSigBytes,Nat.add_mul]; omega
  rw [show xmssOffset p j h i - (p.n+p.forsSigBytes) = j*p.xmssSigBytes+(p.len*p.n+(h*p.n+i)) by unfold xmssOffset; omega]
  change ((List.range p.d).flatMap (MetalWotsOutput.layer p x))[_]? = _
  rw [flatByte (MetalWotsOutput.layer p x) _ _ _ _ (fun _ => xmssSign_length p hv _ _ _ _ _) hj within]
  unfold MetalWotsOutput.layer xmssSign
  rw [List.getElem?_append_right (by rw [wotsSign_length p hv]; omega),wotsSign_length p hv,
      show p.len*p.n+(h*p.n+i)-p.len*p.n=h*p.n+i by omega]
  exact flatByte (auth p x j) _ _ _ _ (fun _ => xmssNode_length p hv _ _ _ _ _) hh hi

/-- A byte written by a FORS pass or an XMSS authentication-path store. -/
abbrev Field (g : MetalSignatureLayout.Geometry) (n : Nat) :=
  { b : MetalSignatureLayout.Byte g n // owner g b.2.1 ≠ .randomizer ∧ owner g b.2.1 ≠ .wots }

def grid (g : MetalSignatureLayout.Geometry) (n : Nat) : List (Field g n) :=
  (MetalSignatureLayout.allBytes g n).filterMap fun b =>
    if h : owner g b.2.1 ≠ .randomizer ∧ owner g b.2.1 ≠ .wots then some ⟨b,h⟩ else none

theorem complete {g n} (order : List (Field g n)) (permutation : order.Perm (grid g n)) :
    ∀ w, w ∈ order := by
  intro w
  apply permutation.mem_iff.mpr
  apply List.mem_filterMap.mpr
  exact ⟨w.val, MetalSignatureLayout.allBytes_complete _ _ _, by simp [w.property]⟩

def events {g n} (order : List (Field g n)) (value : Field g n → Spec.Byte) :
    List (MetalHostValues.Middle g n) :=
  order.map fun f => ⟨f.val, f.property.1, value f⟩

theorem events_write {g n} (order : List (Field g n)) (value : Field g n → Spec.Byte) (initial : Nat → Spec.Byte)
    (f : Field g n) (inSchedule : f ∈ order) :
    MetalHostValues.afterMiddle (events order value) initial (MetalSignatureLayout.address g f.val) = value f := by
  classical
  change (order.map _).foldl _ initial _ = _
  rw [List.foldl_map]
  let site := fun b : Field g n => MetalSignatureLayout.address g b.val
  have injective : Function.Injective site := fun _ _ h => Subtype.ext (MetalSignatureLayout.disjoint _ _ h)
  change MetalWotsOutput.execute site value order initial (site f) = value f
  rw [MetalWotsOutput.scatter_byte _ injective,ite_eq_left inSchedule]

/-- Convert a WOTS coordinate into the typed signature layout, for either FORS split. -/
def wotsField {p : Params} {n} (g : MetalSignatureLayout.Geometry)
    (hn : g.n=p.n) (hd : g.d=p.d) (hc : g.wots=p.len) (w : MetalWotsOutput.Coord p n) :
    MetalSignatureLayout.Byte g n :=
  ⟨w.sig,.inr (.inr (Fin.cast hd.symm w.j,.inl (Fin.cast hc.symm w.c))),Fin.cast hn.symm w.i⟩

theorem survives {p n} (g : MetalSignatureLayout.Geometry)
    (nEq : g.n = p.n) (dEq : g.d = p.d) (cEq : g.wots = p.len)
    (sigEq : MetalSignatureLayout.signatureBytes g = p.sigBytes)
    (forsEq : MetalSignatureLayout.forsBytes g = p.forsSigBytes)
    (xmssEq : MetalSignatureLayout.xmssBytes g = p.xmssSigBytes)
    (whereAt : MetalWotsOutput.Coord p n → Nat) (wotsVal : MetalWotsOutput.Coord p n → Spec.Byte)
    (wots : List (MetalWotsOutput.Coord p n)) (footprint : ∀ w, whereAt w = MetalWotsOutput.addr w)
    (order : List (Field g n)) (value : Field g n → Spec.Byte) (initial : Nat → Spec.Byte)
    (capacity : Nat) (bound : n*p.sigBytes ≤ capacity) (f : Field g n) (present : f ∈ order) :
    let prev := MetalHostValues.afterMiddle (events order value) initial
    let pool := MetalWotsOutput.pool whereAt wotsVal wots prev capacity
    (pool.take (n*p.sigBytes))[MetalSignatureLayout.address g f.val]? = some (value f) := by
  intro prev pool
  let pos := MetalSignatureLayout.address g f.val
  have fits : pos < n*p.sigBytes := by rw [← sigEq]; exact MetalSignatureLayout.in_bounds g f.val
  rw [List.getElem?_take_of_lt fits]
  change (List.ofFn _)[pos]? = _
  rw [List.getElem?_ofFn,dite_eq_left (by omega)]
  apply congrArg some
  change MetalWotsOutput.execute whereAt wotsVal wots prev pos = _
  rw [MetalHostValues.preserve _ _ _ _ pos]
  · exact events_write order value initial f present
  · intro w _ eq
    have addr : MetalSignatureLayout.address g (wotsField g nEq dEq cEq w) = MetalWotsOutput.addr w := by
      simp [wotsField,MetalSignatureLayout.address,MetalWotsOutput.addr,MetalWotsOutput.offset,
            sigEq,forsEq,xmssEq,nEq,Nat.add_assoc]
    rw [footprint,← addr] at eq
    exact f.property.2 (by rw [MetalSignatureLayout.disjoint g n eq]; rfl)

end MetalReducerBytes

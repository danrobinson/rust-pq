import Integration.SlhDsaCompressionWotsReduction
import Integration.SlhDsaSetClosed
import Ideal.Core.HiddenPrefix
import Ideal.Inst.WotsPre128
import Ideal.Inst.SkPrf128

set_option maxRecDepth 768
set_option maxHeartbeats 800000
namespace Reduction.Compression.Wots256
open MLink Ideal Ideal.HP SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder Kronecker

abbrev Node := Bytes 16
abbrev Idx := Bytes 22 × Node
abbrev Row := Idx → Node
abbrev Table := Blk → St
attribute [local irreducible] tblocks mdFold

def write16 (st : St) (v : Node) : St :=
  Vector.ofFn fun i => if h : i.val < 16 then v[i.val]'h else st[i.val]

theorem wr (s : St) (v : Node) : out16 (write16 s v) = v := by
  ext i hi; simp [out16, write16]

theorem undo (s : St) (v : Node) : write16 (write16 s v) (out16 s) = s := by
  ext i hi; by_cases h : i < 16 <;> simp [write16, out16, h]

attribute [local irreducible] write16 out16

def block (x : Idx) := (tblocks x.1 [x.2]).1

private theorem block_inj : Function.Injective block := by
  rintro ⟨a,m⟩ ⟨b,n⟩ h
  have e : tblocks a [m] = tblocks b [n] := Prod.ext h
    ((tblocks_snd_of_length_one a [m] rfl).trans (tblocks_snd_of_length_one b [n] rfl).symm)
  obtain ⟨h₁,h₂⟩ := tblocks_injective e
  exact Prod.ext h₁ (List.singleton_injective h₂)

private noncomputable def index (b : Blk) : Option Idx := by
  classical
  exact if h : ∃ x, block x = b then some h.choose else none

private theorem index_block (x : Idx) : index (block x) = some x := by
  classical
  unfold index
  rw [dite_eq_left (show ∃ y, block y = block x from ⟨x,rfl⟩)]
  congr 1
  exact block_inj (Exists.choose_spec (show ∃ y, block y = block x from ⟨x,rfl⟩))

private theorem index_spec (b : Blk) (x : Idx) (h : index b = some x) : block x = b := by
  classical
  unfold index at h
  split_ifs at h with he
  exact Option.some.inj h ▸ he.choose_spec

def read (T : Table) : Row := fun x => out16 (T (block x))

noncomputable def put (T : Table) (R : Row) (b : Blk) : St :=
  (index b).elim (T b) (fun x => write16 (T b) (R x))

private theorem read_put (T : Table) (R : Row) : read (put T R) = R := by
  funext x
  simp only [read,put,index_block,Option.elim_some]
  exact wr _ _

theorem swap (z : Table × Row) : (put (put z.1 z.2) (read z.1),read (put z.1 z.2)) = z := by
  rcases z with ⟨T,R⟩
  refine Prod.ext (funext fun b => ?_) (read_put ..)
  unfold put
  cases he : index b with
  | none => simp only [he,Option.elim_none]
  | some x =>
    simp only [he,Option.elim_some,read]
    rw [index_spec b x he]
    exact undo _ _

/-- The ideal phase-one chain uses its private first block and the baseline
compression table at every later block. -/
def collection (g : CF St Blk) (T : Table) (a : Bytes 22) (xs : List Node) :=
  out16 (chainI g T (tblocks a xs))

theorem single {A B : Type} (g : CF A B) (T : B → A) (q : B × List B) (hn : q.2 = []) :
    chainI g T q = T q.1 := by simp only [chainI,hn,mdFold,List.foldl_nil]

theorem leaf (g : CF St Blk) (T : Table) (R : Row) (a : Bytes 22) (m : Node) :
    collection g (put T R) a [m] = R (a,m) :=
  (congrArg out16 (single g (put T R) (tblocks a [m]) (tblocks_snd_of_length_one a [m] rfl))).trans
    (congrFun (read_put T R) (a,m))

theorem collection_local (g : CF St Blk) (T : Table) (R U : Row) (a : Bytes 22) (xs : List Node)
    (ha : ∀ m, R (a,m) = U (a,m)) : collection g (put T R) a xs = collection g (put T U) a xs := by
  have e : put T R (tblocks a xs).1 = put T U (tblocks a xs).1 := by
    unfold put
    cases hi : index (tblocks a xs).1 with
    | none => simp only [Option.elim_none]
    | some x =>
      have had : x.1 = a := (btw128_tblocks x.1 [x.2]).symm.trans
        ((congrArg btw128 (index_spec _ _ hi)).trans (btw128_tblocks a xs))
      have he : R x = U x := by simpa only [← had] using ha x.2
      simp only [Option.elim_some,he]
  exact congrArg (fun s => out16 (mdFold g s (tblocks a xs).2)) e

def emb (cv : St) : Idx ↪ Input :=
  ⟨fun x => .inl (cv,block x), fun _ _ e => block_inj (congrArg Prod.snd (Sum.inl.inj e))⟩

def full (pk : Node) (cv : St) (g : CF St Blk) (h : CF Chain512 Block512) (T : Table) : CompressionTables :=
  (gstar IV128 (sb128 pk) cv g T,h)

theorem atRow {A B : Type} [DecidableEq A] [DecidableEq B]
    (iv cv : A) (s : B) (g : CF A B) (t u : B → A) (c : A) (b : B)
    (hh : gstar iv s cv g t (c,b) ≠ gstar iv s cv g u (c,b)) : c = cv ∧ t b ≠ u b := by
  unfold gstar at hh
  split_ifs at hh <;> simp_all

attribute [local irreducible] IV128 sb128 put gstar

private theorem diff_put (T : Table) (R U : Row) (b : Blk) (h : put T R b ≠ put T U b) :
    ∃ j, block j = b ∧ R j ≠ U j := by
  unfold put at h
  cases he : index b with
  | none => simp only [he,Option.elim_none] at h; exact (h rfl).elim
  | some j =>
    refine ⟨j,index_spec _ _ he, fun eq => h ?_⟩
    simp only [he,Option.elim_some,eq]

private theorem localL (pk : Node) (cv : St) (g : CF St Blk) (T : Table) (R U : Row) (q : St × Blk)
    (hn : gstar IV128 (sb128 pk) cv g (put T R) q ≠ gstar IV128 (sb128 pk) cv g (put T U) q) :
    ∃ j, (cv,block j) = q ∧ R j ≠ U j := by
  obtain ⟨c,b⟩ := q
  obtain ⟨hc,nh⟩ := atRow IV128 cv (sb128 pk) g (put T R) (put T U) c b hn
  obtain ⟨j,hj,hh⟩ := diff_put T R U b nh
  exact ⟨j,Prod.ext hc.symm hj,hh⟩

theorem portLocal {X Z J R Y : Type} (e : J → X) (p : J → Prop) (a b : X → Z)
    (f : Z → Y) (r : R → Y) (hl : ∀ x, a x ≠ b x → ∃ j, e j = x ∧ p j)
    (x : X ⊕ R) (hn : Sum.elim (f ∘ a) r x ≠ Sum.elim (f ∘ b) r x) :
    ∃ j, Sum.inl (e j) = x ∧ p j := by
  cases x with
  | inl t =>
    obtain ⟨j,hj,hp⟩ := hl t (fun he => hn (congrArg f he))
    exact ⟨j,congrArg Sum.inl hj,hp⟩
  | inr t => exact (hn rfl).elim

theorem port_eq (pk : Node) (cv : St) (g : CF St Blk) (h : CF Chain512 Block512) (T : Table) :
    oracle (full pk cv g h T) = Sum.elim
      ((fun v : St => (v,0)) ∘ gstar IV128 (sb128 pk) cv g T)
      (fun u => (0,arrayVectorEquivFin UInt64 8 (h u))) := by
  funext x
  cases x <;> rfl

theorem localPort (pk : Node) (cv : St) (g : CF St Blk) (h : CF Chain512 Block512) (T : Table)
    (R U : Row) (x : Input) (hd : oracle (full pk cv g h (put T R)) x ≠ oracle (full pk cv g h (put T U)) x) :
    ∃ j, emb cv j = x ∧ R j ≠ U j := by
  rw [port_eq,port_eq] at hd
  exact portLocal (fun j => (cv,block j)) (fun j => R j ≠ U j) _ _ _ _ (localL pk cv g T R U) x hd

theorem seed_ne (pk : Node) (a : Bytes 22) (m : Node) : sb128 pk ≠ block (a,m) := by
  intro e
  have he := congrArg (fun v : Blk => v[38]) e
  simp only [block,sb128_get38,tblocks_one_get38] at he
  exact absurd he (by decide)

theorem keyed_one {A B K : Type} [DecidableEq A] [DecidableEq B]
    (iv : A) (s : K → B) (pk : K) (cv : A) (g : CF A B) (T : B → A) (q : B × List B)
    (hs : s pk ≠ q.1) (hn : q.2 = []) :
    keyedChain iv s (gstar iv (s pk) cv g T) pk q = T q.1 := by
  have neq : (cv,q.1) ≠ (iv,s pk) := fun e => hs (congrArg Prod.snd e).symm
  simp only [keyedChain,hn,mdFold,List.foldl_nil,gstar,ite_true,neq,ite_false]


/-- The singleton verifier using the reprogrammed public table agrees with
the ideal private-row response even when the hidden chaining value equals the IV. -/
theorem publicLeaf (pk : Node) (cv : St) (g : CF St Blk) (T : Table) (R : Row) (a : Bytes 22) (m : Node) :
    out16 (keyedChain IV128 sb128 (gstar IV128 (sb128 pk) cv g (put T R)) pk (tblocks a [m])) = R (a,m) :=
  (congrArg out16 (keyed_one IV128 sb128 pk cv g (put T R) (tblocks a [m])
    (seed_ne pk a m) (tblocks_snd_of_length_one a [m] rfl))).trans (congrFun (read_put T R) (a,m))

end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.publicLeaf
#print axioms Reduction.Compression.Wots256.swap
#print axioms Reduction.Compression.Wots256.leaf
#print axioms Reduction.Compression.Wots256.collection_local
#print axioms Reduction.Compression.Wots256.localPort

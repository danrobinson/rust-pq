import Integration.SlhDsaCompressionItsrReduction
import MIdeal.Itsr128f

namespace Reduction.Compression.SmallItsr
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA SLHDSA.DigestTransport KeyedHash Classical
variable (S : Sha2Set) (hs : S.vp.params.n = 16)
abbrev Cell := St × Blk
abbrev Entry := Cell × St
abbrev Evidence := Option (Cell ⊕ (Cell × Cell))
abbrev Query := MessageHash.Query S

def raw (x : Query S) : Fast128.Input := cast (congrArg (fun n => Bytes n × Bytes n × Bytes n × List Byte) hs) x

theorem raw_injective : Function.Injective (raw S hs) :=
  (Equiv.cast (congrArg (fun n => Bytes n × Bytes n × Bytes n × List Byte) hs)).injective

def visits (g : CompressionTables) (xs : List (Query S)) :=
  (xs.flatMap (fun x => Fast128.cells g.1 (raw S hs x))).dedup

def last (g : CompressionTables) (x : Query S) : Cell := (g.1 (Fast128.prefixCell g.1 (raw S hs x)),counterFinal 0)

def msg (g : CompressionTables) (x : Query S) := (tablePrimitives g S.vp.params).Hmsg x.1 x.2.1 x.2.2.1 x.2.2.2

noncomputable local instance (g : CompressionTables) : SampleableType (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (SampleableType S.Node)
variable {K : Type} [DecidableEq K] (key : St → K)

structure Covers (i : Fin S.vp.params.k) : Prop where
  hit : ∀ g x y, (coveringDigest S.vp (msg S g x)).1 = (coveringDigest S.vp (msg S g y)).1 →
      (coveringDigest S.vp (msg S g x)).2 i = (coveringDigest S.vp (msg S g y)).2 i →
      key (g.1 (last S hs g x)) = key (g.1 (last S hs g y))

def select (xs : List Entry) : Evidence :=
  match xs.find? (fun z => decide (z.2 = IV128)) with
  | some z => some (.inl z.1)
  | none => ((xs.product xs).find? (fun p => decide (p.1.1 ≠ p.2.1 ∧ key p.1.2 = key p.2.2))).map
      (fun p => .inr (p.1.1,p.2.1))

def accepts (g : CompressionTables) : Evidence → Prop
  | none => False
  | some (.inl u) => g.1 u = IV128
  | some (.inr (u,v)) => u ≠ v ∧ key (g.1 u) = key (g.1 v)

def trace (g : CompressionTables) (xs : List (Query S)) : List Entry := (visits S hs g xs).map (fun u => (u,g.1 u))

theorem selected (i : Fin S.vp.params.k) (c : Covers S hs key i) (g : CompressionTables) (cand : Query S)
    (ts : List (Query S)) (win : (itsrProblem S.vp (tablePrimitives g S.vp.params)).Wins ts cand) :
    accepts key g (select key (trace S hs g (cand::ts))) := by
  let vis := visits S hs g (cand::ts)
  let xs := trace S hs g (cand::ts)
  have incl (x : Query S) (hx : x ∈ cand::ts) (u : Cell) (hu : u ∈ Fast128.cells g.1 (raw S hs x)) : u ∈ vis :=
    List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨x,hx,hu⟩)
  have mem (e : Entry) (h : e ∈ xs) : g.1 e.1 = e.2 := by obtain ⟨u,_,rfl⟩ := List.mem_map.mp h; rfl
  have entry (u : Cell) (h : u ∈ vis) : (u,g.1 u) ∈ xs := List.mem_map.mpr ⟨_,h,rfl⟩
  change accepts key g (select key xs)
  unfold select
  cases he : xs.find? (fun z => decide (z.2 = IV128)) with
  | some z => exact (mem _ (List.mem_of_find?_eq_some he)).trans (of_decide_eq_true (List.find?_some (p := fun e : Entry => decide (e.2 = IV128)) he))
  | none =>
    let ok := fun p : Entry × Entry => decide (p.1.1 ≠ p.2.1 ∧ key p.1.2 = key p.2.2)
    change accepts key g (((xs.product xs).find? ok).map _)
    cases hp : (xs.product xs).find? ok with
    | some p =>
      have m := List.mem_product.mp (List.mem_of_find?_eq_some hp)
      have w : p.1.1 ≠ p.2.1 ∧ key p.1.2 = key p.2.2 := of_decide_eq_true (List.find?_some (p := ok) hp)
      exact ⟨w.1,by rw [mem _ m.1,mem _ m.2]; exact w.2⟩
    | none =>
      exfalso
      have noPair (u v : Cell) (mu : u ∈ vis) (mv : v ∈ vis) (ne : u ≠ v) (eq : key (g.1 u) = key (g.1 v)) : False := by
        have hh := List.find?_eq_none.mp hp ((u,g.1 u),(v,g.1 v)) (List.mem_product.mpr ⟨entry u mu,entry v mv⟩)
        simp [ok,ne,eq] at hh
      have inject : ∀ u ∈ vis, ∀ v ∈ vis, g.1 u = g.1 v → u = v :=
        fun u hu v hv eq => by_contra (fun hn => noPair u v hu hv hn (congrArg key eq))
      have iv (u : Cell) (hu : u ∈ vis) : g.1 u ≠ IV128 := by
        intro eq
        have hh := List.find?_eq_none.mp he (u,g.1 u) (entry u hu)
        simp [eq] at hh
      let d := msg S g cand
      let needle := ((splitDigest S.vp.params d).forsAdrs, i.val * 2^S.vp.params.a +
        forsIdx S.vp.params (splitDigest S.vp.params d).md.toList i.val)
      have hn : needle ∈ idxOf S.vp d := by
        simp only [idxOf,Reduction.forsIndices,List.mem_map,List.mem_range]
        exact ⟨i.val,i.isLt,rfl⟩
      obtain ⟨y,hy,hit⟩ := List.mem_flatMap.mp (win.2 needle hn)
      obtain ⟨h₁,h₂⟩ := match_of_mem_idxOf S.vp d (msg S g y) i hit
      have last_in (x : Query S) (hx : x ∈ cand::ts) : last S hs g x ∈ vis :=
        incl x hx _ (by simp [last,Fast128.cells])
      have diff : last S hs g cand ≠ last S hs g y := by
        intro eq
        have rows := congrArg Prod.fst eq
        have same := Fast128.row_injective g.1 vis inject iv (raw S hs cand) (raw S hs y)
          (incl _ (List.mem_cons_self ..)) (incl _ (List.mem_cons_of_mem _ hy)) rows
        exact win.1 ((raw_injective S hs same).symm ▸ hy)
      exact noPair _ _ (last_in _ (List.mem_cons_self ..)) (last_in _ (List.mem_cons_of_mem _ hy)) diff
        (c.hit g cand y h₁.symm h₂.symm)

end Reduction.Compression.SmallItsr
#print axioms Reduction.Compression.SmallItsr.selected

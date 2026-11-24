import MIdeal.Hmac512
import Ideal.Inst.MsgPrf128

namespace MIdeal.Sha512
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec ENNReal PRFScheme VCVio.Algorithms.Sha2
variable (S : Sha2Set)
private theorem width64 : S.vp.params.n ≤ 64 := by cases S <;> decide

def takeBytes (n : ℕ) (hn : n ≤ 64) (st : Bytes 64) : Bytes n :=
  Vector.ofFn fun i => st[i.val]'(Nat.lt_of_lt_of_le i.isLt hn)

theorem takeBytes_balanced (n : ℕ) (hn : n ≤ 64) (P : Bytes n → Prop) :
    Pr{let u ← $ᵗ (Bytes 64)}[P (takeBytes n hn u)] = Pr{let y ← $ᵗ Bytes n}[P y] := by
  let low (s : (Bytes 64)) : Bytes (64-n) := Vector.ofFn fun i => s[i.val+n]'(by omega)
  have split : Function.Bijective (fun s : (Bytes 64) => (takeBytes n hn s, low s)) := by
    constructor
    · intro s t h
      obtain ⟨h1,h2⟩ := Prod.mk.inj h
      apply Vector.ext
      intro i hi
      by_cases h : i < n
      · simpa [takeBytes] using congrArg (fun v : Bytes n => v[i]'h) h1
      · have eq := congrArg (fun v : Bytes (64-n) => v[i-n]'(by omega)) h2
        simpa [low, show i-n+n = i by omega] using eq
    · rintro ⟨a,b⟩
      refine ⟨Vector.ofFn fun i : Fin 64 => if h : i.val < n then a[i.val]'h else b[i.val-n]'(by omega), ?_⟩
      apply Prod.ext
      · apply Vector.ext; intro i hi; simp [takeBytes]
      · apply Vector.ext; intro i hi; simp [low]
  exact (SampleableType.prEvent_uniformSample_comp_of_bijective split (fun z => P z.1)).trans
    (SampleableType.prEvent_uniformSample_fst P)

theorem takeBytes_eq (n : ℕ) (hn : n ≤ 64) (s : (Bytes 64)) : byteArrayPrefixOrZero (bytesToByteArray s) n = takeBytes n hn s := by
  have hraw : ((bytesToByteArray s).extract 0 n).toList = s.toList.take n := by
    rw [ByteArray.toList_eq_toList_data, ByteArray.data_extract, Array.toList_extract]
    simp [bytesToByteArray, Vector.toList]
  have hl : ((bytesToByteArray s).extract 0 n).toList.length = n := by
    rw [hraw]; simp [Nat.min_eq_left hn]
  simp only [byteArrayPrefixOrZero, byteArrayPrefixChecked, decodeExact, hl, dite_true]
  apply Vector.ext
  intro i hi
  simp [takeBytes, hraw]

abbrev prefixBytes := takeBytes S.vp.params.n (width64 S)

theorem prefix_balanced (P : S.Node → Prop) :
    Pr{let u ← $ᵗ (Bytes 64)}[P (prefixBytes S u)] = Pr{let y ← $ᵗ S.Node}[P y] :=
  takeBytes_balanced _ _ P

theorem prefix_eq (s : Bytes 64) :
    byteArrayPrefixOrZero (bytesToByteArray s) S.vp.params.n = prefixBytes S s :=
  takeBytes_eq _ _ s

def innerBlocks (d : S.Node × List Byte) : Block512 × List Block512 :=
  ((iblocks S d.1 d.2).headD (Vector.replicate 128 0), (iblocks S d.1 d.2).tail)

theorem iblocks_eq_cons (d : S.Node × List Byte) :
    iblocks S d.1 d.2 = (innerBlocks S d).1 :: (innerBlocks S d).2 := by
  have h := iblocks_ne_nil S d.1 d.2
  unfold innerBlocks
  cases hb : iblocks S d.1 d.2 with
  | nil => exact absurd hb h
  | cons b bs => rfl

theorem innerBlocks_injective : Function.Injective (innerBlocks S) := by
  intro d d' h
  have h1 : iblocks S d.1 d.2 = iblocks S d'.1 d'.2 := by
    rw [iblocks_eq_cons, iblocks_eq_cons, h]
  obtain ⟨h2, h3⟩ := iblocks_injective S h1
  exact Prod.ext h2 h3

/-- Number of inner blocks after the first one. -/
theorem innerBlocks_snd_length (d : S.Node × List Byte) :
    (innerBlocks S d).2.length = (d.2.length + S.vp.params.n + 16) / 128 := by
  have h := iblocks_length S d.1 d.2
  rw [iblocks_eq_cons] at h
  simpa using h


def trunc (s : Chain512) : S.Node := prefixBytes S (serialize s)

theorem trunc_uniform (P : S.Node → Prop) :
    Pr{let u ← $ᵗ Chain512}[P (trunc S u)] = Pr{let y ← $ᵗ S.Node}[P y] :=
  (SampleableType.prEvent_uniformSample_comp_of_bijective serialize_bijective
    (fun s => P (prefixBytes S s))).trans (prefix_balanced S P)

local instance (g : CompressionTables) (p : Params) : SampleableType (tablePrimitives g p).SkPrf :=
  inferInstanceAs (SampleableType (Bytes p.n))
local instance (g : CompressionTables) (p : Params) : SampleableType (tablePrimitives g p).Y :=
  inferInstanceAs (SampleableType (Bytes p.n))

theorem msg_scheme (g : CompressionTables) (hw : S.vp.params.n ≠ 16) :
    Reduction.msgPrf S.vp (tablePrimitives g S.vp.params) =
      macSchemeI initial (ikey S) (okey S) (innerBlocks S) oblock (trunc S) g.2 := by
  have he (k : S.Node) (d : S.Node × List Byte) :
      (tablePrimitives g S.vp.params).PRFmsg k d.1 d.2 =
        macF initial (ikey S) (okey S) (innerBlocks S) oblock (trunc S) g.2 k d := by
    obtain ⟨r,m⟩ := d
    apply (msgPrf_shape S g hw k r m).trans
    rw [iblocks_eq_cons S (r,m)]
    simp only [macF, keyedChain, mdFold, List.foldl_cons, trunc]
    let st := g.2 (g.2 (initial,okey S k),oblock
      ((innerBlocks S (r,m)).2.foldl (fun st b => g.2 (st,b))
        (g.2 (g.2 (initial,ikey S k),(innerBlocks S (r,m)).1))))
    exact prefix_eq S (serialize st)
  unfold Reduction.msgPrf SLHDSA.msgPrfScheme macSchemeI
  exact congrArg (fun f => (⟨$ᵗ S.Node, f⟩ : PRFScheme S.Node (S.Node × List Byte) S.Node))
    (funext fun k => funext (he k))

abbrev MsgAdv := PrfAdvI Chain512 Block512 S.Node (List Byte) S.Node

noncomputable def real (g256 : CF St Blk) (A : MsgAdv S) : ℝ≥0∞ :=
  cfAdvantage fun g => (Reduction.msgPrf S.vp (tablePrimitives (g256,g) S.vp.params)).prfRealExperiment (A.inst g)

noncomputable def ideal (A : MsgAdv S) : ℝ≥0∞ :=
  cfAdvantage fun g => prfIdealExperiment (A.inst g)

def short (limit : ℕ) : ℕ ⊕ ((Chain512 × Block512) ⊕ (S.Node × List Byte)) → Prop
  | .inr (.inr d) => d.2.length ≤ limit
  | _ => True

/-- The SHA-512 message PRF at both 192-bit and 256-bit widths, conditional
on any fixed public SHA-256 table. The error is two-sided. -/
theorem msg_prf_bound (g256 : CF St Blk) (hw : S.vp.params.n ≠ 16) (A : MsgAdv S)
    (q qo limit : ℕ) (hq : IsQueryBoundP A (fun i => isCompQ i = true) q)
    (ho : IsQueryBoundP A (fun i => isPrfQ i = true) qo) (hs : AllQueriesSatisfy A (short S limit)) :
    let L := (limit + S.vp.params.n + 16)/128
    let err := 2*(q:ℝ≥0∞)*(Fintype.card S.Node : ℝ≥0∞)⁻¹ +
      ((3*q + qo*(1+3*L) + 3 + (q+qo*(1+L))^2 : ℕ) : ℝ≥0∞)*((2:ℝ≥0∞)^512)⁻¹
    real S g256 A ≤ ideal S A + err ∧ ideal S A ≤ real S g256 A + err := by
  let L := (limit + S.vp.params.n + 16)/128
  have hl : AllQueriesSatisfy A (ibLenLe (innerBlocks S) L) := by
    refine AllQueriesSatisfy.mono hs ?_
    rintro (n|port|d) h
    · trivial
    · trivial
    · change (innerBlocks S d).2.length ≤ L
      rw [innerBlocks_snd_length]
      exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.add_le_add_right h _) _)
  have hr : real S g256 A = HP.prT (macRealGameI initial (ikey S) (okey S) (innerBlocks S) oblock (trunc S) A) := by
    rw [← cfAdvantage_macReal]
    unfold real
    refine congrArg cfAdvantage (funext fun g => ?_)
    exact congrArg (fun sch : PRFScheme S.Node (S.Node × List Byte) S.Node =>
      sch.prfRealExperiment (A.inst g)) (msg_scheme S (g256,g) hw)
  have hi : ideal S A = HP.prT (prfIdealGameI A) := cfAdvantage_prfIdeal A
  rw [hr, hi]
  have h := prT_mac_two_sided initial (ikey S) (okey S) (ikey_injective S) (okey_injective S)
    (key_blocks_distinct S) (innerBlocks S) (innerBlocks_injective S) oblock oblock_injective
    (trunc S) (trunc_uniform S) A q qo L hq ho hl
  simpa only [card_chain512, Nat.cast_pow, Nat.cast_ofNat] using h

end MIdeal.Sha512

#print axioms MIdeal.Sha512.msg_prf_bound

import Xmsskeys.Prepare
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssKeys
open XmssKeysRust (asChecked asPad)
abbrev shape (N G L : Usize) := (N.val=16 ∧ G.val=16 ∧ L.val=640) ∨
  (N.val=24 ∧ G.val=8 ∧ L.val=1280) ∨ (N.val=32 ∧ G.val=8 ∧ L.val=2304)
def seedOf {N} (s : XmssKeysRust.hash.Seed N) : hash.Seed N := ⟨s.pk_seed,s.state,s.state512⟩
def digestPrefix {N G L} (s : XmssKeysRust.hash.Seed N) (sk : Array U8 N) (a : XmssKeysRust.address.Adrs)
    (first : U32) (rows : Array (Array U8 L) G) (out : Wots.Rows N) := do
  let (active,back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 L))) rows ⟨out.len⟩
  let written ← XmssKeysRust.sha256.x86.wots_endpoints s.state sk a first active
  let active' ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 L))) (back written) ⟨out.len⟩
  if N=16#usize then XmssKeysRust.sha256.x86.key_digests s.state active' out
  else XmssKeysRust.sha512.x86.key_digests s.state512 active' out

theorem digestPrefix_spec {N G L} (p : params.Params) (hp : PN p N) (seed : XmssKeysRust.hash.Seed N)
    (hs : SeedOk (seedOf seed)) (sk : Array U8 N) (a : XmssKeysRust.address.Adrs) (first : U32)
    (rows : Array (Array U8 L) G) (out : Wots.Rows N) (size block : Usize) (cpu : GatherRust.avx512Available=true)
    (format : shape N G L) (blockEq : block = if N=16#usize then 64#usize else 128#usize)
    (sizeEq : size.val=22+(2*N.val+3)*N.val) (keys : first.val+G.val≤2^32) (used : out.length≤G.val)
    (nonempty : 0<out.length) (prepared : ∀ j<G.val, initialized (Array.repeat L 0#u8) rows.val[j]! a first size block j) :
    digestPrefix seed sk a first rows out ⦃ final => final.length=out.length ∧ ∀ j<out.length,
      bytes final.val[j]!.val = Spec.wotsPkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val)
        (Wots.leafAddress (asChecked a) (first.val+j)) ⦄ := by
  unfold digestPrefix
  apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice rows ⟨out.len⟩ used)
  rintro ⟨active,back⟩ ⟨slice,len,restore⟩
  have same : active.length=out.length := len
  have supported : Wots.Checked.supported N L := by rcases format with h|h|h <;> simp_all [Wots.Checked.supported]
  have cap : active.length≤16 := by rcases format with h|h|h <;> omega
  have keyRoom : first.val+active.length≤2^32 := by omega
  obtain ⟨written,op,wlen,_⟩ := spec_imp_exists (Wots.Checked.endpoints_fips (paramsS p) seed.state sk (asChecked a)
    first active (bytes seed.pk_seed.val) cpu supported cap hp.n.symm (by simpa using hp.n.symm)
    (by rw [hp.n]; exact hs.1) keyRoom)
  simp only
  unfold XmssKeysRust.sha256.x86.wots_endpoints
  simp only [op,bind_tc_eq,bind_ok]
  have changed : written.length=out.length := wlen.trans same
  step as ⟨active',sliced,len'⟩
  have readBack : active'=written := by
    apply Slice.ext
    apply List.ext_getElem
    · exact len'.trans changed.symm
    · intro j h h'
      rw [← getElem!_pos active'.val j h,← getElem!_pos written.val j h',sliced,Array.val_to_slice,restore]
      exact back_lane _ _ j out.length (by change j<written.length at h'; omega) changed (by simpa using used)
  subst active'
  have sizes : (N.val=16 ∧ L.val=640 ∧ block.val=64 ∧ active.length≤16) ∨
      (N.val=24 ∧ L.val=1280 ∧ block.val=128 ∧ active.length≤8) ∨
      (N.val=32 ∧ L.val=2304 ∧ block.val=128 ∧ active.length≤8) := by
    rcases format with ⟨n,g,l⟩|⟨n,g,l⟩|⟨n,g,l⟩
    · exact Or.inl ⟨n,l,by rw [blockEq,if_pos (UScalar.eq_of_val_eq n)]; rfl,cap⟩
    · apply Or.inr ∘ Or.inl; exact ⟨n,l,by rw [blockEq,if_neg (by scalar_tac)]; rfl,by omega⟩
    · exact Or.inr (Or.inr ⟨n,l,by rw [blockEq,if_neg (by scalar_tac)]; rfl,by omega⟩)
  have proof := Wots.keyBatch_fips p hp (seedOf seed) hs sk (asChecked a) first active out size block cpu sizes
    (by omega) same.symm sizeEq keyRoom (fun j hj => by
      have eq : active.val[j]! = rows.val[j]! := by rw [slice]; exact slice0_getElem! _ _ _ (by omega) (by simpa using used)
      rw [eq]; exact prepared j (by omega))
  unfold Wots.keyBatch at proof
  change WotsX86Rust.sha256.x86.wots_endpoints (seedOf seed).state sk (asChecked a) first active = ok written at op
  simp only [op,bind_tc_eq,bind_ok] at proof
  simpa only [seedOf,XmssKeysRust.sha256.x86.key_digests,XmssKeysRust.sha512.x86.key_digests] using proof

end slhdsa.X86.XmssKeys

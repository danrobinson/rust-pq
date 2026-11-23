import Wotswide.Backend
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots.Wide

def coreAddress (a : WotsWideRust.address.Adrs) : slhdsa.address.Adrs :=
  ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def coreSeed {N} (s : WotsWideRust.hash.Seed N) : slhdsa.hash.Seed N := ⟨s.pk_seed,s.state,s.state512⟩


private theorem addExact (x y z : Usize) (numeric : x.val + y.val = z.val) :
    (x + y) = ok z := by
  obtain ⟨out,eq,value⟩ := spec_imp_exists (Usize.add_spec (x := x) (y := y) (by rw [numeric]; scalar_tac))
  rw [eq,UScalar.eq_of_val_eq (value.trans numeric)]

private theorem mulExact (x y z : Usize) (numeric : x.val * y.val = z.val) :
    (x * y) = ok z := by
  obtain ⟨out,eq,value⟩ := spec_imp_exists (Usize.mul_spec (x := x) (y := y) (by rw [numeric]; scalar_tac))
  rw [eq,UScalar.eq_of_val_eq (value.trans numeric)]

theorem thash_eq {N : Usize} (seed : WotsWideRust.hash.Seed N) (a : WotsWideRust.address.Adrs)
    (b : Slice (Array U8 64#usize)) (width : NOk N) (size : b.length = 2*N.val+3) :
    WotsWideRust.hash.thash_values seed a b = hash.thash_values (coreSeed seed) (coreAddress a) b := by
  have adr : WotsWideRust.address.Adrs.compress a = address.Adrs.compress (coreAddress a) := rfl
  have fill0 : WotsWideRust.hash.thash_values_loop0 = hash.thash_values_loop0 := rfl
  have fill2 : WotsWideRust.hash.thash_values_loop2 = hash.thash_values_loop2 := rfl
  have trunc : WotsWideRust.hash.trunc = hash.trunc := rfl
  have trunc512 : WotsWideRust.hash.trunc512 = hash.trunc512 := rfl
  unfold WotsWideRust.hash.thash_values hash.thash_values
  rw [adr,fill0,fill2,trunc,trunc512]
  rcases width with h|h|h
  · have w : N = 16#usize := UScalar.eq_of_val_eq h
    subst N
    have l : b.len = 35#usize := UScalar.eq_of_val_eq (by simpa using size)
    have calcLen : (16#usize * 35#usize) = ok 560#usize := mulExact _ _ _ rfl
    have calcMsg : (22#usize + 560#usize) = ok 582#usize := addExact _ _ _ rfl
    have pad : (582#usize + 9#usize) = ok 591#usize := addExact _ _ _ rfl
    have align : (591#usize + 63#usize) = ok 654#usize := addExact _ _ _ rfl
    have div : (654#usize / 64#usize) = ok 10#usize := by rfl
    have mul : (10#usize * 64#usize) = ok 640#usize := mulExact _ _ _ rfl
    simp only [l,calcLen,calcMsg,pad,align,div,mul,bind_ok,ite_true,coreSeed,
      same256 _ 640#usize _ (by decide) (by decide)]
  · have w : N = 24#usize := UScalar.eq_of_val_eq h
    subst N
    have l : b.len = 51#usize := UScalar.eq_of_val_eq (by simpa using size)
    have calcLen : (24#usize * 51#usize) = ok 1224#usize := mulExact _ _ _ rfl
    have calcMsg : (22#usize + 1224#usize) = ok 1246#usize := addExact _ _ _ rfl
    have pad : (1246#usize + 17#usize) = ok 1263#usize := addExact _ _ _ rfl
    have align : (1263#usize + 127#usize) = ok 1390#usize := addExact _ _ _ rfl
    have div : (1390#usize / 128#usize) = ok 10#usize := by rfl
    have mul : (10#usize * 128#usize) = ok 1280#usize := mulExact _ _ _ rfl
    simp only [l,calcLen,calcMsg,pad,align,div,mul,bind_ok,show 24#usize ≠ 16#usize by decide,ite_false,coreSeed,
      same512 _ 1280#usize _ (by decide) (by decide)]
  · have w : N = 32#usize := UScalar.eq_of_val_eq h
    subst N
    have l : b.len = 67#usize := UScalar.eq_of_val_eq (by simpa using size)
    have calcLen : (32#usize * 67#usize) = ok 2144#usize := mulExact _ _ _ rfl
    have calcMsg : (22#usize + 2144#usize) = ok 2166#usize := addExact _ _ _ rfl
    have pad : (2166#usize + 17#usize) = ok 2183#usize := addExact _ _ _ rfl
    have align : (2183#usize + 127#usize) = ok 2310#usize := addExact _ _ _ rfl
    have div : (2310#usize / 128#usize) = ok 18#usize := by rfl
    have mul : (18#usize * 128#usize) = ok 2304#usize := mulExact _ _ _ rfl
    simp only [l,calcLen,calcMsg,pad,align,div,mul,bind_ok,show 32#usize ≠ 16#usize by decide,ite_false,coreSeed,
      same512 _ 2304#usize _ (by decide) (by decide)]

end slhdsa.X86.Wots.Wide

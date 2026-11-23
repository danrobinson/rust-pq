import Rcarmcode.Proof
import Rcarmcode.Proof512
import Rcsoft.Proof
import Rcsoft256.Proof

/-! # Arm Linux runtime dispatch

Arm AARCHMRS 2026-09, `Features.json`, gives FEAT_SHA3 ⇒ FEAT_SHA512 and its
converse. Linux identifies them individually in AT_HWCAP bits 17 and 21.
An operating system can hide a CPU feature. Truthful positive reports suffice.
[Arm's machine-readable constraints](https://kernel.googlesource.com/pub/scm/linux/kernel/git/maz/AARCHMRS/+/1346b16d47619400448f3cb6d4f22d62d3b76848/Features.json#42185).

RustCrypto's linked Linux probe tests either bit. Rust 1.100 standard detection
additionally requires both bits, SHA1, SHA2 and ASIMD. Both predicates imply
the instructions needed by their respective kernels under these constraints.
[Rust's Linux source](https://github.com/rust-lang/rust/blob/0ef1bc386059596dada8fb65b50425aab2ea637a/library/std_detect/src/detect/os/linux/aarch64.rs#L345-L349).
-/

namespace slhdsa.RcArmCode.Linux
open Aeneas Aeneas.Std Result

/-- Linux elf_hwcap.h assigns SHA2, SHA3 and SHA512 bits 6, 17 and 21.
The release gate checks these masks in the linked detector instructions. -/
def sha256Detected (hwcap : BitVec 64) : Bool := hwcap.getLsbD 6
def sha512Detected (hwcap : BitVec 64) : Bool := (hwcap &&& 0x220000#64) != 0#64

theorem sha512_mask (hwcap : BitVec 64) :
    sha512Detected hwcap = (hwcap.getLsbD 17 || hwcap.getLsbD 21) := by
  have table : ∀ i : Fin 64, (0x220000#64).getLsbD i =
      (decide (i.val = 17) || decide (i.val = 21)) := by decide
  have zero : hwcap &&& 0x220000#64 = 0#64 ↔
      hwcap.getLsbD 17 = false ∧ hwcap.getLsbD 21 = false := by
    constructor
    · intro eq
      constructor
      · have h := congrArg (fun x : BitVec 64 => x.getLsbD 17) eq
        simpa only [BitVec.getLsbD_and, BitVec.getLsbD_zero,
          show (0x220000#64).getLsbD 17 = true by decide, Bool.and_true] using h
      · have h := congrArg (fun x : BitVec 64 => x.getLsbD 21) eq
        simpa only [BitVec.getLsbD_and, BitVec.getLsbD_zero,
          show (0x220000#64).getLsbD 21 = true by decide, Bool.and_true] using h
    · rintro ⟨h17,h21⟩
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_and, BitVec.getLsbD_zero, table ⟨i,hi⟩]
      by_cases a : i = 17
      · subst i; rw [h17]; rfl
      · by_cases b : i = 21
        · subst i; rw [h21]; rfl
        · simp [a,b]
  cases a : hwcap.getLsbD 17 <;> cases b : hwcap.getLsbD 21 <;>
    simp [sha512Detected, zero, a, b] at *
  tauto

/-- A reported capability is available on every CPU on which the process can execute. Arm's machine-readable feature
constraints explicitly require FEAT_SHA3 to imply FEAT_SHA512. -/
theorem sha512_available (hwcap : BitVec 64) (hasSHA3 hasSHA512 : Prop)
    (sha3Reported : hwcap.getLsbD 17 = true → hasSHA3)
    (sha512Reported : hwcap.getLsbD 21 = true → hasSHA512)
    (armArchitecture : hasSHA3 → hasSHA512) (selected : sha512Detected hwcap = true) :
    hasSHA512 := by
  rw [sha512_mask, Bool.or_eq_true] at selected
  exact selected.elim (armArchitecture ∘ sha3Reported) sha512Reported

/-- 255 is uninitialized; first use writes 0 or 1. A cached decision is stable
for the process-wide capability set (including concurrent initial reads). -/
def choose (cache : BitVec 8) (detected : Bool) : Bool :=
  if cache == 1 then true else if cache == 255 then detected else false

def store (detected : Bool) : BitVec 8 := if detected then 1 else 0

theorem cache_choice (detected : Bool) :
    choose 255 detected = detected ∧ choose (store detected) detected = detected := by
  cases detected <;> decide

def selected512 (native : Bool) (st : Array U64 8#usize) (bs : Slice (Array U8 128#usize)) :
    Result (List Spec.SHA512.Word) :=
  if native then ok (S512.execute false (slhdsa.S512.wv st.val) bs.val)
  else do
    let out ← RcSoft.sha512.soft.unroll.compress st bs
    ok (slhdsa.S512.wv out.val)

def selected256 (native : Bool) (st : Array U32 8#usize) (bs : Slice (Array U8 64#usize)) :
    Result (List Spec.SHA256.Word) :=
  if native then ok (execute false (wv st.val) bs.val)
  else do
    let out ← RcSoft256.sha256.soft.unroll.compress st bs
    ok (wv out.val)

theorem selected512_is_fips (cache : BitVec 8) (hwcap : BitVec 64) (st : Array U64 8#usize)
    (bs : Slice (Array U8 128#usize)) :
    selected512 (choose cache (sha512Detected hwcap)) st bs ⦃ out =>
       out = X86.Stream.fold512 (slhdsa.S512.wv st.val) bs.val ⦄ := by
  unfold selected512
  split
  · exact (WP.spec_ok _).mpr (S512.execute_is_fips false bs.val _)
  · apply WP.spec_bind (RcSoftProof.execute_is_fips st bs)
    intro _ eq; exact (WP.spec_ok _).mpr eq

theorem selected256_is_fips (cache : BitVec 8) (hwcap : BitVec 64) (st : Array U32 8#usize)
    (bs : Slice (Array U8 64#usize)) :
    selected256 (choose cache (sha256Detected hwcap)) st bs ⦃ out =>
       out = X86.Stream.fold256 (wv st.val) bs.val ⦄ := by
  unfold selected256
  split
  · exact (WP.spec_ok _).mpr (execute_is_fips false bs.val _ (by simp))
  · apply WP.spec_bind (RcSoft256Proof.execute_is_fips st bs)
    intro _ eq; exact (WP.spec_ok _).mpr eq

/-- The actual cache starts at 255 and may subsequently contain the operating
system's process-wide detection result. Under the architectural ISA rule this
path both has its instruction set and implements the FIPS compressor. -/
theorem dispatch512 (hwcap : BitVec 64) (cache : BitVec 8)
    (reachable : cache = 255 ∨ cache = store (sha512Detected hwcap))
    (hasSHA3 hasSHA512 : Prop) (sha3Reported : hwcap.getLsbD 17 = true → hasSHA3)
    (sha512Reported : hwcap.getLsbD 21 = true → hasSHA512)
    (armArchitecture : hasSHA3 → hasSHA512) (st : Array U64 8#usize) (bs : Slice (Array U8 128#usize)) :
    (choose cache (sha512Detected hwcap) = true → hasSHA512) ∧
      (selected512 (choose cache (sha512Detected hwcap)) st bs ⦃ out =>
        out = X86.Stream.fold512 (slhdsa.S512.wv st.val) bs.val ⦄) := by
  refine ⟨?_, selected512_is_fips _ _ _ _⟩
  have decision := cache_choice (sha512Detected hwcap)
  rcases reachable with rfl | rfl <;>
    simpa only [decision.1, decision.2] using
      sha512_available hwcap hasSHA3 hasSHA512 sha3Reported sha512Reported armArchitecture

theorem dispatch256 (hwcap : BitVec 64) (cache : BitVec 8)
    (reachable : cache = 255 ∨ cache = store (sha256Detected hwcap)) (hasSHA256 : Prop)
    (reported : hwcap.getLsbD 6 = true → hasSHA256) (st : Array U32 8#usize) (bs : Slice (Array U8 64#usize)) :
    (choose cache (sha256Detected hwcap) = true → hasSHA256) ∧
      (selected256 (choose cache (sha256Detected hwcap)) st bs ⦃ out =>
        out = X86.Stream.fold256 (wv st.val) bs.val ⦄) := by
  refine ⟨?_, selected256_is_fips _ _ _ _⟩
  have decision := cache_choice (sha256Detected hwcap)
  rcases reachable with rfl | rfl
  · rw [decision.1]; exact reported
  · rw [decision.2]; exact reported

-- Explicit regression cases for no flags, each reported flag separately and both.
example : ([0, 0x20000, 0x200000, 0x220000] : List (BitVec 64)).map sha512Detected =
    [false, true, true, true] := by decide

end slhdsa.RcArmCode.Linux

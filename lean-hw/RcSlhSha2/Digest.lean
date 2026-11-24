import RcSlhSha2.Initial
import Rcarmcode.Proof512
import Rcarmcode.Proof
import Spec.Correctness

namespace slhdsa.RcSlhSha2
open Spec

/-- The two branches in block-buffer's digest_pad. An exhausted last block is
compressed before a new zero block receives the length field. -/
def padded (bs suffix : Nat) (m : Bytes) : Bytes :=
  let pos := m.length % bs
  let free := bs - pos - 1
  let zeros := if free < suffix then free + (bs - suffix) else free - suffix
  let bitLength := 8 * (pos + bs * (m.length / bs))
  m ++ [0x80#8] ++ List.replicate zeros 0#8 ++ toByte bitLength suffix

theorem padded256 (m : Bytes) : padded 64 8 m = SHA256.pad m := by
  simp only [padded, SHA256.pad]
  rw [Nat.mod_add_div]
  have h : (if 64 - m.length%64 - 1 < 8 then 64 - m.length%64 - 1 + (64-8)
    else 64 - m.length%64 - 1 - 8) = (119 - m.length%64) % 64 := by split <;> omega
  rw [h]

theorem padded512 (m : Bytes) : padded 128 16 m = SHA512.pad m := by
  simp only [padded, SHA512.pad]
  rw [Nat.mod_add_div]
  have h : (if 128 - m.length%128 - 1 < 16 then 128 - m.length%128 - 1 + (128-16)
    else 128 - m.length%128 - 1 - 16) = (239 - m.length%128) % 128 := by split <;> omega
  rw [h]

/-- Decode input words and run the released RustCrypto Arm compression circuit
whose instructions, constants and register mapping are checked separately. -/
def native256 (st : List SHA256.Word) (b : Bytes) :=
  RcArmCode.writeState (RcArmCode.linux RcArmCode.linuxConstants (vOf st 0) (vOf st 4)
    (beV b 0) (beV b 16) (beV b 32) (beV b 48))

def native512 (st : List SHA512.Word) (b : Bytes) :=
  RcArmCode.S512.writeState (RcArmCode.S512.linux (fun _ => Arm.ADD2) RcArmCode.S512.linuxConstants
    (H512.vOf2 st 0) (H512.vOf2 st 2) (H512.vOf2 st 4) (H512.vOf2 st 6)
    (H512.beV2 b 0) (H512.beV2 b 16) (H512.beV2 b 32) (H512.beV2 b 48)
    (H512.beV2 b 64) (H512.beV2 b 80) (H512.beV2 b 96) (H512.beV2 b 112))

attribute [local irreducible] RcArmCode.linux RcArmCode.S512.linux kcompress H512.kcompress

theorem native256_spec (st : List SHA256.Word) (b : Bytes) (s : st.length = 8) (len : b.length=64) :
    native256 st b = SHA256.compress st b := by
  unfold native256; rw [RcArmCode.linux_registers]
  exact kcompress_eq st s b len

theorem native512_spec (st : List SHA512.Word) (b : Bytes) :
    native512 st b = SHA512.compress st b := by
  unfold native512; rw [RcArmCode.S512.linux_registers]; exact H512.kcompress_eq st b

attribute [local irreducible] native256 native512 SHA256.compress SHA512.compress

def digest256 (m : Bytes) : Bytes :=
  let p := padded 64 8 m
  let s := (List.range (p.length / 64)).foldl (fun st k => native256 st (SHA256.blockAt p k)) initial256
  s.flatMap fun w => toByte w.toNat 4

def digest512 (m : Bytes) : Bytes :=
  let p := padded 128 16 m
  let s := (List.range (p.length / 128)).foldl (fun st k => native512 st (SHA512.blockAt p k)) initial512
  s.flatMap fun w => toByte w.toNat 8

private theorem fold_agrees {A I : Type} (f g : A → I → A) (valid : A → Prop)
    (allowed : I → Prop) (step : ∀ a i, valid a → allowed i → f a i = g a i)
    (keep : ∀ a i, valid (g a i)) (ids : List I) (good : ∀ i ∈ ids, allowed i)
    (st : A) (hs : valid st) : ids.foldl f st = ids.foldl g st := by
  induction ids generalizing st with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldl_cons, step st i hs (good i (by simp))]
    exact ih (fun j hj => good j (List.mem_cons_of_mem _ hj)) _ (keep _ _)

private theorem fold256 (p : Bytes) (ids : List Nat) (good : ∀ i ∈ ids, i < p.length/64)
    (st : List SHA256.Word) (s : st.length = 8) :
    ids.foldl (fun a i => native256 a (SHA256.blockAt p i)) st =
      ids.foldl (fun a i => SHA256.compress a (SHA256.blockAt p i)) st :=
  @fold_agrees (List SHA256.Word) Nat (fun a i => native256 a (SHA256.blockAt p i))
    (fun a i => SHA256.compress a (SHA256.blockAt p i)) (fun a => a.length = 8)
    (fun i => i < p.length / 64)
    (fun a i size idx => native256_spec a _ size (by simp [SHA256.blockAt]; omega))
    (fun a i => compress_length a (SHA256.blockAt p i)) ids good st s

private theorem iv_length : SHA256.H0.length = 8 := rfl

attribute [local irreducible] SHA256.pad SHA512.pad SHA256.blockAt SHA512.blockAt SHA256.H0 SHA512.H0
  padded toByte

theorem digest256_eq : digest256 = sha256 := by
  funext m
  unfold digest256 SHA256.sha256
  rw [padded256, initial256_eq]
  exact congrArg (fun s : List SHA256.Word => s.flatMap (fun w => toByte w.toNat 4))
    (fold256 (SHA256.pad m) (List.range ((SHA256.pad m).length/64))
      (fun _ h => List.mem_range.mp h) SHA256.H0 iv_length)

theorem digest512_eq : digest512 = sha512 := by
  funext m
  unfold digest512 SHA512.sha512
  simp only [padded512,initial512_eq,native512_spec]

end slhdsa.RcSlhSha2

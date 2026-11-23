import X86key.Top
import Slhdsa.Proofs.Sets
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Key

namespace sha2_128s
private theorem params_eq : paramsOf X86KeyRust.sets.sha2_128s.params.PARAMS = sets.sha2_128s.params.PARAMS := by
  with_unfolding_all rfl

theorem keygen_fips (seeds : Array U8 48#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize) :
    X86KeyRust.sets.sha2_128s.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val,bytes r.2.val) = Spec.slhKeygenInternal Spec.sha2_128s
        (Spec.block Spec.sha2_128s (bytes seeds.val) 0) (Spec.block Spec.sha2_128s (bytes seeds.val) 1)
        (Spec.block Spec.sha2_128s (bytes seeds.val) 2) ⦄ := by
  have hp : PN (paramsOf X86KeyRust.sets.sha2_128s.params.PARAMS) 16#usize := params_eq ▸ slhdsa.sha2_128s.pn
  have eq : X86KeyRust.sets.sha2_128s.keygen seeds sk pk = sets.sha2_128s.keygen seeds sk pk := by
    unfold X86KeyRust.sets.sha2_128s.keygen sets.sha2_128s.keygen
    simp only [keygen_eq _ hp,params_eq]
  rw [eq]
  exact slhdsa.sha2_128s.keygen_spec _ _ _

theorem public_key_fips (sk : Array U8 64#usize) : X86KeyRust.sets.sha2_128s.public_key sk ⦃ out =>
    bytes out.val=Spec.skPk Spec.sha2_128s (bytes sk.val) ⦄ := slhdsa.sha2_128s.public_key_spec sk
end sha2_128s

namespace sha2_128f
private theorem params_eq : paramsOf X86KeyRust.sets.sha2_128f.params.PARAMS = sets.sha2_128f.params.PARAMS := by
  with_unfolding_all rfl

theorem keygen_fips (seeds : Array U8 48#usize) (sk : Array U8 64#usize) (pk : Array U8 32#usize) :
    X86KeyRust.sets.sha2_128f.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val,bytes r.2.val) = Spec.slhKeygenInternal Spec.sha2_128f
        (Spec.block Spec.sha2_128f (bytes seeds.val) 0) (Spec.block Spec.sha2_128f (bytes seeds.val) 1)
        (Spec.block Spec.sha2_128f (bytes seeds.val) 2) ⦄ := by
  have hp : PN (paramsOf X86KeyRust.sets.sha2_128f.params.PARAMS) 16#usize := params_eq ▸ slhdsa.sha2_128f.pn
  have eq : X86KeyRust.sets.sha2_128f.keygen seeds sk pk = sets.sha2_128f.keygen seeds sk pk := by
    unfold X86KeyRust.sets.sha2_128f.keygen sets.sha2_128f.keygen
    simp only [keygen_eq _ hp,params_eq]
  rw [eq]
  exact slhdsa.sha2_128f.keygen_spec _ _ _

theorem public_key_fips (sk : Array U8 64#usize) : X86KeyRust.sets.sha2_128f.public_key sk ⦃ out =>
    bytes out.val=Spec.skPk Spec.sha2_128f (bytes sk.val) ⦄ := slhdsa.sha2_128f.public_key_spec sk
end sha2_128f

namespace sha2_192s
private theorem params_eq : paramsOf X86KeyRust.sets.sha2_192s.params.PARAMS = sets.sha2_192s.params.PARAMS := by
  with_unfolding_all rfl

theorem keygen_fips (seeds : Array U8 72#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize) :
    X86KeyRust.sets.sha2_192s.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val,bytes r.2.val) = Spec.slhKeygenInternal Spec.sha2_192s
        (Spec.block Spec.sha2_192s (bytes seeds.val) 0) (Spec.block Spec.sha2_192s (bytes seeds.val) 1)
        (Spec.block Spec.sha2_192s (bytes seeds.val) 2) ⦄ := by
  have hp : PN (paramsOf X86KeyRust.sets.sha2_192s.params.PARAMS) 24#usize := params_eq ▸ slhdsa.sha2_192s.pn
  have eq : X86KeyRust.sets.sha2_192s.keygen seeds sk pk = sets.sha2_192s.keygen seeds sk pk := by
    unfold X86KeyRust.sets.sha2_192s.keygen sets.sha2_192s.keygen
    simp only [keygen_eq _ hp,params_eq]
  rw [eq]
  exact slhdsa.sha2_192s.keygen_spec _ _ _

theorem public_key_fips (sk : Array U8 96#usize) : X86KeyRust.sets.sha2_192s.public_key sk ⦃ out =>
    bytes out.val=Spec.skPk Spec.sha2_192s (bytes sk.val) ⦄ := slhdsa.sha2_192s.public_key_spec sk
end sha2_192s

namespace sha2_192f
private theorem params_eq : paramsOf X86KeyRust.sets.sha2_192f.params.PARAMS = sets.sha2_192f.params.PARAMS := by
  with_unfolding_all rfl

theorem keygen_fips (seeds : Array U8 72#usize) (sk : Array U8 96#usize) (pk : Array U8 48#usize) :
    X86KeyRust.sets.sha2_192f.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val,bytes r.2.val) = Spec.slhKeygenInternal Spec.sha2_192f
        (Spec.block Spec.sha2_192f (bytes seeds.val) 0) (Spec.block Spec.sha2_192f (bytes seeds.val) 1)
        (Spec.block Spec.sha2_192f (bytes seeds.val) 2) ⦄ := by
  have hp : PN (paramsOf X86KeyRust.sets.sha2_192f.params.PARAMS) 24#usize := params_eq ▸ slhdsa.sha2_192f.pn
  have eq : X86KeyRust.sets.sha2_192f.keygen seeds sk pk = sets.sha2_192f.keygen seeds sk pk := by
    unfold X86KeyRust.sets.sha2_192f.keygen sets.sha2_192f.keygen
    simp only [keygen_eq _ hp,params_eq]
  rw [eq]
  exact slhdsa.sha2_192f.keygen_spec _ _ _

theorem public_key_fips (sk : Array U8 96#usize) : X86KeyRust.sets.sha2_192f.public_key sk ⦃ out =>
    bytes out.val=Spec.skPk Spec.sha2_192f (bytes sk.val) ⦄ := slhdsa.sha2_192f.public_key_spec sk
end sha2_192f

namespace sha2_256s
private theorem params_eq : paramsOf X86KeyRust.sets.sha2_256s.params.PARAMS = sets.sha2_256s.params.PARAMS := by
  with_unfolding_all rfl

theorem keygen_fips (seeds : Array U8 96#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize) :
    X86KeyRust.sets.sha2_256s.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val,bytes r.2.val) = Spec.slhKeygenInternal Spec.sha2_256s
        (Spec.block Spec.sha2_256s (bytes seeds.val) 0) (Spec.block Spec.sha2_256s (bytes seeds.val) 1)
        (Spec.block Spec.sha2_256s (bytes seeds.val) 2) ⦄ := by
  have hp : PN (paramsOf X86KeyRust.sets.sha2_256s.params.PARAMS) 32#usize := params_eq ▸ slhdsa.sha2_256s.pn
  have eq : X86KeyRust.sets.sha2_256s.keygen seeds sk pk = sets.sha2_256s.keygen seeds sk pk := by
    unfold X86KeyRust.sets.sha2_256s.keygen sets.sha2_256s.keygen
    simp only [keygen_eq _ hp,params_eq]
  rw [eq]
  exact slhdsa.sha2_256s.keygen_spec _ _ _

theorem public_key_fips (sk : Array U8 128#usize) : X86KeyRust.sets.sha2_256s.public_key sk ⦃ out =>
    bytes out.val=Spec.skPk Spec.sha2_256s (bytes sk.val) ⦄ := slhdsa.sha2_256s.public_key_spec sk
end sha2_256s

namespace sha2_256f
private theorem params_eq : paramsOf X86KeyRust.sets.sha2_256f.params.PARAMS = sets.sha2_256f.params.PARAMS := by
  with_unfolding_all rfl

theorem keygen_fips (seeds : Array U8 96#usize) (sk : Array U8 128#usize) (pk : Array U8 64#usize) :
    X86KeyRust.sets.sha2_256f.keygen seeds sk pk ⦃ r =>
      (bytes r.1.val,bytes r.2.val) = Spec.slhKeygenInternal Spec.sha2_256f
        (Spec.block Spec.sha2_256f (bytes seeds.val) 0) (Spec.block Spec.sha2_256f (bytes seeds.val) 1)
        (Spec.block Spec.sha2_256f (bytes seeds.val) 2) ⦄ := by
  have hp : PN (paramsOf X86KeyRust.sets.sha2_256f.params.PARAMS) 32#usize := params_eq ▸ slhdsa.sha2_256f.pn
  have eq : X86KeyRust.sets.sha2_256f.keygen seeds sk pk = sets.sha2_256f.keygen seeds sk pk := by
    unfold X86KeyRust.sets.sha2_256f.keygen sets.sha2_256f.keygen
    simp only [keygen_eq _ hp,params_eq]
  rw [eq]
  exact slhdsa.sha2_256f.keygen_spec _ _ _

theorem public_key_fips (sk : Array U8 128#usize) : X86KeyRust.sets.sha2_256f.public_key sk ⦃ out =>
    bytes out.val=Spec.skPk Spec.sha2_256f (bytes sk.val) ⦄ := slhdsa.sha2_256f.public_key_spec sk
end sha2_256f
end slhdsa.X86.Key

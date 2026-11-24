import Spec.ArmSha2PublicSign
import Spec.AppleSha2InternalSignerWitness
import Spec.AppleSegmentedFrameWitness
namespace LinkedAppleSha2PublicSign
open Spec.ArmSha2PublicSign
set_option maxRecDepth 65536
set_option maxHeartbeats 0
def dispatch16 : Array Nat := #[0xd101c3ff,0xa9035ff8,0xa90457f6,0xa9054ff4,0xa9067bfd,0x910183fd,0xf103fc9f,0x54000089,
0x92800009,0xf9000109,0x14000025,0xf10ffc5f,0x540000e9,0xa9467bfd,0xa9454ff4,0xa94457f6,
0xa9435ff8,0x9101c3ff,0x17ffc8a4,0xaa0803f8,0x910003e8,0xaa0003f4,0xaa0103e0,0xaa0203e1,
0xaa0303e2,0xaa0403e3,0xaa0703f5,0xaa0603f6,0xaa0503f7,0x94000830,0xa9408bf3,0x910063e8,
0xaa1403e0,0xaa1303e1,0xaa1703e3,0xaa1603e4,0xaa1503e5,0x97fff8ce,0x3cc183e0,0x3d800300,
0xf94017e8,0xf9000b08,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,0x97fea5f7,0xa9467bfd,
0xa9454ff4,0xa94457f6,0xa9435ff8,0x9101c3ff,0xd65f03c0,0xaa0003f4,0xf94003e1,0xb4000081,
0xaa1303e0,0x52800022,0x97fea5eb,0xaa1403e0,0x94016198]
def sha2_128s_sign : Image := ⟨Spec.sha2_128s.n,false,0x100076aa4,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0xf0000320,0x910ac000,
0x52800806,0x1400143b],0x10007bbb4,dispatch16,LinkedSha2InternalSigner.sha2_128s.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_128s.body,LinkedSegmentedFrame.sha2_128s.entry,0x100025448⟩
theorem sha2_128s_sign_checked (valid short : Bool) : run sha2_128s_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_128s_slh_sign : Image := ⟨Spec.sha2_128s.n,false,0x100076b38,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0xf0000320,0x910ac000,
0x52800806,0x14001416],0x10007bbb4,dispatch16,LinkedSha2InternalSigner.sha2_128s.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_128s.body,LinkedSegmentedFrame.sha2_128s.entry,0x100025448⟩
theorem sha2_128s_slh_sign_checked (valid short : Bool) : run sha2_128s_slh_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_128s_sign_deterministic : Image := ⟨Spec.sha2_128s.n,true,0x1000769c4,#[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,
0x3dc008a0,0x3d8003e0,0xf0000320,0x910ac000,0x910003e7,0x52800806,0x9400146e,0xa9417bfd,
0x910083ff,0xd65f03c0],0x10007bbb4,dispatch16,LinkedSha2InternalSigner.sha2_128s.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_128s.body,LinkedSegmentedFrame.sha2_128s.entry,0x100025448⟩
theorem sha2_128s_sign_deterministic_checked (valid short : Bool) : run sha2_128s_sign_deterministic valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_128f_sign : Image := ⟨Spec.sha2_128f.n,false,0x1000793d4,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0x90000320,0x910ec000,
0x52800806,0x140009ef],0x10007bbb4,dispatch16,LinkedSha2InternalSigner.sha2_128f.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_128f.body,LinkedSegmentedFrame.sha2_128f.entry,0x100025448⟩
theorem sha2_128f_sign_checked (valid short : Bool) : run sha2_128f_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_128f_slh_sign : Image := ⟨Spec.sha2_128f.n,false,0x100079468,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0x90000320,0x910ec000,
0x52800806,0x140009ca],0x10007bbb4,dispatch16,LinkedSha2InternalSigner.sha2_128f.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_128f.body,LinkedSegmentedFrame.sha2_128f.entry,0x100025448⟩
theorem sha2_128f_slh_sign_checked (valid short : Bool) : run sha2_128f_slh_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_128f_sign_deterministic : Image := ⟨Spec.sha2_128f.n,true,0x1000792f4,#[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,
0x3dc008a0,0x3d8003e0,0x90000320,0x910ec000,0x910003e7,0x52800806,0x94000a22,0xa9417bfd,
0x910083ff,0xd65f03c0],0x10007bbb4,dispatch16,LinkedSha2InternalSigner.sha2_128f.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_128f.body,LinkedSegmentedFrame.sha2_128f.entry,0x100025448⟩
theorem sha2_128f_sign_deterministic_checked (valid short : Bool) : run sha2_128f_sign_deterministic valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def dispatch24 : Array Nat := #[0xd101c3ff,0xa9035ff8,0xa90457f6,0xa9054ff4,0xa9067bfd,0x910183fd,0xf103fc9f,0x54000089,
0x92800009,0xf9000109,0x14000025,0xf10ffc5f,0x540000e9,0xa9467bfd,0xa9454ff4,0xa94457f6,
0xa9435ff8,0x9101c3ff,0x17ffca4c,0xaa0803f8,0x910003e8,0xaa0003f4,0xaa0103e0,0xaa0203e1,
0xaa0303e2,0xaa0403e3,0xaa0703f5,0xaa0603f6,0xaa0503f7,0x940007f3,0xa9408bf3,0x910063e8,
0xaa1403e0,0xaa1303e1,0xaa1703e3,0xaa1603e4,0xaa1503e5,0x97fff9c8,0x3cc183e0,0x3d800300,
0xf94017e8,0xf9000b08,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,0x97fea5ba,0xa9467bfd,
0xa9454ff4,0xa94457f6,0xa9435ff8,0x9101c3ff,0xd65f03c0,0xaa0003f4,0xf94003e1,0xb4000081,
0xaa1303e0,0x52800022,0x97fea5ae,0xaa1403e0,0x9401615b]
def sha2_192s_sign : Image := ⟨Spec.sha2_192s.n,false,0x10007374c,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0xd0000340,0x91098000,
0x52800c06,0x1400214e],0x10007bca8,dispatch24,LinkedSha2InternalSigner.sha2_192s.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_192s.body,LinkedSegmentedFrame.sha2_192s.entry,0x100025448⟩
theorem sha2_192s_sign_checked (valid short : Bool) : run sha2_192s_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_192s_slh_sign : Image := ⟨Spec.sha2_192s.n,false,0x1000737e0,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0xd0000340,0x91098000,
0x52800c06,0x14002129],0x10007bca8,dispatch24,LinkedSha2InternalSigner.sha2_192s.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_192s.body,LinkedSegmentedFrame.sha2_192s.entry,0x100025448⟩
theorem sha2_192s_slh_sign_checked (valid short : Bool) : run sha2_192s_slh_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_192s_sign_deterministic : Image := ⟨Spec.sha2_192s.n,true,0x10007364c,#[0xd100c3ff,0xa9027bfd,0x910083fd,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,
0x3dc00ca0,0x3d8003e0,0xf94020a9,0xf9000be9,0xd0000340,0x91098000,0x910003e7,0x52800c06,
0x94002187,0xa9427bfd,0x9100c3ff,0xd65f03c0],0x10007bca8,dispatch24,LinkedSha2InternalSigner.sha2_192s.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_192s.body,LinkedSegmentedFrame.sha2_192s.entry,0x100025448⟩
theorem sha2_192s_sign_deterministic_checked (valid short : Bool) : run sha2_192s_sign_deterministic valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_192f_sign : Image := ⟨Spec.sha2_192f.n,false,0x100073528,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0xd0000340,0x9108e000,
0x52800c06,0x140021d7],0x10007bca8,dispatch24,LinkedSha2InternalSigner.sha2_192f.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_192f.body,LinkedSegmentedFrame.sha2_192f.entry,0x100025448⟩
theorem sha2_192f_sign_checked (valid short : Bool) : run sha2_192f_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_192f_slh_sign : Image := ⟨Spec.sha2_192f.n,false,0x1000735bc,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0xd0000340,0x9108e000,
0x52800c06,0x140021b2],0x10007bca8,dispatch24,LinkedSha2InternalSigner.sha2_192f.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_192f.body,LinkedSegmentedFrame.sha2_192f.entry,0x100025448⟩
theorem sha2_192f_slh_sign_checked (valid short : Bool) : run sha2_192f_slh_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_192f_sign_deterministic : Image := ⟨Spec.sha2_192f.n,true,0x100073428,#[0xd100c3ff,0xa9027bfd,0x910083fd,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,
0x3dc00ca0,0x3d8003e0,0xf94020a9,0xf9000be9,0xd0000340,0x9108e000,0x910003e7,0x52800c06,
0x94002210,0xa9427bfd,0x9100c3ff,0xd65f03c0],0x10007bca8,dispatch24,LinkedSha2InternalSigner.sha2_192f.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_192f.body,LinkedSegmentedFrame.sha2_192f.entry,0x100025448⟩
theorem sha2_192f_sign_deterministic_checked (valid short : Bool) : run sha2_192f_sign_deterministic valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def dispatch32 : Array Nat := #[0xd101c3ff,0xa9035ff8,0xa90457f6,0xa9054ff4,0xa9067bfd,0x910183fd,0xf103fc9f,0x54000089,
0x92800009,0xf9000109,0x14000025,0xf10ffc5f,0x540000e9,0xa9467bfd,0xa9454ff4,0xa94457f6,
0xa9435ff8,0x9101c3ff,0x17ffcc1b,0xaa0803f8,0x910003e8,0xaa0003f4,0xaa0103e0,0xaa0203e1,
0xaa0303e2,0xaa0403e3,0xaa0703f5,0xaa0603f6,0xaa0503f7,0x940007b6,0xa9408bf3,0x910063e8,
0xaa1403e0,0xaa1303e1,0xaa1703e3,0xaa1603e4,0xaa1503e5,0x97fffa9d,0x3cc183e0,0x3d800300,
0xf94017e8,0xf9000b08,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,0x97fea57d,0xa9467bfd,
0xa9454ff4,0xa94457f6,0xa9435ff8,0x9101c3ff,0xd65f03c0,0xaa0003f4,0xf94003e1,0xb4000081,
0xaa1303e0,0x52800022,0x97fea571,0xaa1403e0,0x9401611e]
def sha2_256s_sign : Image := ⟨Spec.sha2_256s.n,false,0x1000795fc,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0x90000320,0x910e2000,
0x52801006,0x140009df],0x10007bd9c,dispatch32,LinkedSha2InternalSigner.sha2_256s.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_256s.body,LinkedSegmentedFrame.sha2_256s.entry,0x100025448⟩
theorem sha2_256s_sign_checked (valid short : Bool) : run sha2_256s_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_256s_slh_sign : Image := ⟨Spec.sha2_256s.n,false,0x100079690,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0x90000320,0x910e2000,
0x52801006,0x140009ba],0x10007bd9c,dispatch32,LinkedSha2InternalSigner.sha2_256s.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_256s.body,LinkedSegmentedFrame.sha2_256s.entry,0x100025448⟩
theorem sha2_256s_slh_sign_checked (valid short : Bool) : run sha2_256s_slh_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_256s_sign_deterministic : Image := ⟨Spec.sha2_256s.n,true,0x1000794f8,#[0xd100c3ff,0xa9027bfd,0x910083fd,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,
0xad4204a0,0xad0007e0,0x90000320,0x910e2000,0x910003e7,0x52801006,0x94000a1b,0xa9427bfd,
0x9100c3ff,0xd65f03c0],0x10007bd9c,dispatch32,LinkedSha2InternalSigner.sha2_256s.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_256s.body,LinkedSegmentedFrame.sha2_256s.entry,0x100025448⟩
theorem sha2_256s_sign_deterministic_checked (valid short : Bool) : run sha2_256s_sign_deterministic valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_256f_sign : Image := ⟨Spec.sha2_256f.n,false,0x10007dfb0,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0x90000300,0x91126000,
0x52801006,0x17fff772],0x10007bd9c,dispatch32,LinkedSha2InternalSigner.sha2_256f.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_256f.body,LinkedSegmentedFrame.sha2_256f.entry,0x100025448⟩
theorem sha2_256f_sign_checked (valid short : Bool) : run sha2_256f_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_256f_slh_sign : Image := ⟨Spec.sha2_256f.n,false,0x10007e044,#[0xaa0503e7,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,0xf00002e0,0x91126000,
0x52801006,0x17fff74d],0x10007bd9c,dispatch32,LinkedSha2InternalSigner.sha2_256f.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_256f.body,LinkedSegmentedFrame.sha2_256f.entry,0x100025448⟩
theorem sha2_256f_slh_sign_checked (valid short : Bool) : run sha2_256f_slh_sign valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
def sha2_256f_sign_deterministic : Image := ⟨Spec.sha2_256f.n,true,0x10007deac,#[0xd100c3ff,0xa9027bfd,0x910083fd,0xaa0403e5,0xaa0303e4,0xaa0203e3,0xaa0103e2,0xaa0003e1,
0xad4204a0,0xad0007e0,0x90000300,0x91126000,0x910003e7,0x52801006,0x97fff7ae,0xa9427bfd,
0x9100c3ff,0xd65f03c0],0x10007bd9c,dispatch32,LinkedSha2InternalSigner.sha2_256f.cfg.param,LinkedApplePureFrame.image.entry,LinkedSha2InternalSigner.sha2_256f.body,LinkedSegmentedFrame.sha2_256f.entry,0x100025448⟩
theorem sha2_256f_sign_deterministic_checked (valid short : Bool) : run sha2_256f_sign_deterministic valid short = some (expected valid short) := by
  cases valid <;> cases short <;> decide +kernel
theorem wrongContextCutoff : run {sha2_128s_sign with dispatchWords := sha2_128s_sign.dispatchWords.modify 6 (· ^^^ 1024)} false true ≠
    some (expected false true) := by decide +kernel
theorem wrongMessageCutoff : run {sha2_128s_sign with dispatchWords := sha2_128s_sign.dispatchWords.modify 11 (· ^^^ 1024)} true false ≠
    some (expected true false) := by decide +kernel
theorem wrongSegmentTarget : run {sha2_128s_sign with dispatchWords := sha2_128s_sign.dispatchWords.modify 18 (· ^^^ 1)} true false ≠
    some (expected true false) := by decide +kernel
theorem wrongResult : run {sha2_128s_sign with dispatchWords := sha2_128s_sign.dispatchWords.modify 40 (· ^^^ 1024)} true true ≠
    some (expected true true) := by decide +kernel
theorem wrongSeed : run {sha2_128s_sign_deterministic with words := sha2_128s_sign_deterministic.words.modify 8 (· ^^^ 1024)} true false ≠
    some (expected true false) := by decide +kernel
end LinkedAppleSha2PublicSign

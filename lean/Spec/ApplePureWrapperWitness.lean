import Spec.ArmPureWrapper
import Spec.AppleVerifyBodyWitness
import Spec.AppleInternalSignerWitness
namespace LinkedApplePure
open Spec.ArmPureWrapper
set_option maxHeartbeats 0
set_option maxRecDepth 65536
def shake_128s_verify : Image := ⟨.verify,Spec.shake_128s.n,LinkedAppleVerifyBody.shake_128s_image.gate.param,0x100073254,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x94002a96,
0xa9410bf3,0xd0000340,0x91084000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800406,
0x94002816,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97fec85f,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97fec853,0xaa1403e0,0x94018400
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_128s_image.body,0x100025448⟩
theorem shake_128s_verify_valid : run shake_128s_verify true = some .forwarded := by decide +kernel
theorem shake_128s_verify_long : run shake_128s_verify false = some .rejected := by decide +kernel
theorem shake_128s_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_128s_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_128s_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_128s f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_128s msg sig ctx pk :=
  verify_eq shake_128s_verify_valid shake_128s_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_128s_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_128s m sig pk) f.payload_eq))
theorem shake_128s_verify_malformed {msg ctx sig pk r} (pub : execute shake_128s_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_128s.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_128s msg sig ctx pk :=
  verify_eq shake_128s_verify_valid shake_128s_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_128s_malformed _ _ _ fits bad).eq_spec)
def shake_128s_slh_verify : Image := ⟨.verify,Spec.shake_128s.n,LinkedAppleVerifyBody.shake_128s_image.gate.param,0x100072f50,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x94002b57,
0xa9410bf3,0xf0000340,0x91084000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800406,
0x940028d7,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97fec920,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97fec914,0xaa1403e0,0x940184c1
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_128s_image.body,0x100025448⟩
theorem shake_128s_slh_verify_valid : run shake_128s_slh_verify true = some .forwarded := by decide +kernel
theorem shake_128s_slh_verify_long : run shake_128s_slh_verify false = some .rejected := by decide +kernel
theorem shake_128s_slh_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_128s_slh_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_128s_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_128s f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_128s msg sig ctx pk :=
  verify_eq shake_128s_slh_verify_valid shake_128s_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_128s_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_128s m sig pk) f.payload_eq))
theorem shake_128s_slh_verify_malformed {msg ctx sig pk r} (pub : execute shake_128s_slh_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_128s.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_128s msg sig ctx pk :=
  verify_eq shake_128s_slh_verify_valid shake_128s_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_128s_malformed _ _ _ fits bad).eq_spec)
def shake_128s_sign : Image := ⟨.sign,Spec.shake_128s.n,LinkedInternalSigner.shake_128s.cfg.param,0x100073178,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x94002ace,0xa9408bf3,
0xd0000340,0x91084000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52800804,0xaa1603e5,0x9400232f,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97fec894,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97fec889,0xaa1403e0,0x94018436
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_128s.body,0x100025448⟩
theorem shake_128s_sign_valid : run shake_128s_sign true = some .forwarded := by decide +kernel
theorem shake_128s_sign_long : run shake_128s_sign false = some .rejected := by decide +kernel
theorem shake_128s_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_128s_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_128s profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_128s f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_128s msg ctx key rand :=
  sign_eq shake_128s_sign_valid shake_128s_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_128s_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_128s m key rand) f.payload_eq))
def shake_128s_slh_sign : Image := ⟨.sign,Spec.shake_128s.n,LinkedInternalSigner.shake_128s.cfg.param,0x100073308,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x94002a6a,0xa9408bf3,
0xd0000340,0x91084000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52800804,0xaa1603e5,0x940022cb,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97fec830,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97fec825,0xaa1403e0,0x940183d2
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_128s.body,0x100025448⟩
theorem shake_128s_slh_sign_valid : run shake_128s_slh_sign true = some .forwarded := by decide +kernel
theorem shake_128s_slh_sign_long : run shake_128s_slh_sign false = some .rejected := by decide +kernel
theorem shake_128s_slh_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_128s_slh_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_128s profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_128s f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_128s msg ctx key rand :=
  sign_eq shake_128s_slh_sign_valid shake_128s_slh_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_128s_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_128s m key rand) f.payload_eq))
def shake_128s_sign_deterministic : Image := ⟨.deterministic,Spec.shake_128s.n,LinkedInternalSigner.shake_128s.cfg.param,0x100073024,#[
0xd101c3ff,0xa90457f6,0xa9054ff4,0xa9067bfd,0x910183fd,0xaa0803f4,0x3dc00880,0x3d8003e0,
0xf103fc7f,0x54000089,0x92800008,0xf9000288,0x14000016,0xaa0403f5,0x910043e8,0x94002b22,
0xa9418bf3,0xd0000340,0x91084000,0x9100a3e8,0x910003e5,0xaa1303e1,0xaa1503e3,0x52800804,
0x94002383,0x3cc283e0,0x3d800280,0xf9401fe8,0xf9000a88,0xf9400be1,0xb4000081,0xaa1303e0,
0x52800022,0x97fec8e8,0xa9467bfd,0xa9454ff4,0xa94457f6,0x9101c3ff,0xd65f03c0,0xaa0003f4,
0xf9400be1,0xb4000081,0xaa1303e0,0x52800022,0x97fec8dd,0xaa1403e0,0x9401848a
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_128s.body,0x100025448⟩
theorem shake_128s_sign_deterministic_valid : run shake_128s_sign_deterministic true = some .forwarded := by decide +kernel
theorem shake_128s_sign_deterministic_long : run shake_128s_sign_deterministic false = some .rejected := by decide +kernel
theorem shake_128s_sign_deterministic_eq {msg ctx key out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_128s_sign_deterministic ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_128s profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_128s f.payload key (Spec.block Spec.shake_128s key 2)) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_128s msg ctx key (Spec.block Spec.shake_128s key 2) :=
  sign_eq shake_128s_sign_deterministic_valid shake_128s_sign_deterministic_long pub (fun _ =>
    (LinkedInternalSigner.shake_128s_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_128s m key (Spec.block Spec.shake_128s key 2)) f.payload_eq))
def shake_128f_verify : Image := ⟨.verify,Spec.shake_128f.n,LinkedAppleVerifyBody.shake_128f_image.gate.param,0x100072de4,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x94002bb2,
0xa9410bf3,0xf0000340,0x9107a000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800406,
0x94002932,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97fec97b,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97fec96f,0xaa1403e0,0x9401851c
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_128f_image.body,0x100025448⟩
theorem shake_128f_verify_valid : run shake_128f_verify true = some .forwarded := by decide +kernel
theorem shake_128f_verify_long : run shake_128f_verify false = some .rejected := by decide +kernel
theorem shake_128f_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_128f_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_128f_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_128f f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_128f msg sig ctx pk :=
  verify_eq shake_128f_verify_valid shake_128f_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_128f_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_128f m sig pk) f.payload_eq))
theorem shake_128f_verify_malformed {msg ctx sig pk r} (pub : execute shake_128f_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_128f.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_128f msg sig ctx pk :=
  verify_eq shake_128f_verify_valid shake_128f_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_128f_malformed _ _ _ fits bad).eq_spec)
def shake_128f_slh_verify : Image := ⟨.verify,Spec.shake_128f.n,LinkedAppleVerifyBody.shake_128f_image.gate.param,0x100072ae0,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x94002c73,
0xa9410bf3,0xf0000340,0x9107a000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800406,
0x940029f3,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97feca3c,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97feca30,0xaa1403e0,0x940185dd
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_128f_image.body,0x100025448⟩
theorem shake_128f_slh_verify_valid : run shake_128f_slh_verify true = some .forwarded := by decide +kernel
theorem shake_128f_slh_verify_long : run shake_128f_slh_verify false = some .rejected := by decide +kernel
theorem shake_128f_slh_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_128f_slh_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_128f_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_128f f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_128f msg sig ctx pk :=
  verify_eq shake_128f_slh_verify_valid shake_128f_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_128f_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_128f m sig pk) f.payload_eq))
theorem shake_128f_slh_verify_malformed {msg ctx sig pk r} (pub : execute shake_128f_slh_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_128f.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_128f msg sig ctx pk :=
  verify_eq shake_128f_slh_verify_valid shake_128f_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_128f_malformed _ _ _ fits bad).eq_spec)
def shake_128f_sign : Image := ⟨.sign,Spec.shake_128f.n,LinkedInternalSigner.shake_128f.cfg.param,0x100072d08,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x94002bea,0xa9408bf3,
0xf0000340,0x9107a000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52800804,0xaa1603e5,0x9400244b,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97fec9b0,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97fec9a5,0xaa1403e0,0x94018552
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_128f.body,0x100025448⟩
theorem shake_128f_sign_valid : run shake_128f_sign true = some .forwarded := by decide +kernel
theorem shake_128f_sign_long : run shake_128f_sign false = some .rejected := by decide +kernel
theorem shake_128f_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_128f_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_128f profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_128f f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_128f msg ctx key rand :=
  sign_eq shake_128f_sign_valid shake_128f_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_128f_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_128f m key rand) f.payload_eq))
def shake_128f_slh_sign : Image := ⟨.sign,Spec.shake_128f.n,LinkedInternalSigner.shake_128f.cfg.param,0x100072e98,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x94002b86,0xa9408bf3,
0xf0000340,0x9107a000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52800804,0xaa1603e5,0x940023e7,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97fec94c,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97fec941,0xaa1403e0,0x940184ee
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_128f.body,0x100025448⟩
theorem shake_128f_slh_sign_valid : run shake_128f_slh_sign true = some .forwarded := by decide +kernel
theorem shake_128f_slh_sign_long : run shake_128f_slh_sign false = some .rejected := by decide +kernel
theorem shake_128f_slh_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_128f_slh_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_128f profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_128f f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_128f msg ctx key rand :=
  sign_eq shake_128f_slh_sign_valid shake_128f_slh_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_128f_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_128f m key rand) f.payload_eq))
def shake_128f_sign_deterministic : Image := ⟨.deterministic,Spec.shake_128f.n,LinkedInternalSigner.shake_128f.cfg.param,0x100072bb4,#[
0xd101c3ff,0xa90457f6,0xa9054ff4,0xa9067bfd,0x910183fd,0xaa0803f4,0x3dc00880,0x3d8003e0,
0xf103fc7f,0x54000089,0x92800008,0xf9000288,0x14000016,0xaa0403f5,0x910043e8,0x94002c3e,
0xa9418bf3,0xf0000340,0x9107a000,0x9100a3e8,0x910003e5,0xaa1303e1,0xaa1503e3,0x52800804,
0x9400249f,0x3cc283e0,0x3d800280,0xf9401fe8,0xf9000a88,0xf9400be1,0xb4000081,0xaa1303e0,
0x52800022,0x97feca04,0xa9467bfd,0xa9454ff4,0xa94457f6,0x9101c3ff,0xd65f03c0,0xaa0003f4,
0xf9400be1,0xb4000081,0xaa1303e0,0x52800022,0x97fec9f9,0xaa1403e0,0x940185a6
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_128f.body,0x100025448⟩
theorem shake_128f_sign_deterministic_valid : run shake_128f_sign_deterministic true = some .forwarded := by decide +kernel
theorem shake_128f_sign_deterministic_long : run shake_128f_sign_deterministic false = some .rejected := by decide +kernel
theorem shake_128f_sign_deterministic_eq {msg ctx key out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_128f_sign_deterministic ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_128f profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_128f f.payload key (Spec.block Spec.shake_128f key 2)) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_128f msg ctx key (Spec.block Spec.shake_128f key 2) :=
  sign_eq shake_128f_sign_deterministic_valid shake_128f_sign_deterministic_long pub (fun _ =>
    (LinkedInternalSigner.shake_128f_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_128f m key (Spec.block Spec.shake_128f key 2)) f.payload_eq))
def shake_192s_verify : Image := ⟨.verify,Spec.shake_192s.n,LinkedAppleVerifyBody.shake_192s_image.gate.param,0x100078c8c,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x94001408,
0xa9410bf3,0xb0000320,0x910d8000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800606,
0x94001279,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97feb1d1,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97feb1c5,0xaa1403e0,0x94016d72
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_192s_image.body,0x100025448⟩
theorem shake_192s_verify_valid : run shake_192s_verify true = some .forwarded := by decide +kernel
theorem shake_192s_verify_long : run shake_192s_verify false = some .rejected := by decide +kernel
theorem shake_192s_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_192s_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_192s_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_192s f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_192s msg sig ctx pk :=
  verify_eq shake_192s_verify_valid shake_192s_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_192s_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_192s m sig pk) f.payload_eq))
theorem shake_192s_verify_malformed {msg ctx sig pk r} (pub : execute shake_192s_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_192s.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_192s msg sig ctx pk :=
  verify_eq shake_192s_verify_valid shake_192s_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_192s_malformed _ _ _ fits bad).eq_spec)
def shake_192s_slh_verify : Image := ⟨.verify,Spec.shake_192s.n,LinkedAppleVerifyBody.shake_192s_image.gate.param,0x100078968,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x940014d1,
0xa9410bf3,0xb0000320,0x910d8000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800606,
0x94001342,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97feb29a,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97feb28e,0xaa1403e0,0x94016e3b
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_192s_image.body,0x100025448⟩
theorem shake_192s_slh_verify_valid : run shake_192s_slh_verify true = some .forwarded := by decide +kernel
theorem shake_192s_slh_verify_long : run shake_192s_slh_verify false = some .rejected := by decide +kernel
theorem shake_192s_slh_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_192s_slh_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_192s_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_192s f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_192s msg sig ctx pk :=
  verify_eq shake_192s_slh_verify_valid shake_192s_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_192s_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_192s m sig pk) f.payload_eq))
theorem shake_192s_slh_verify_malformed {msg ctx sig pk r} (pub : execute shake_192s_slh_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_192s.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_192s msg sig ctx pk :=
  verify_eq shake_192s_slh_verify_valid shake_192s_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_192s_malformed _ _ _ fits bad).eq_spec)
def shake_192s_sign : Image := ⟨.sign,Spec.shake_192s.n,LinkedInternalSigner.shake_192s.cfg.param,0x100078bb0,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x94001440,0xa9408bf3,
0xb0000320,0x910d8000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52800c04,0xaa1603e5,0x94000dec,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97feb206,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97feb1fb,0xaa1403e0,0x94016da8
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_192s.body,0x100025448⟩
theorem shake_192s_sign_valid : run shake_192s_sign true = some .forwarded := by decide +kernel
theorem shake_192s_sign_long : run shake_192s_sign false = some .rejected := by decide +kernel
theorem shake_192s_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_192s_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_192s profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_192s f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_192s msg ctx key rand :=
  sign_eq shake_192s_sign_valid shake_192s_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_192s_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_192s m key rand) f.payload_eq))
def shake_192s_slh_sign : Image := ⟨.sign,Spec.shake_192s.n,LinkedInternalSigner.shake_192s.cfg.param,0x100078d40,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x940013dc,0xa9408bf3,
0xb0000320,0x910d8000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52800c04,0xaa1603e5,0x94000d88,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97feb1a2,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97feb197,0xaa1403e0,0x94016d44
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_192s.body,0x100025448⟩
theorem shake_192s_slh_sign_valid : run shake_192s_slh_sign true = some .forwarded := by decide +kernel
theorem shake_192s_slh_sign_long : run shake_192s_slh_sign false = some .rejected := by decide +kernel
theorem shake_192s_slh_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_192s_slh_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_192s profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_192s f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_192s msg ctx key rand :=
  sign_eq shake_192s_slh_sign_valid shake_192s_slh_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_192s_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_192s m key rand) f.payload_eq))
def shake_192s_sign_deterministic : Image := ⟨.deterministic,Spec.shake_192s.n,LinkedInternalSigner.shake_192s.cfg.param,0x100078a3c,#[
0xd10203ff,0xa90557f6,0xa9064ff4,0xa9077bfd,0x9101c3fd,0xaa0803f4,0x3dc00c80,0x3d8003e0,
0xf9402088,0xf9000be8,0xf103fc7f,0x54000089,0x92800008,0xf9000288,0x14000016,0xaa0403f5,
0x910083e8,0x9400149a,0xa9428bf3,0xb0000320,0x910d8000,0x9100e3e8,0x910003e5,0xaa1303e1,
0xaa1503e3,0x52800c04,0x94000e46,0x3cc383e0,0x3d800280,0xf94027e8,0xf9000a88,0xf94013e1,
0xb4000081,0xaa1303e0,0x52800022,0x97feb260,0xa9477bfd,0xa9464ff4,0xa94557f6,0x910203ff,
0xd65f03c0,0xaa0003f4,0xf94013e1,0xb4000081,0xaa1303e0,0x52800022,0x97feb255,0xaa1403e0,
0x94016e02
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_192s.body,0x100025448⟩
theorem shake_192s_sign_deterministic_valid : run shake_192s_sign_deterministic true = some .forwarded := by decide +kernel
theorem shake_192s_sign_deterministic_long : run shake_192s_sign_deterministic false = some .rejected := by decide +kernel
theorem shake_192s_sign_deterministic_eq {msg ctx key out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_192s_sign_deterministic ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_192s profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_192s f.payload key (Spec.block Spec.shake_192s key 2)) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_192s msg ctx key (Spec.block Spec.shake_192s key 2) :=
  sign_eq shake_192s_sign_deterministic_valid shake_192s_sign_deterministic_long pub (fun _ =>
    (LinkedInternalSigner.shake_192s_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_192s m key (Spec.block Spec.shake_192s key 2)) f.payload_eq))
def shake_192f_verify : Image := ⟨.verify,Spec.shake_192f.n,LinkedAppleVerifyBody.shake_192f_image.gate.param,0x1000787fc,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x9400152c,
0xa9410bf3,0xb0000320,0x910ce000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800606,
0x9400139d,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97feb2f5,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97feb2e9,0xaa1403e0,0x94016e96
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_192f_image.body,0x100025448⟩
theorem shake_192f_verify_valid : run shake_192f_verify true = some .forwarded := by decide +kernel
theorem shake_192f_verify_long : run shake_192f_verify false = some .rejected := by decide +kernel
theorem shake_192f_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_192f_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_192f_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_192f f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_192f msg sig ctx pk :=
  verify_eq shake_192f_verify_valid shake_192f_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_192f_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_192f m sig pk) f.payload_eq))
theorem shake_192f_verify_malformed {msg ctx sig pk r} (pub : execute shake_192f_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_192f.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_192f msg sig ctx pk :=
  verify_eq shake_192f_verify_valid shake_192f_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_192f_malformed _ _ _ fits bad).eq_spec)
def shake_192f_slh_verify : Image := ⟨.verify,Spec.shake_192f.n,LinkedAppleVerifyBody.shake_192f_image.gate.param,0x1000784d8,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x940015f5,
0xa9410bf3,0xb0000320,0x910ce000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800606,
0x94001466,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97feb3be,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97feb3b2,0xaa1403e0,0x94016f5f
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_192f_image.body,0x100025448⟩
theorem shake_192f_slh_verify_valid : run shake_192f_slh_verify true = some .forwarded := by decide +kernel
theorem shake_192f_slh_verify_long : run shake_192f_slh_verify false = some .rejected := by decide +kernel
theorem shake_192f_slh_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_192f_slh_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_192f_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_192f f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_192f msg sig ctx pk :=
  verify_eq shake_192f_slh_verify_valid shake_192f_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_192f_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_192f m sig pk) f.payload_eq))
theorem shake_192f_slh_verify_malformed {msg ctx sig pk r} (pub : execute shake_192f_slh_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_192f.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_192f msg sig ctx pk :=
  verify_eq shake_192f_slh_verify_valid shake_192f_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_192f_malformed _ _ _ fits bad).eq_spec)
def shake_192f_sign : Image := ⟨.sign,Spec.shake_192f.n,LinkedInternalSigner.shake_192f.cfg.param,0x100078720,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x94001564,0xa9408bf3,
0xb0000320,0x910ce000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52800c04,0xaa1603e5,0x94000f10,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97feb32a,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97feb31f,0xaa1403e0,0x94016ecc
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_192f.body,0x100025448⟩
theorem shake_192f_sign_valid : run shake_192f_sign true = some .forwarded := by decide +kernel
theorem shake_192f_sign_long : run shake_192f_sign false = some .rejected := by decide +kernel
theorem shake_192f_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_192f_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_192f profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_192f f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_192f msg ctx key rand :=
  sign_eq shake_192f_sign_valid shake_192f_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_192f_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_192f m key rand) f.payload_eq))
def shake_192f_slh_sign : Image := ⟨.sign,Spec.shake_192f.n,LinkedInternalSigner.shake_192f.cfg.param,0x1000788b0,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x94001500,0xa9408bf3,
0xb0000320,0x910ce000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52800c04,0xaa1603e5,0x94000eac,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97feb2c6,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97feb2bb,0xaa1403e0,0x94016e68
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_192f.body,0x100025448⟩
theorem shake_192f_slh_sign_valid : run shake_192f_slh_sign true = some .forwarded := by decide +kernel
theorem shake_192f_slh_sign_long : run shake_192f_slh_sign false = some .rejected := by decide +kernel
theorem shake_192f_slh_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_192f_slh_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_192f profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_192f f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_192f msg ctx key rand :=
  sign_eq shake_192f_slh_sign_valid shake_192f_slh_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_192f_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_192f m key rand) f.payload_eq))
def shake_192f_sign_deterministic : Image := ⟨.deterministic,Spec.shake_192f.n,LinkedInternalSigner.shake_192f.cfg.param,0x1000785ac,#[
0xd10203ff,0xa90557f6,0xa9064ff4,0xa9077bfd,0x9101c3fd,0xaa0803f4,0x3dc00c80,0x3d8003e0,
0xf9402088,0xf9000be8,0xf103fc7f,0x54000089,0x92800008,0xf9000288,0x14000016,0xaa0403f5,
0x910083e8,0x940015be,0xa9428bf3,0xb0000320,0x910ce000,0x9100e3e8,0x910003e5,0xaa1303e1,
0xaa1503e3,0x52800c04,0x94000f6a,0x3cc383e0,0x3d800280,0xf94027e8,0xf9000a88,0xf94013e1,
0xb4000081,0xaa1303e0,0x52800022,0x97feb384,0xa9477bfd,0xa9464ff4,0xa94557f6,0x910203ff,
0xd65f03c0,0xaa0003f4,0xf94013e1,0xb4000081,0xaa1303e0,0x52800022,0x97feb379,0xaa1403e0,
0x94016f26
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_192f.body,0x100025448⟩
theorem shake_192f_sign_deterministic_valid : run shake_192f_sign_deterministic true = some .forwarded := by decide +kernel
theorem shake_192f_sign_deterministic_long : run shake_192f_sign_deterministic false = some .rejected := by decide +kernel
theorem shake_192f_sign_deterministic_eq {msg ctx key out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_192f_sign_deterministic ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_192f profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_192f f.payload key (Spec.block Spec.shake_192f key 2)) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_192f msg ctx key (Spec.block Spec.shake_192f key 2) :=
  sign_eq shake_192f_sign_deterministic_valid shake_192f_sign_deterministic_long pub (fun _ =>
    (LinkedInternalSigner.shake_192f_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_192f m key (Spec.block Spec.shake_192f key 2)) f.payload_eq))
def shake_256s_verify : Image := ⟨.verify,Spec.shake_256s.n,LinkedAppleVerifyBody.shake_256s_image.gate.param,0x100079120,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x940012e3,
0xa9410bf3,0x90000320,0x910e2000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800806,
0x9400121b,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97feb0ac,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97feb0a0,0xaa1403e0,0x94016c4d
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_256s_image.body,0x100025448⟩
theorem shake_256s_verify_valid : run shake_256s_verify true = some .forwarded := by decide +kernel
theorem shake_256s_verify_long : run shake_256s_verify false = some .rejected := by decide +kernel
theorem shake_256s_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_256s_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_256s_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_256s f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_256s msg sig ctx pk :=
  verify_eq shake_256s_verify_valid shake_256s_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_256s_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_256s m sig pk) f.payload_eq))
theorem shake_256s_verify_malformed {msg ctx sig pk r} (pub : execute shake_256s_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_256s.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_256s msg sig ctx pk :=
  verify_eq shake_256s_verify_valid shake_256s_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_256s_malformed _ _ _ fits bad).eq_spec)
def shake_256s_slh_verify : Image := ⟨.verify,Spec.shake_256s.n,LinkedAppleVerifyBody.shake_256s_image.gate.param,0x100078df8,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x940013ad,
0xa9410bf3,0xb0000320,0x910e2000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800806,
0x940012e5,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97feb176,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97feb16a,0xaa1403e0,0x94016d17
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_256s_image.body,0x100025448⟩
theorem shake_256s_slh_verify_valid : run shake_256s_slh_verify true = some .forwarded := by decide +kernel
theorem shake_256s_slh_verify_long : run shake_256s_slh_verify false = some .rejected := by decide +kernel
theorem shake_256s_slh_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_256s_slh_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_256s_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_256s f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_256s msg sig ctx pk :=
  verify_eq shake_256s_slh_verify_valid shake_256s_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_256s_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_256s m sig pk) f.payload_eq))
theorem shake_256s_slh_verify_malformed {msg ctx sig pk r} (pub : execute shake_256s_slh_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_256s.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_256s msg sig ctx pk :=
  verify_eq shake_256s_slh_verify_valid shake_256s_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_256s_malformed _ _ _ fits bad).eq_spec)
def shake_256s_sign : Image := ⟨.sign,Spec.shake_256s.n,LinkedInternalSigner.shake_256s.cfg.param,0x100079044,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x9400131b,0xa9408bf3,
0x90000320,0x910e2000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52801004,0xaa1603e5,0x94000e22,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97feb0e1,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97feb0d6,0xaa1403e0,0x94016c83
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_256s.body,0x100025448⟩
theorem shake_256s_sign_valid : run shake_256s_sign true = some .forwarded := by decide +kernel
theorem shake_256s_sign_long : run shake_256s_sign false = some .rejected := by decide +kernel
theorem shake_256s_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_256s_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_256s profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_256s f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_256s msg ctx key rand :=
  sign_eq shake_256s_sign_valid shake_256s_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_256s_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_256s m key rand) f.payload_eq))
def shake_256s_slh_sign : Image := ⟨.sign,Spec.shake_256s.n,LinkedInternalSigner.shake_256s.cfg.param,0x1000791d4,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x940012b7,0xa9408bf3,
0x90000320,0x910e2000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52801004,0xaa1603e5,0x94000dbe,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97feb07d,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97feb072,0xaa1403e0,0x94016c1f
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_256s.body,0x100025448⟩
theorem shake_256s_slh_sign_valid : run shake_256s_slh_sign true = some .forwarded := by decide +kernel
theorem shake_256s_slh_sign_long : run shake_256s_slh_sign false = some .rejected := by decide +kernel
theorem shake_256s_slh_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_256s_slh_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_256s profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_256s f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_256s msg ctx key rand :=
  sign_eq shake_256s_slh_sign_valid shake_256s_slh_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_256s_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_256s m key rand) f.payload_eq))
def shake_256s_sign_deterministic : Image := ⟨.deterministic,Spec.shake_256s.n,LinkedInternalSigner.shake_256s.cfg.param,0x100078ecc,#[
0xd10203ff,0xa90557f6,0xa9064ff4,0xa9077bfd,0x9101c3fd,0xaa0803f4,0xad420480,0xad0007e0,
0xf103fc7f,0x54000089,0x92800008,0xf9000288,0x14000016,0xaa0403f5,0x910083e8,0x94001378,
0xa9428bf3,0xb0000320,0x910e2000,0x9100e3e8,0x910003e5,0xaa1303e1,0xaa1503e3,0x52801004,
0x94000e7f,0x3cc383e0,0x3d800280,0xf94027e8,0xf9000a88,0xf94013e1,0xb4000081,0xaa1303e0,
0x52800022,0x97feb13e,0xa9477bfd,0xa9464ff4,0xa94557f6,0x910203ff,0xd65f03c0,0xaa0003f4,
0xf94013e1,0xb4000081,0xaa1303e0,0x52800022,0x97feb133,0xaa1403e0,0x94016ce0
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_256s.body,0x100025448⟩
theorem shake_256s_sign_deterministic_valid : run shake_256s_sign_deterministic true = some .forwarded := by decide +kernel
theorem shake_256s_sign_deterministic_long : run shake_256s_sign_deterministic false = some .rejected := by decide +kernel
theorem shake_256s_sign_deterministic_eq {msg ctx key out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_256s_sign_deterministic ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_256s profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_256s f.payload key (Spec.block Spec.shake_256s key 2)) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_256s msg ctx key (Spec.block Spec.shake_256s key 2) :=
  sign_eq shake_256s_sign_deterministic_valid shake_256s_sign_deterministic_long pub (fun _ =>
    (LinkedInternalSigner.shake_256s_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_256s m key (Spec.block Spec.shake_256s key 2)) f.payload_eq))
def shake_256f_verify : Image := ⟨.verify,Spec.shake_256f.n,LinkedAppleVerifyBody.shake_256f_image.gate.param,0x100076634,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x94001d9e,
0xa9410bf3,0xf0000320,0x910a2000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800806,
0x94001cd6,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97febb67,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97febb5b,0xaa1403e0,0x94017708
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_256f_image.body,0x100025448⟩
theorem shake_256f_verify_valid : run shake_256f_verify true = some .forwarded := by decide +kernel
theorem shake_256f_verify_long : run shake_256f_verify false = some .rejected := by decide +kernel
theorem shake_256f_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_256f_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_256f_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_256f f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_256f msg sig ctx pk :=
  verify_eq shake_256f_verify_valid shake_256f_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_256f_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_256f m sig pk) f.payload_eq))
theorem shake_256f_verify_malformed {msg ctx sig pk r} (pub : execute shake_256f_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_256f.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_256f msg sig ctx pk :=
  verify_eq shake_256f_verify_valid shake_256f_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_256f_malformed _ _ _ fits bad).eq_spec)
def shake_256f_slh_verify : Image := ⟨.verify,Spec.shake_256f.n,LinkedAppleVerifyBody.shake_256f_image.gate.param,0x100076634,#[
0xd10143ff,0xa90257f6,0xa9034ff4,0xa9047bfd,0x910103fd,0xf103fcbf,0x54000069,0x52800000,
0x14000018,0xaa0603f4,0xaa0303f5,0xaa0203f6,0x910023e8,0xaa0403e2,0xaa0503e3,0x94001d9e,
0xa9410bf3,0xf0000320,0x910a2000,0xaa1303e1,0xaa1603e3,0xaa1503e4,0xaa1403e5,0x52800806,
0x94001cd6,0xf94007e1,0xb40000c1,0xaa0003f4,0xaa1303e0,0x52800022,0x97febb67,0xaa1403e0,
0xa9447bfd,0xa9434ff4,0xa94257f6,0x910143ff,0xd65f03c0,0xaa0003f4,0xf94007e1,0xb4000081,
0xaa1303e0,0x52800022,0x97febb5b,0xaa1403e0,0x94017708
],LinkedApplePureFrame.image.entry,LinkedAppleVerifyBody.shake_256f_image.body,0x100025448⟩
theorem shake_256f_slh_verify_valid : run shake_256f_slh_verify true = some .forwarded := by decide +kernel
theorem shake_256f_slh_verify_long : run shake_256f_slh_verify false = some .rejected := by decide +kernel
theorem shake_256f_slh_verify_eq {msg ctx sig pk out r} (f : Frame msg ctx)
    (pub : execute shake_256f_slh_verify ctx = some r)
    (core : Spec.ArmVerifyBody.run LinkedAppleVerifyBody.shake_256f_image = some out)
    (v : Spec.ArmVerifyBody.Callees Spec.shake_256f f.payload sig pk) :
    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.shake_256f msg sig ctx pk :=
  verify_eq shake_256f_slh_verify_valid shake_256f_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyBody.shake_256f_eq core v).trans
      (congrArg (fun m => Spec.slhVerifyInternal Spec.shake_256f m sig pk) f.payload_eq))
theorem shake_256f_slh_verify_malformed {msg ctx sig pk r} (pub : execute shake_256f_slh_verify ctx = some r)
    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.shake_256f.sigBytes) :
    verifyReturn r false = Spec.slhVerify Spec.shake_256f msg sig ctx pk :=
  verify_eq shake_256f_slh_verify_valid shake_256f_slh_verify_long pub (fun _ =>
    (LinkedAppleVerifyLength.shake_256f_malformed _ _ _ fits bad).eq_spec)
def shake_256f_sign : Image := ⟨.sign,Spec.shake_256f.n,LinkedInternalSigner.shake_256f.cfg.param,0x100076880,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x94001d0c,0xa9408bf3,
0xf0000320,0x910a2000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52801004,0xaa1603e5,0x94001813,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97febad2,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97febac7,0xaa1403e0,0x94017674
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_256f.body,0x100025448⟩
theorem shake_256f_sign_valid : run shake_256f_sign true = some .forwarded := by decide +kernel
theorem shake_256f_sign_long : run shake_256f_sign false = some .rejected := by decide +kernel
theorem shake_256f_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_256f_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_256f profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_256f f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_256f msg ctx key rand :=
  sign_eq shake_256f_sign_valid shake_256f_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_256f_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_256f m key rand) f.payload_eq))
def shake_256f_slh_sign : Image := ⟨.sign,Spec.shake_256f.n,LinkedInternalSigner.shake_256f.cfg.param,0x100076880,#[
0xd10183ff,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0803f4,0xf103fc7f,0x54000089,
0x92800008,0xf9000288,0x14000017,0xaa0403f5,0x910003e8,0xaa0503f6,0x94001d0c,0xa9408bf3,
0xf0000320,0x910a2000,0x910063e8,0xaa1303e1,0xaa1503e3,0x52801004,0xaa1603e5,0x94001813,
0x3cc183e0,0x3d800280,0xf94017e8,0xf9000a88,0xf94003e1,0xb4000081,0xaa1303e0,0x52800022,
0x97febad2,0xa9457bfd,0xa9444ff4,0xa94357f6,0x910183ff,0xd65f03c0,0xaa0003f4,0xf94003e1,
0xb4000081,0xaa1303e0,0x52800022,0x97febac7,0xaa1403e0,0x94017674
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_256f.body,0x100025448⟩
theorem shake_256f_slh_sign_valid : run shake_256f_slh_sign true = some .forwarded := by decide +kernel
theorem shake_256f_slh_sign_long : run shake_256f_slh_sign false = some .rejected := by decide +kernel
theorem shake_256f_slh_sign_eq {msg ctx key rand out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_256f_slh_sign ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_256f profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_256f f.payload key rand) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_256f msg ctx key rand :=
  sign_eq shake_256f_slh_sign_valid shake_256f_slh_sign_long pub (fun _ =>
    (LinkedInternalSigner.shake_256f_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_256f m key rand) f.payload_eq))
def shake_256f_sign_deterministic : Image := ⟨.deterministic,Spec.shake_256f.n,LinkedInternalSigner.shake_256f.cfg.param,0x100076708,#[
0xd10203ff,0xa90557f6,0xa9064ff4,0xa9077bfd,0x9101c3fd,0xaa0803f4,0xad420480,0xad0007e0,
0xf103fc7f,0x54000089,0x92800008,0xf9000288,0x14000016,0xaa0403f5,0x910083e8,0x94001d69,
0xa9428bf3,0xf0000320,0x910a2000,0x9100e3e8,0x910003e5,0xaa1303e1,0xaa1503e3,0x52801004,
0x94001870,0x3cc383e0,0x3d800280,0xf94027e8,0xf9000a88,0xf94013e1,0xb4000081,0xaa1303e0,
0x52800022,0x97febb2f,0xa9477bfd,0xa9464ff4,0xa94557f6,0x910203ff,0xd65f03c0,0xaa0003f4,
0xf94013e1,0xb4000081,0xaa1303e0,0x52800022,0x97febb24,0xaa1403e0,0x940176d1
],LinkedApplePureFrame.image.entry,LinkedInternalSigner.shake_256f.body,0x100025448⟩
theorem shake_256f_sign_deterministic_valid : run shake_256f_sign_deterministic true = some .forwarded := by decide +kernel
theorem shake_256f_sign_deterministic_long : run shake_256f_sign_deterministic false = some .rejected := by decide +kernel
theorem shake_256f_sign_deterministic_eq {msg ctx key out r} (f : Frame msg ctx) (profile : Fin 4)
    (pub : execute shake_256f_sign_deterministic ctx = some r)
    (core : Spec.ArmInternalSigner.run LinkedInternalSigner.shake_256f profile = some out)
    (v : Spec.ArmInternalSigner.Callees Spec.shake_256f f.payload key (Spec.block Spec.shake_256f key 2)) :
    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.shake_256f msg ctx key (Spec.block Spec.shake_256f key 2) :=
  sign_eq shake_256f_sign_deterministic_valid shake_256f_sign_deterministic_long pub (fun _ =>
    (LinkedInternalSigner.shake_256f_eq profile core v).trans
      (congrArg (fun m => Spec.slhSignInternal Spec.shake_256f m key (Spec.block Spec.shake_256f key 2)) f.payload_eq))
theorem wrongContext : run {shake_128s_verify with words := shake_128s_verify.words.set! 14 0xaa0403e3} true ≠
    some .forwarded := by decide +kernel
theorem wrongVerdict : run {shake_128s_verify with words := shake_128s_verify.words.set! 31 0xaa1303e0} true ≠
    some .forwarded := by decide +kernel
theorem wrongSeed : run {shake_128s_sign_deterministic with words := shake_128s_sign_deterministic.words.set! 6 0x3dc00480} true ≠
    some .forwarded := by decide +kernel
theorem wrongResult : run {shake_128s_sign with words := shake_128s_sign.words.set! 26 0xf94013e8} true ≠
    some .forwarded := by decide +kernel
theorem wrongCutoff : run {shake_128s_slh_verify with words := shake_128s_slh_verify.words.set! 5 0xf103f8bf} true ≠
    some .forwarded := by decide +kernel
#print axioms shake_128s_verify_eq
#print axioms shake_256f_sign_deterministic_eq
end LinkedApplePure

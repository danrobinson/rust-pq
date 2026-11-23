import Spec.ArmVerifyLength
namespace LinkedAppleVerifyLength
open Spec.ArmVerifyLength
set_option maxRecDepth 65536
set_option maxHeartbeats 0
-- Mach-O SHA-256 ab672dc82d293ec220beb29f475bedda4614d59c76636cd16edef18705e1ac0a
def shake_128s_path : Path := ⟨0x100073154, 0x1000dd210, [16, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 63, 0, 0, 0, 7, 0, 0, 0, 9, 0, 0, 0, 12, 0, 0, 0, 14, 0, 0, 0],
  [(0x100073154,0xaa0403e5), (0x100073158,0xaa0303e4), (0x10007315c,0xaa0203e3), (0x100073160,0xaa0103e2), (0x100073164,0xaa0003e1), (0x100073168,0xd0000340), (0x10007316c,0x91084000), (0x100073170,0x52800406), (0x100073174,0x14002866), (0x10007d30c,0xd105c3ff), (0x10007d310,0xa9116ffc), (0x10007d314,0xa91267fa), (0x10007d318,0xa9135ff8), (0x10007d31c,0xa91457f6), (0x10007d320,0xa9154ff4), (0x10007d324,0xa9167bfd), (0x10007d328,0x910583fd), (0x10007d32c,0xaa0403f6), (0x10007d330,0xf940001a), (0x10007d334,0x2943ec15), (0x10007d338,0x1b156f73), (0x10007d33c,0x2942e009), (0x10007d340,0xa90203e9), (0x10007d344,0x8b1a0708), (0x10007d348,0x91000d17), (0x10007d34c,0x9b094ee8), (0x10007d350,0x9b086b48)],
  (0x10007d354,0xeb08009f), (0x10007d358,0x54001381),
  [(0x10007d5c8,0x52800000), (0x10007d5cc,0xa9567bfd), (0x10007d5d0,0xa9554ff4), (0x10007d5d4,0xa95457f6), (0x10007d5d8,0xa9535ff8), (0x10007d5dc,0xa95267fa), (0x10007d5e0,0xa9516ffc), (0x10007d5e4,0x9105c3ff), (0x10007d5e8,0xd65f03c0)]⟩
theorem shake_128s_params : shake_128s_path.params = Spec.ArmKeygen.parameterBytes Spec.shake_128s := by decide
theorem shake_128s_checked : inspect shake_128s_path = some ⟨Spec.shake_128s.sigBytes,0x10007d35c,false⟩ := by decide
theorem shake_128s_validEdge : execute shake_128s_path Spec.shake_128s.sigBytes = some (.continued 0x10007d35c) :=
  acceptedEdge shake_128s_checked (by decide)
def shake_128s_trace (msg sig pk : Spec.Bytes) (value : Bool)
    (actual : execute shake_128s_path sig.length = some (.returned value)) :
    LinkedArm.Signer.VerifyTrace Spec.shake_128s msg sig pk value :=
  toVerifyTrace shake_128s_checked msg sig pk value actual
def shake_128s_malformed (msg sig pk : Spec.Bytes) (fits : sig.length < 2^64)
    (bad : sig.length ≠ Spec.shake_128s.sigBytes) :
    LinkedArm.Signer.VerifyTrace Spec.shake_128s msg sig pk false :=
  shake_128s_trace msg sig pk false (rejects shake_128s_checked sig fits bad)

def shake_128s_toHash : List (Nat × Nat) := [(0x10007d35c,0xf1003cdf), (0x10007d360,0x54001589), (0x10007d364,0xaa0503fc), (0x10007d368,0x3dc000a0), (0x10007d36c,0x3d800fe0), (0x10007d370,0xf1007cdf), (0x10007d374,0x540015a9), (0x10007d378,0x3dc00780), (0x10007d37c,0x3d8013e0), (0x10007d380,0xf1003edf), (0x10007d384,0x540015e9), (0x10007d388,0xaa0303f9), (0x10007d38c,0xaa0203e5), (0x10007d390,0xaa0103e4), (0x10007d394,0x3dc00060), (0x10007d398,0x3d8017e0), (0x10007d39c,0x9101a3e8), (0x10007d3a0,0x910143e1), (0x10007d3a4,0x9100c3e2), (0x10007d3a8,0x910103e3), (0x10007d3ac,0xf94017f4), (0x10007d3b0,0xaa1403e0), (0x10007d3b4,0x97ffe1b6)]
theorem shake_128s_hashCall : hashCall shake_128s_path Spec.shake_128s.n Spec.shake_128s.sigBytes
    0x100075a8c shake_128s_toHash = some (expectedCall Spec.shake_128s.n) := by decide
theorem shake_128s_digestPremise {call}
    (actual : hashCall shake_128s_path Spec.shake_128s.n Spec.shake_128s.sigBytes 0x100075a8c shake_128s_toHash = some call)
    (msg sig pk digest : Spec.Bytes) (sigSize : Spec.shake_128s.n ≤ sig.length)
    (pkSize : 2 * Spec.shake_128s.n ≤ pk.length)
    (target : let v := Spec.ArmKeygen.interpret (hashSources Spec.shake_128s sig pk)
      digest = Spec.Hmsg Spec.shake_128s (Spec.ArmKeygen.bytes v call.randomizer)
        (Spec.ArmKeygen.bytes v call.publicSeed) (Spec.ArmKeygen.bytes v call.publicRoot) msg) :
    digest = Spec.Hmsg Spec.shake_128s (sig.take Spec.shake_128s.n)
      (Spec.block Spec.shake_128s pk 0) (Spec.block Spec.shake_128s pk 1) msg :=
  digestPremise shake_128s_hashCall actual msg sig pk digest sigSize pkSize (by decide) (by decide) target

theorem wrongLengthSource : inspect { shake_128s_path with before := shake_128s_path.before.map (fun (pc,w) => (pc,if pc = 0x100073158 then 0xaa0203e4 else w)) } ≠
    some ⟨Spec.shake_128s.sigBytes,0x10007d35c,false⟩ := by decide
theorem wrongSizeArithmetic : inspect { shake_128s_path with before := shake_128s_path.before.map (fun (pc,w) => (pc,if w = 0x91000d17 then 0x91001117 else w)) } ≠
    some ⟨Spec.shake_128s.sigBytes,0x10007d35c,false⟩ := by decide
theorem reversedGuard : inspect { shake_128s_path with branch := (0x10007d358,0x54001380) } ≠
    some ⟨Spec.shake_128s.sigBytes,0x10007d35c,false⟩ := by decide
theorem acceptsMalformed : inspect { shake_128s_path with reject := shake_128s_path.reject.map (fun (pc,w) => (pc,if w = 0x52800000 then 0x52800020 else w)) } ≠
    some ⟨Spec.shake_128s.sigBytes,0x10007d35c,false⟩ := by decide
theorem wrongHashArgument : hashCall shake_128s_path 16 Spec.shake_128s.sigBytes 0x100075a8c
    (shake_128s_toHash.map (fun (pc,w) => (pc,if w == 0x910143e1 then 0x9100c3e1 else w)))
    ≠ some (expectedCall 16) := by decide
theorem wrongHashTarget : hashCall shake_128s_path 16 Spec.shake_128s.sigBytes 0x100075a8c
    (shake_128s_toHash.map (fun (pc,w) => (pc,if pc = 0x10007d3b4 then 0x97ffe1b7 else w)))
    ≠ some (expectedCall 16) := by decide
def shake_128f_path : Path := ⟨0x100072ce4, 0x1000dd1e8, [16, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 66, 0, 0, 0, 22, 0, 0, 0, 3, 0, 0, 0, 6, 0, 0, 0, 33, 0, 0, 0],
  [(0x100072ce4,0xaa0403e5), (0x100072ce8,0xaa0303e4), (0x100072cec,0xaa0203e3), (0x100072cf0,0xaa0103e2), (0x100072cf4,0xaa0003e1), (0x100072cf8,0xf0000340), (0x100072cfc,0x9107a000), (0x100072d00,0x52800406), (0x100072d04,0x14002982), (0x10007d30c,0xd105c3ff), (0x10007d310,0xa9116ffc), (0x10007d314,0xa91267fa), (0x10007d318,0xa9135ff8), (0x10007d31c,0xa91457f6), (0x10007d320,0xa9154ff4), (0x10007d324,0xa9167bfd), (0x10007d328,0x910583fd), (0x10007d32c,0xaa0403f6), (0x10007d330,0xf940001a), (0x10007d334,0x2943ec15), (0x10007d338,0x1b156f73), (0x10007d33c,0x2942e009), (0x10007d340,0xa90203e9), (0x10007d344,0x8b1a0708), (0x10007d348,0x91000d17), (0x10007d34c,0x9b094ee8), (0x10007d350,0x9b086b48)],
  (0x10007d354,0xeb08009f), (0x10007d358,0x54001381),
  [(0x10007d5c8,0x52800000), (0x10007d5cc,0xa9567bfd), (0x10007d5d0,0xa9554ff4), (0x10007d5d4,0xa95457f6), (0x10007d5d8,0xa9535ff8), (0x10007d5dc,0xa95267fa), (0x10007d5e0,0xa9516ffc), (0x10007d5e4,0x9105c3ff), (0x10007d5e8,0xd65f03c0)]⟩
theorem shake_128f_params : shake_128f_path.params = Spec.ArmKeygen.parameterBytes Spec.shake_128f := by decide
theorem shake_128f_checked : inspect shake_128f_path = some ⟨Spec.shake_128f.sigBytes,0x10007d35c,false⟩ := by decide
theorem shake_128f_validEdge : execute shake_128f_path Spec.shake_128f.sigBytes = some (.continued 0x10007d35c) :=
  acceptedEdge shake_128f_checked (by decide)
def shake_128f_trace (msg sig pk : Spec.Bytes) (value : Bool)
    (actual : execute shake_128f_path sig.length = some (.returned value)) :
    LinkedArm.Signer.VerifyTrace Spec.shake_128f msg sig pk value :=
  toVerifyTrace shake_128f_checked msg sig pk value actual
def shake_128f_malformed (msg sig pk : Spec.Bytes) (fits : sig.length < 2^64)
    (bad : sig.length ≠ Spec.shake_128f.sigBytes) :
    LinkedArm.Signer.VerifyTrace Spec.shake_128f msg sig pk false :=
  shake_128f_trace msg sig pk false (rejects shake_128f_checked sig fits bad)

def shake_128f_toHash : List (Nat × Nat) := [(0x10007d35c,0xf1003cdf), (0x10007d360,0x54001589), (0x10007d364,0xaa0503fc), (0x10007d368,0x3dc000a0), (0x10007d36c,0x3d800fe0), (0x10007d370,0xf1007cdf), (0x10007d374,0x540015a9), (0x10007d378,0x3dc00780), (0x10007d37c,0x3d8013e0), (0x10007d380,0xf1003edf), (0x10007d384,0x540015e9), (0x10007d388,0xaa0303f9), (0x10007d38c,0xaa0203e5), (0x10007d390,0xaa0103e4), (0x10007d394,0x3dc00060), (0x10007d398,0x3d8017e0), (0x10007d39c,0x9101a3e8), (0x10007d3a0,0x910143e1), (0x10007d3a4,0x9100c3e2), (0x10007d3a8,0x910103e3), (0x10007d3ac,0xf94017f4), (0x10007d3b0,0xaa1403e0), (0x10007d3b4,0x97ffe1b6)]
theorem shake_128f_hashCall : hashCall shake_128f_path Spec.shake_128f.n Spec.shake_128f.sigBytes
    0x100075a8c shake_128f_toHash = some (expectedCall Spec.shake_128f.n) := by decide
theorem shake_128f_digestPremise {call}
    (actual : hashCall shake_128f_path Spec.shake_128f.n Spec.shake_128f.sigBytes 0x100075a8c shake_128f_toHash = some call)
    (msg sig pk digest : Spec.Bytes) (sigSize : Spec.shake_128f.n ≤ sig.length)
    (pkSize : 2 * Spec.shake_128f.n ≤ pk.length)
    (target : let v := Spec.ArmKeygen.interpret (hashSources Spec.shake_128f sig pk)
      digest = Spec.Hmsg Spec.shake_128f (Spec.ArmKeygen.bytes v call.randomizer)
        (Spec.ArmKeygen.bytes v call.publicSeed) (Spec.ArmKeygen.bytes v call.publicRoot) msg) :
    digest = Spec.Hmsg Spec.shake_128f (sig.take Spec.shake_128f.n)
      (Spec.block Spec.shake_128f pk 0) (Spec.block Spec.shake_128f pk 1) msg :=
  digestPremise shake_128f_hashCall actual msg sig pk digest sigSize pkSize (by decide) (by decide) target

def shake_192s_path : Path := ⟨0x100078b8c, 0x1000dd360, [24, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 63, 0, 0, 0, 7, 0, 0, 0, 9, 0, 0, 0, 14, 0, 0, 0, 17, 0, 0, 0],
  [(0x100078b8c,0xaa0403e5), (0x100078b90,0xaa0303e4), (0x100078b94,0xaa0203e3), (0x100078b98,0xaa0103e2), (0x100078b9c,0xaa0003e1), (0x100078ba0,0xb0000320), (0x100078ba4,0x910d8000), (0x100078ba8,0x52800606), (0x100078bac,0x140012c9), (0x10007d6d0,0xd10543ff), (0x10007d6d4,0xa90f6ffc), (0x10007d6d8,0xa91067fa), (0x10007d6dc,0xa9115ff8), (0x10007d6e0,0xa91257f6), (0x10007d6e4,0xa9134ff4), (0x10007d6e8,0xa9147bfd), (0x10007d6ec,0x910503fd), (0x10007d6f0,0xaa0403f6), (0x10007d6f4,0xf940001b), (0x10007d6f8,0x2943dc18), (0x10007d6fc,0x1b185efc), (0x10007d700,0x2942cc08), (0x10007d704,0x8b1b0669), (0x10007d708,0x91000d29), (0x10007d70c,0x9b087128), (0x10007d710,0x9b086f68)],
  (0x10007d714,0xeb08009f), (0x10007d718,0x54000f81),
  [(0x10007d908,0x52800000), (0x10007d90c,0xa9547bfd), (0x10007d910,0xa9534ff4), (0x10007d914,0xa95257f6), (0x10007d918,0xa9515ff8), (0x10007d91c,0xa95067fa), (0x10007d920,0xa94f6ffc), (0x10007d924,0x910543ff), (0x10007d928,0xd65f03c0)]⟩
theorem shake_192s_params : shake_192s_path.params = Spec.ArmKeygen.parameterBytes Spec.shake_192s := by decide
theorem shake_192s_checked : inspect shake_192s_path = some ⟨Spec.shake_192s.sigBytes,0x10007d71c,false⟩ := by decide
theorem shake_192s_validEdge : execute shake_192s_path Spec.shake_192s.sigBytes = some (.continued 0x10007d71c) :=
  acceptedEdge shake_192s_checked (by decide)
def shake_192s_trace (msg sig pk : Spec.Bytes) (value : Bool)
    (actual : execute shake_192s_path sig.length = some (.returned value)) :
    LinkedArm.Signer.VerifyTrace Spec.shake_192s msg sig pk value :=
  toVerifyTrace shake_192s_checked msg sig pk value actual
def shake_192s_malformed (msg sig pk : Spec.Bytes) (fits : sig.length < 2^64)
    (bad : sig.length ≠ Spec.shake_192s.sigBytes) :
    LinkedArm.Signer.VerifyTrace Spec.shake_192s msg sig pk false :=
  shake_192s_trace msg sig pk false (rejects shake_192s_checked sig fits bad)

def shake_192s_toHash : List (Nat × Nat) := [(0x10007d71c,0xf1005cdf), (0x10007d720,0x54001069), (0x10007d724,0xaa0503f9), (0x10007d728,0x3dc000a0), (0x10007d72c,0x3d8007e0), (0x10007d730,0xf94008a8), (0x10007d734,0xf90013e8), (0x10007d738,0xf100bcdf), (0x10007d73c,0x54001049), (0x10007d740,0x3cc18320), (0x10007d744,0x3d800fe0), (0x10007d748,0xf9401728), (0x10007d74c,0xf90023e8), (0x10007d750,0xf1005edf), (0x10007d754,0x54001049), (0x10007d758,0xaa0303f5), (0x10007d75c,0xaa0203e5), (0x10007d760,0xaa0103e4), (0x10007d764,0xaa0003f4), (0x10007d768,0x3dc00060), (0x10007d76c,0x3d8017e0), (0x10007d770,0xf9400868), (0x10007d774,0xf90033e8), (0x10007d778,0x9101a3e8), (0x10007d77c,0x910143e1), (0x10007d780,0x910043e2), (0x10007d784,0x9100c3e3), (0x10007d788,0x97ffe118)]
theorem shake_192s_hashCall : hashCall shake_192s_path Spec.shake_192s.n Spec.shake_192s.sigBytes
    0x100075be8 shake_192s_toHash = some (expectedCall Spec.shake_192s.n) := by decide
theorem shake_192s_digestPremise {call}
    (actual : hashCall shake_192s_path Spec.shake_192s.n Spec.shake_192s.sigBytes 0x100075be8 shake_192s_toHash = some call)
    (msg sig pk digest : Spec.Bytes) (sigSize : Spec.shake_192s.n ≤ sig.length)
    (pkSize : 2 * Spec.shake_192s.n ≤ pk.length)
    (target : let v := Spec.ArmKeygen.interpret (hashSources Spec.shake_192s sig pk)
      digest = Spec.Hmsg Spec.shake_192s (Spec.ArmKeygen.bytes v call.randomizer)
        (Spec.ArmKeygen.bytes v call.publicSeed) (Spec.ArmKeygen.bytes v call.publicRoot) msg) :
    digest = Spec.Hmsg Spec.shake_192s (sig.take Spec.shake_192s.n)
      (Spec.block Spec.shake_192s pk 0) (Spec.block Spec.shake_192s pk 1) msg :=
  digestPremise shake_192s_hashCall actual msg sig pk digest sigSize pkSize (by decide) (by decide) target

def shake_192f_path : Path := ⟨0x1000786fc, 0x1000dd338, [24, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 66, 0, 0, 0, 22, 0, 0, 0, 3, 0, 0, 0, 8, 0, 0, 0, 33, 0, 0, 0],
  [(0x1000786fc,0xaa0403e5), (0x100078700,0xaa0303e4), (0x100078704,0xaa0203e3), (0x100078708,0xaa0103e2), (0x10007870c,0xaa0003e1), (0x100078710,0xb0000320), (0x100078714,0x910ce000), (0x100078718,0x52800606), (0x10007871c,0x140013ed), (0x10007d6d0,0xd10543ff), (0x10007d6d4,0xa90f6ffc), (0x10007d6d8,0xa91067fa), (0x10007d6dc,0xa9115ff8), (0x10007d6e0,0xa91257f6), (0x10007d6e4,0xa9134ff4), (0x10007d6e8,0xa9147bfd), (0x10007d6ec,0x910503fd), (0x10007d6f0,0xaa0403f6), (0x10007d6f4,0xf940001b), (0x10007d6f8,0x2943dc18), (0x10007d6fc,0x1b185efc), (0x10007d700,0x2942cc08), (0x10007d704,0x8b1b0669), (0x10007d708,0x91000d29), (0x10007d70c,0x9b087128), (0x10007d710,0x9b086f68)],
  (0x10007d714,0xeb08009f), (0x10007d718,0x54000f81),
  [(0x10007d908,0x52800000), (0x10007d90c,0xa9547bfd), (0x10007d910,0xa9534ff4), (0x10007d914,0xa95257f6), (0x10007d918,0xa9515ff8), (0x10007d91c,0xa95067fa), (0x10007d920,0xa94f6ffc), (0x10007d924,0x910543ff), (0x10007d928,0xd65f03c0)]⟩
theorem shake_192f_params : shake_192f_path.params = Spec.ArmKeygen.parameterBytes Spec.shake_192f := by decide
theorem shake_192f_checked : inspect shake_192f_path = some ⟨Spec.shake_192f.sigBytes,0x10007d71c,false⟩ := by decide
theorem shake_192f_validEdge : execute shake_192f_path Spec.shake_192f.sigBytes = some (.continued 0x10007d71c) :=
  acceptedEdge shake_192f_checked (by decide)
def shake_192f_trace (msg sig pk : Spec.Bytes) (value : Bool)
    (actual : execute shake_192f_path sig.length = some (.returned value)) :
    LinkedArm.Signer.VerifyTrace Spec.shake_192f msg sig pk value :=
  toVerifyTrace shake_192f_checked msg sig pk value actual
def shake_192f_malformed (msg sig pk : Spec.Bytes) (fits : sig.length < 2^64)
    (bad : sig.length ≠ Spec.shake_192f.sigBytes) :
    LinkedArm.Signer.VerifyTrace Spec.shake_192f msg sig pk false :=
  shake_192f_trace msg sig pk false (rejects shake_192f_checked sig fits bad)

def shake_192f_toHash : List (Nat × Nat) := [(0x10007d71c,0xf1005cdf), (0x10007d720,0x54001069), (0x10007d724,0xaa0503f9), (0x10007d728,0x3dc000a0), (0x10007d72c,0x3d8007e0), (0x10007d730,0xf94008a8), (0x10007d734,0xf90013e8), (0x10007d738,0xf100bcdf), (0x10007d73c,0x54001049), (0x10007d740,0x3cc18320), (0x10007d744,0x3d800fe0), (0x10007d748,0xf9401728), (0x10007d74c,0xf90023e8), (0x10007d750,0xf1005edf), (0x10007d754,0x54001049), (0x10007d758,0xaa0303f5), (0x10007d75c,0xaa0203e5), (0x10007d760,0xaa0103e4), (0x10007d764,0xaa0003f4), (0x10007d768,0x3dc00060), (0x10007d76c,0x3d8017e0), (0x10007d770,0xf9400868), (0x10007d774,0xf90033e8), (0x10007d778,0x9101a3e8), (0x10007d77c,0x910143e1), (0x10007d780,0x910043e2), (0x10007d784,0x9100c3e3), (0x10007d788,0x97ffe118)]
theorem shake_192f_hashCall : hashCall shake_192f_path Spec.shake_192f.n Spec.shake_192f.sigBytes
    0x100075be8 shake_192f_toHash = some (expectedCall Spec.shake_192f.n) := by decide
theorem shake_192f_digestPremise {call}
    (actual : hashCall shake_192f_path Spec.shake_192f.n Spec.shake_192f.sigBytes 0x100075be8 shake_192f_toHash = some call)
    (msg sig pk digest : Spec.Bytes) (sigSize : Spec.shake_192f.n ≤ sig.length)
    (pkSize : 2 * Spec.shake_192f.n ≤ pk.length)
    (target : let v := Spec.ArmKeygen.interpret (hashSources Spec.shake_192f sig pk)
      digest = Spec.Hmsg Spec.shake_192f (Spec.ArmKeygen.bytes v call.randomizer)
        (Spec.ArmKeygen.bytes v call.publicSeed) (Spec.ArmKeygen.bytes v call.publicRoot) msg) :
    digest = Spec.Hmsg Spec.shake_192f (sig.take Spec.shake_192f.n)
      (Spec.block Spec.shake_192f pk 0) (Spec.block Spec.shake_192f pk 1) msg :=
  digestPremise shake_192f_hashCall actual msg sig pk digest sigSize pkSize (by decide) (by decide) target

def shake_256s_path : Path := ⟨0x100079020, 0x1000dd388, [32, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 8, 0, 0, 0, 8, 0, 0, 0, 14, 0, 0, 0, 22, 0, 0, 0],
  [(0x100079020,0xaa0403e5), (0x100079024,0xaa0303e4), (0x100079028,0xaa0203e3), (0x10007902c,0xaa0103e2), (0x100079030,0xaa0003e1), (0x100079034,0x90000320), (0x100079038,0x910e2000), (0x10007903c,0x52800806), (0x100079040,0x1400126b), (0x10007d9ec,0xd105c3ff), (0x10007d9f0,0xa9116ffc), (0x10007d9f4,0xa91267fa), (0x10007d9f8,0xa9135ff8), (0x10007d9fc,0xa91457f6), (0x10007da00,0xa9154ff4), (0x10007da04,0xa9167bfd), (0x10007da08,0x910583fd), (0x10007da0c,0xaa0403f6), (0x10007da10,0xf940001b), (0x10007da14,0x2943dc18), (0x10007da18,0x1b185efc), (0x10007da1c,0x2942cc08), (0x10007da20,0x8b1b0669), (0x10007da24,0x91000d29), (0x10007da28,0x9b087128), (0x10007da2c,0x9b086f68)],
  (0x10007da30,0xeb08009f), (0x10007da34,0x54000e81),
  [(0x10007dc04,0x52800000), (0x10007dc08,0xa9567bfd), (0x10007dc0c,0xa9554ff4), (0x10007dc10,0xa95457f6), (0x10007dc14,0xa9535ff8), (0x10007dc18,0xa95267fa), (0x10007dc1c,0xa9516ffc), (0x10007dc20,0x9105c3ff), (0x10007dc24,0xd65f03c0)]⟩
theorem shake_256s_params : shake_256s_path.params = Spec.ArmKeygen.parameterBytes Spec.shake_256s := by decide
theorem shake_256s_checked : inspect shake_256s_path = some ⟨Spec.shake_256s.sigBytes,0x10007da38,false⟩ := by decide
theorem shake_256s_validEdge : execute shake_256s_path Spec.shake_256s.sigBytes = some (.continued 0x10007da38) :=
  acceptedEdge shake_256s_checked (by decide)
def shake_256s_trace (msg sig pk : Spec.Bytes) (value : Bool)
    (actual : execute shake_256s_path sig.length = some (.returned value)) :
    LinkedArm.Signer.VerifyTrace Spec.shake_256s msg sig pk value :=
  toVerifyTrace shake_256s_checked msg sig pk value actual
def shake_256s_malformed (msg sig pk : Spec.Bytes) (fits : sig.length < 2^64)
    (bad : sig.length ≠ Spec.shake_256s.sigBytes) :
    LinkedArm.Signer.VerifyTrace Spec.shake_256s msg sig pk false :=
  shake_256s_trace msg sig pk false (rejects shake_256s_checked sig fits bad)

def shake_256s_toHash : List (Nat × Nat) := [(0x10007da38,0xf1007cdf), (0x10007da3c,0x54000f69), (0x10007da40,0xaa0503f9), (0x10007da44,0xad4004a0), (0x10007da48,0xad0087e0), (0x10007da4c,0xf100fcdf), (0x10007da50,0x54000f89), (0x10007da54,0xad410720), (0x10007da58,0xad0187e0), (0x10007da5c,0xf1007edf), (0x10007da60,0x54000fc9), (0x10007da64,0xaa0303f5), (0x10007da68,0xaa0203e5), (0x10007da6c,0xaa0103e4), (0x10007da70,0xaa0003f4), (0x10007da74,0xad400460), (0x10007da78,0xad0287e0), (0x10007da7c,0x9101e3e8), (0x10007da80,0x910143e1), (0x10007da84,0x910043e2), (0x10007da88,0x9100c3e3), (0x10007da8c,0x97ffe0ae)]
theorem shake_256s_hashCall : hashCall shake_256s_path Spec.shake_256s.n Spec.shake_256s.sigBytes
    0x100075d44 shake_256s_toHash = some (expectedCall Spec.shake_256s.n) := by decide
theorem shake_256s_digestPremise {call}
    (actual : hashCall shake_256s_path Spec.shake_256s.n Spec.shake_256s.sigBytes 0x100075d44 shake_256s_toHash = some call)
    (msg sig pk digest : Spec.Bytes) (sigSize : Spec.shake_256s.n ≤ sig.length)
    (pkSize : 2 * Spec.shake_256s.n ≤ pk.length)
    (target : let v := Spec.ArmKeygen.interpret (hashSources Spec.shake_256s sig pk)
      digest = Spec.Hmsg Spec.shake_256s (Spec.ArmKeygen.bytes v call.randomizer)
        (Spec.ArmKeygen.bytes v call.publicSeed) (Spec.ArmKeygen.bytes v call.publicRoot) msg) :
    digest = Spec.Hmsg Spec.shake_256s (sig.take Spec.shake_256s.n)
      (Spec.block Spec.shake_256s pk 0) (Spec.block Spec.shake_256s pk 1) msg :=
  digestPremise shake_256s_hashCall actual msg sig pk digest sigSize pkSize (by decide) (by decide) target

def shake_256f_path : Path := ⟨0x10007685c, 0x1000dd288, [32, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 17, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 35, 0, 0, 0],
  [(0x10007685c,0xaa0403e5), (0x100076860,0xaa0303e4), (0x100076864,0xaa0203e3), (0x100076868,0xaa0103e2), (0x10007686c,0xaa0003e1), (0x100076870,0xf0000320), (0x100076874,0x910a2000), (0x100076878,0x52800806), (0x10007687c,0x14001c5c), (0x10007d9ec,0xd105c3ff), (0x10007d9f0,0xa9116ffc), (0x10007d9f4,0xa91267fa), (0x10007d9f8,0xa9135ff8), (0x10007d9fc,0xa91457f6), (0x10007da00,0xa9154ff4), (0x10007da04,0xa9167bfd), (0x10007da08,0x910583fd), (0x10007da0c,0xaa0403f6), (0x10007da10,0xf940001b), (0x10007da14,0x2943dc18), (0x10007da18,0x1b185efc), (0x10007da1c,0x2942cc08), (0x10007da20,0x8b1b0669), (0x10007da24,0x91000d29), (0x10007da28,0x9b087128), (0x10007da2c,0x9b086f68)],
  (0x10007da30,0xeb08009f), (0x10007da34,0x54000e81),
  [(0x10007dc04,0x52800000), (0x10007dc08,0xa9567bfd), (0x10007dc0c,0xa9554ff4), (0x10007dc10,0xa95457f6), (0x10007dc14,0xa9535ff8), (0x10007dc18,0xa95267fa), (0x10007dc1c,0xa9516ffc), (0x10007dc20,0x9105c3ff), (0x10007dc24,0xd65f03c0)]⟩
theorem shake_256f_params : shake_256f_path.params = Spec.ArmKeygen.parameterBytes Spec.shake_256f := by decide
theorem shake_256f_checked : inspect shake_256f_path = some ⟨Spec.shake_256f.sigBytes,0x10007da38,false⟩ := by decide
theorem shake_256f_validEdge : execute shake_256f_path Spec.shake_256f.sigBytes = some (.continued 0x10007da38) :=
  acceptedEdge shake_256f_checked (by decide)
def shake_256f_trace (msg sig pk : Spec.Bytes) (value : Bool)
    (actual : execute shake_256f_path sig.length = some (.returned value)) :
    LinkedArm.Signer.VerifyTrace Spec.shake_256f msg sig pk value :=
  toVerifyTrace shake_256f_checked msg sig pk value actual
def shake_256f_malformed (msg sig pk : Spec.Bytes) (fits : sig.length < 2^64)
    (bad : sig.length ≠ Spec.shake_256f.sigBytes) :
    LinkedArm.Signer.VerifyTrace Spec.shake_256f msg sig pk false :=
  shake_256f_trace msg sig pk false (rejects shake_256f_checked sig fits bad)

def shake_256f_toHash : List (Nat × Nat) := [(0x10007da38,0xf1007cdf), (0x10007da3c,0x54000f69), (0x10007da40,0xaa0503f9), (0x10007da44,0xad4004a0), (0x10007da48,0xad0087e0), (0x10007da4c,0xf100fcdf), (0x10007da50,0x54000f89), (0x10007da54,0xad410720), (0x10007da58,0xad0187e0), (0x10007da5c,0xf1007edf), (0x10007da60,0x54000fc9), (0x10007da64,0xaa0303f5), (0x10007da68,0xaa0203e5), (0x10007da6c,0xaa0103e4), (0x10007da70,0xaa0003f4), (0x10007da74,0xad400460), (0x10007da78,0xad0287e0), (0x10007da7c,0x9101e3e8), (0x10007da80,0x910143e1), (0x10007da84,0x910043e2), (0x10007da88,0x9100c3e3), (0x10007da8c,0x97ffe0ae)]
theorem shake_256f_hashCall : hashCall shake_256f_path Spec.shake_256f.n Spec.shake_256f.sigBytes
    0x100075d44 shake_256f_toHash = some (expectedCall Spec.shake_256f.n) := by decide
theorem shake_256f_digestPremise {call}
    (actual : hashCall shake_256f_path Spec.shake_256f.n Spec.shake_256f.sigBytes 0x100075d44 shake_256f_toHash = some call)
    (msg sig pk digest : Spec.Bytes) (sigSize : Spec.shake_256f.n ≤ sig.length)
    (pkSize : 2 * Spec.shake_256f.n ≤ pk.length)
    (target : let v := Spec.ArmKeygen.interpret (hashSources Spec.shake_256f sig pk)
      digest = Spec.Hmsg Spec.shake_256f (Spec.ArmKeygen.bytes v call.randomizer)
        (Spec.ArmKeygen.bytes v call.publicSeed) (Spec.ArmKeygen.bytes v call.publicRoot) msg) :
    digest = Spec.Hmsg Spec.shake_256f (sig.take Spec.shake_256f.n)
      (Spec.block Spec.shake_256f pk 0) (Spec.block Spec.shake_256f pk 1) msg :=
  digestPremise shake_256f_hashCall actual msg sig pk digest sigSize pkSize (by decide) (by decide) target

end LinkedAppleVerifyLength

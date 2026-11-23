import Spec.ArmPureFrame
namespace LinkedApplePureFrame
open Spec.ArmPureFrame
set_option maxHeartbeats 0
set_option maxRecDepth 65536
def image : Image := ⟨0x10007dce8,#[
0xd10183ff,0xa9025ff8,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xaa0303f6,0xaa0203f7,
0xaa0103f4,0xaa0003f5,0xaa0803f3,0x52800028,0xa900a3ff,0xf9000fff,0x910023e0,0x9401574e,
0xf9400be8,0x3900011f,0x52800028,0xf9000fe8,0xf94007e8,0xf100051f,0x54000061,0x910023e0,
0x94015745,0xf9400be8,0x39000516,0x52800048,0xf9000fe8,0xf94007e9,0xd1000928,0xeb0802df,
0x54000408,0x52800048,0xb4000116,0xf9400be9,0x8b080120,0xaa1703e1,0xaa1603e2,0x940159de,
0xf9400fe8,0xf94007e9,0x8b160101,0xcb010128,0xf9000fe1,0xeb08029f,0x54000348,0xb40000f4,
0xf9400be8,0x8b010100,0xaa1503e1,0xaa1403e2,0x940159d1,0xf9400fe1,0x8b140028,0x3cc083e0,
0x3d800260,0xf9000a68,0xa9457bfd,0xa9444ff4,0xa94357f6,0xa9425ff8,0x910183ff,0xd65f03c0,
0x910023e0,0x52800041,0xaa1603e2,0x52800023,0x52800024,0x940140c3,0xf9400fe8,0x17ffffdc,
0x910023e0,0xaa1403e2,0x52800023,0x52800024,0x940140bc,0xf9400fe1,0x17ffffe2,0xaa0003f3,
0xf94007e1,0xb4000081,0xf9400be0,0x52800022,0x97fe9d84,0xaa1303e0,0x94015931
],0x1000d3a5c,0x1000ce108,0x1000d44fc⟩
theorem checked (b : Choices) : run image b = some (expected b) := by
  rcases b with ⟨g,c,m,ec,em⟩
  cases g <;> cases c <;> cases m <;> cases ec <;> cases em <;> decide +kernel
theorem framed {b pieces} (h : run image b = some pieces) (m ctx : Spec.Bytes)
    (hc : b.emptyC = decide (ctx = [])) (hm : b.emptyM = decide (m = [])) :
    pieces.flatMap (bytes m ctx) = Spec.withContext m ctx := of_run (checked b) h m ctx hc hm
theorem wrongDomain : run {image with words := image.words.set! 17 0x39000116} (choices 0) ≠
    some (expected (choices 0)) := by decide +kernel
theorem wrongContextByte : run {image with words := image.words.set! 26 0x39000514} (choices 0) ≠
    some (expected (choices 0)) := by decide +kernel
theorem wrongContextCopyLength : run {image with words := image.words.set! 38 0xaa1403e2} (choices 0) ≠
    some (expected (choices 0)) := by decide +kernel
theorem wrongMessageSource : run {image with words := image.words.set! 50 0xaa1703e1} (choices 0) ≠
    some (expected (choices 0)) := by decide +kernel
theorem wrongGrowthBranch : run {image with words := image.words.set! 22 0x54000068} (choices 1) ≠
    some (expected (choices 1)) := by decide +kernel
theorem wrongReserveLength : run {image with words := image.words.set! 73 0xaa1603e2} (choices 4) ≠
    some (expected (choices 4)) := by decide +kernel
#print axioms framed
end LinkedApplePureFrame

import Spec.ArmSha2PublicVerify
import Spec.AppleSha2VerifyWitness
namespace LinkedAppleSha2PublicVerify
open Spec.ArmSha2PublicVerify
set_option maxRecDepth 65536
set_option maxHeartbeats 0
def dispatcher16 : Array Nat := #[0xd10183ff,0xa9025ff8,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xf103fcdf,0x54000069,
0x52800000,0x14000028,0xaa0403f3,0xaa0303f5,0xf9400bb6,0xf10ffc5f,0x54000189,0xf9000bb6,
0xaa0503e3,0xaa0603e4,0xaa1503e5,0xaa1303e6,0xa9457bfd,0xa9444ff4,0xa94357f6,0xa9425ff8,
0x910183ff,0x17ffd794,0x910023e8,0xaa0003f7,0xaa0103e0,0xaa0203e1,0xaa0503e2,0xaa0603e3,
0xaa0703f8,0x94000ff6,0xa9410bf4,0xaa1703e0,0xaa1403e1,0xaa1503e3,0xaa1303e4,0xaa1803e5,
0xaa1603e6,0x9400054a,0xf94007e1,0xb40000c1,0xaa0003f3,0xaa1403e0,0x52800022,0x97feadc0,
0xaa1303e0,0xa9457bfd,0xa9444ff4,0xa94357f6,0xa9425ff8,0x910183ff,0xd65f03c0,0xaa0003f3,
0xf94007e1,0xb4000081,0xaa1403e0,0x52800022,0x97feadb3,0xaa1303e0,0x94016960]
def segmented16 : Array Nat := #[0xd10743ff,0xa9176ffc,0xa91867fa,0xa9195ff8,0xa91a57f6,0xa91b4ff4,0xa91c7bfd,0x910703fd,
0xaa0603f7,0xf940001c,0x2943d015,0x1b155293,0x2942a009,0xa905a3e9,0x8b1c0508,0x91000d1a,
0x9b094f48,0x9b087388,0xeb0800df,0x54000f21,0xf9400ba8,0xf1003d1f,0x54001a89,0xf1007d1f,
0x54001b09,0xf1003eff,0x54001b89,0xaa0503f9,0xaa0403e6,0xaa0303e5,0xaa0103ea,0x3dc000e0,
0x3d800fe0,0xaa0703e4,0xa9c16088,0xf90017e8,0xf9400401,0xf90003e2,0xaa0003f6,0x9101a3e0,
0xaa1903e2,0xaa0703fb,0xaa0703e3,0xaa0a03e7,0x97fffe94,0xaa1603e0,0xa94723f1,0x528000e9,
0x1b1426a9,0x53037d24,0xb94012c9,0xf94033ea,0x4b0a0129,0x11001d2a,0x53037d4a,0x8b040156,
0xeb0802df,0xf90027f1,0x54001848,0xf90013fa,0xaa1903e1,0xd280000b,0x340000ea,0x8b04022c,
0xaa0a03ed,0x3840158e,0xaa0b21cb,0xf10005ad,0x54ffffa1,0xf94033ec,0x11001d8c,0x53037d8c,
0xb04015a,0x8b0c0356,0xeb0802df,0x540016c8,0x9b137f82,0x91004056,0x4b0903e8,0x9ac82169,
0x9ac82533,0xf9000ffc,0xd2800009,0x340000cc,0x8b1a0228,0x3840150a,0xaa092149,0xf100058c,
0x54ffffa1,0xd2800008,0x910283f4,0xd2c0006a,0xa9082bf3,0xf94033eb,0x9240156a,0xf9002bea,
0x9280000a,0x2912ffff,0x9acb215c,0xa3c0139,0xb90093f9,0x3dc00fe0,0x6e200800,0x6f00e401,
0xad0507e0,0xad0607e1,0x910283ea,0xd0000329,0x3dc3cd20,0xb000036c,0x9111c18c,0xd000032b,
0x3dc3d161,0x1400000a,0x3ce87983,0x4ea28463,0x4ea11c22,0x5e034002,0x5e035020,0x4ea21c41,
0xaa0d03e8,0xf10041bf,0x54000280,0x9240050e,0x3cee7942,0x9100050d,0xf100311f,0x54fffe62,
0x924005af,0x3cef7943,0x4ea21c44,0x5e282864,0x5100050f,0xd27f01d0,0x3cf07943,0x924005ef,
0x3cef7945,0x5e056064,0x3cae7944,0x17ffffe7,0x52800000,0x1400004c,0x3dc3d161,0x4ea18441,
0x3dc3cd22,0x4ea28400,0x6f00e402,0xad050be2,0xad060be2,0x3dc00362,0x3d803be1,0xad028a80,
0x90000543,0x91266063,0x5280021a,0xb100445f,0x54000928,0xf9001bf8,0xeb1602f8,0x540008c3,
0xd102c3a8,0xaa0103f5,0x91004021,0x910283e5,0x910203e6,0xf94027e3,0x940045d1,0x3dc01e80,
0x3d802280,0xf9402fe8,0x34000448,0xd280001a,0xd2800017,0xf9000bf8,0x8b1602bb,0xa941a7e8,
0x9b087d36,0xd10243b5,0xb81783b7,0xf81703b3,0xf80142bf,0xf800c2bf,0xab1a02c8,0x54000542,
0xeb18011f,0x54000508,0xd101c3a0,0x8b1a0363,0xd10283a5,0x910283e6,0xd10243a7,0xf94033e1,
0xaa1903e2,0xaa1603e4,0x94001182,0x3dc02e80,0x3d802280,0xa3c0279,0xa94523e9,0x9ac92673,
0x910006f7,0x8b16035a,0xeb17011f,0x54fffce1,0xa97623a9,0xf94017ea,0xeb0a013f,0xf9401be9,
0xfa490100,0x1a9f17e0,0xf94037e1,0xb40000c1,0xaa0003f3,0xf94027e0,0x52800022,0x97fed56b,
0xaa1303e0,0xa95c7bfd,0xa95b4ff4,0xa95a57f6,0xa9595ff8,0xa95867fa,0xa9576ffc,0x910743ff,
0xd65f03c0,0x8b1a02d6,0x90000543,0x91290063,0xf9400bf7,0xaa1a03e0,0xaa1603e1,0xaa1703e2,
0x94019066,0xd4200020,0x90000543,0x912d2063,0xd2800000,0x52800201,0xaa0803e2,0x9401905f,
0x90000543,0x912d2063,0x52800200,0x52800401,0xaa0803e2,0x94019059,0x90000543,0x912d2063,
0xd2800000,0x52800201,0xaa1703e2,0x94019053,0x90000543,0x91338063,0xaa0403fa,0xaa0803f7,
0x17ffffe5,0x90000543,0x91332063,0xaa0803f7,0x17ffffe1,0x14000001,0xf94037e1,0xf94027e8,
0xb40000c1,0xaa0003f3,0xaa0803e0,0x52800022,0x97fed536,0xaa1303e0,0x940190e3]
def sha2_128s_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800408,0xf90003e8,0xf0000320,0x910ac000,0x94000c59,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_128s_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_128s_image,0x100076af0,sha2_128s_verifyWords,0x100079c8c,dispatcher16,0x10006fb40,segmented16,0x10006f640⟩
def sha2_128s_slh_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800408,0xf90003e8,0xf0000320,0x910ac000,0x94000cbe,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_128s_slh_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_128s_image,0x10007695c,sha2_128s_slh_verifyWords,0x100079c8c,dispatcher16,0x10006fb40,segmented16,0x10006f640⟩
def sha2_128f_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800408,0xf90003e8,0x90000320,0x910ec000,0x9400020d,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_128f_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_128f_image,0x100079420,sha2_128f_verifyWords,0x100079c8c,dispatcher16,0x10006fb40,segmented16,0x10006f640⟩
def sha2_128f_slh_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800408,0xf90003e8,0x90000320,0x910ec000,0x94000272,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_128f_slh_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_128f_image,0x10007928c,sha2_128f_slh_verifyWords,0x100079c8c,dispatcher16,0x10006fb40,segmented16,0x10006f640⟩
def dispatcher24 : Array Nat := #[0xd10183ff,0xa9025ff8,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xf103fcdf,0x54000069,
0x52800000,0x14000028,0xaa0403f3,0xaa0303f5,0xf9400bb6,0xf10ffc5f,0x54000189,0xf9000bb6,
0xaa0503e3,0xaa0603e4,0xaa1503e5,0xaa1303e6,0xa9457bfd,0xa9444ff4,0xa94357f6,0xa9425ff8,
0x910183ff,0x17ffd864,0x910023e8,0xaa0003f7,0xaa0103e0,0xaa0203e1,0xaa0503e2,0xaa0603e3,
0xaa0703f8,0x94000fb7,0xa9410bf4,0xaa1703e0,0xaa1403e1,0xaa1503e3,0xaa1303e4,0xaa1803e5,
0xaa1603e6,0x9400060e,0xf94007e1,0xb40000c1,0xaa0003f3,0xaa1403e0,0x52800022,0x97fead81,
0xaa1303e0,0xa9457bfd,0xa9444ff4,0xa94357f6,0xa9425ff8,0x910183ff,0xd65f03c0,0xaa0003f3,
0xf94007e1,0xb4000081,0xaa1403e0,0x52800022,0x97fead74,0xaa1303e0,0x94016921]
def segmented24 : Array Nat := #[0xd10583ff,0xa9106ffc,0xa91167fa,0xa9125ff8,0xa91357f6,0xa9144ff4,0xa9157bfd,0x910543fd,
0xaa0603f7,0xf940001c,0x2943e019,0x1b196313,0x2942ec08,0x8b1c0769,0x91000d29,0x9b084d28,
0x9b087388,0xeb0800df,0x54000d21,0xf9400ba8,0xf1005d1f,0x54000de9,0xaa0703f4,0x3dc000e0,
0x3d8007e0,0xf94008e9,0xf90013e9,0xf100bd1f,0x54000dc9,0xf1005eff,0x54000e49,0xaa0503f6,
0xaa0403e6,0xaa0303e5,0xaa0103e7,0xaa0003f5,0xf9400401,0xf90003e2,0x9100c3e0,0x91006284,
0xaa1603e2,0xaa1403e3,0x97fffdec,0xa943a3ef,0x528000e9,0x1b182729,0x53037d38,0xb94012a9,
0x4b1b0129,0x11001d2a,0x53037d4a,0x8b18015a,0xeb08035f,0xf90007ef,0x54000c08,0xd280000b,
0x340000ea,0x8b1801ec,0xaa0a03ed,0x3840158e,0xaa0b21cb,0xf10005ad,0x54ffffa1,0x11001f6c,
0x53037d8c,0xb180140,0x8b0c001a,0xeb08035f,0x54000ac8,0x4b0903e8,0x9ac82169,0x9ac82539,
0xd2800008,0x340000cc,0x8b0001e9,0x3840152a,0xaa082148,0xf100058c,0x54ffffa1,0x92800009,
0x9adb2129,0xd2c0006a,0xa904abf9,0xa29011b,0x290bffff,0xb9005bfb,0x9101a3e8,0x910043e0,
0x97ffe06f,0x9b137f82,0x9100605a,0xf0000523,0x91266063,0x52800300,0xb100645f,0x540007c8,
0xeb1a02fc,0x54000783,0xd101c3a8,0x910062c1,0x9101a3e5,0x910123e6,0xaa1503e0,0xf94007e3,
0xaa1803e4,0x9400466e,0xd101c3a1,0x8b1a02c2,0x9101a3e4,0x91006287,0xaa1503e0,0xaa1c03e3,
0xaa1903e5,0xaa1b03e6,0x94000fa7,0xf9401be1,0xb4000101,0xaa0003f3,0xf94007e0,0x52800022,
0x97fed4bb,0xaa1303e0,0x14000002,0x52800000,0xa9557bfd,0xa9544ff4,0xa95357f6,0xa9525ff8,
0xa95167fa,0xa9506ffc,0x910583ff,0xd65f03c0,0xf0000523,0x912d2063,0xd2800000,0x52800301,
0xaa0803e2,0x94018fb6,0xf0000523,0x912d2063,0x52800300,0x52800601,0xaa0803e2,0x94018fb0,
0xf0000523,0x912d2063,0xd2800000,0x52800301,0xaa1703e2,0x94018faa,0xf0000523,0x91338063,
0xaa1803e0,0x14000003,0xf0000523,0x91332063,0xaa0803f7,0xaa1a03e1,0xaa1703e2,0x94018fa0,
0xd4200020,0xf9401be1,0xb40000c1,0xaa0003f3,0xf94007e0,0x52800022,0x97fed48d,0xaa1303e0,
0x9401903a]
def sha2_192s_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800608,0xf90003e8,0xd0000340,0x91098000,0x9400196e,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_192s_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_192s_image,0x100073798,sha2_192s_verifyWords,0x100079d88,dispatcher24,0x10006ff7c,segmented24,0x10006f7d4⟩
def sha2_192s_slh_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800608,0xf90003e8,0xd0000340,0x91098000,0x940019db,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_192s_slh_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_192s_image,0x1000735e4,sha2_192s_slh_verifyWords,0x100079d88,dispatcher24,0x10006ff7c,segmented24,0x10006f7d4⟩
def sha2_192f_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800608,0xf90003e8,0xd0000340,0x9108e000,0x940019f7,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_192f_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_192f_image,0x100073574,sha2_192f_verifyWords,0x100079d88,dispatcher24,0x10006ff7c,segmented24,0x10006f7d4⟩
def sha2_192f_slh_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800608,0xf90003e8,0xd0000340,0x9108e000,0x94001a64,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_192f_slh_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_192f_image,0x1000733c0,sha2_192f_slh_verifyWords,0x100079d88,dispatcher24,0x10006ff7c,segmented24,0x10006f7d4⟩
def dispatcher32 : Array Nat := #[0xd10183ff,0xa9025ff8,0xa90357f6,0xa9044ff4,0xa9057bfd,0x910143fd,0xf103fcdf,0x54000069,
0x52800000,0x14000028,0xaa0403f3,0xaa0303f5,0xf9400bb6,0xf10ffc5f,0x54000189,0xf9000bb6,
0xaa0503e3,0xaa0603e4,0xaa1503e5,0xaa1303e6,0xa9457bfd,0xa9444ff4,0xa94357f6,0xa9425ff8,
0x910183ff,0x17ffd8ce,0x910023e8,0xaa0003f7,0xaa0103e0,0xaa0203e1,0xaa0503e2,0xaa0603e3,
0xaa0703f8,0x94000f78,0xa9410bf4,0xaa1703e0,0xaa1403e1,0xaa1503e3,0xaa1303e4,0xaa1803e5,
0xaa1603e6,0x9400067c,0xf94007e1,0xb40000c1,0xaa0003f3,0xaa1403e0,0x52800022,0x97fead42,
0xaa1303e0,0xa9457bfd,0xa9444ff4,0xa94357f6,0xa9425ff8,0x910183ff,0xd65f03c0,0xaa0003f3,
0xf94007e1,0xb4000081,0xaa1403e0,0x52800022,0x97fead35,0xaa1303e0,0x940168e2]
def segmented32 : Array Nat := #[0xd105c3ff,0xa9116ffc,0xa91267fa,0xa9135ff8,0xa91457f6,0xa9154ff4,0xa9167bfd,0x910583fd,
0xaa0603f7,0xf940001c,0x2943e019,0x1b196313,0x2942ec08,0x8b1c0769,0x91000d29,0x9b084d28,
0x9b087388,0xeb0800df,0x54000ce1,0xf9400ba8,0xf1007d1f,0x54000da9,0xaa0703f4,0xad4004e0,
0xad0087e0,0xf100fd1f,0x54000dc9,0xf1007eff,0x54000e49,0xaa0503f6,0xaa0403e6,0xaa0303e5,
0xaa0103e7,0xaa0003f5,0xf9400401,0xf90003e2,0x9100c3e0,0x91008284,0xaa1603e2,0xaa1403e3,
0x97fffdb9,0xa943a3ef,0x528000e9,0x1b182729,0x53037d38,0xb94012a9,0x4b1b0129,0x11001d2a,
0x53037d4a,0x8b18015a,0xeb08035f,0xf90007ef,0x54000c08,0xd280000b,0x340000ea,0x8b1801ec,
0xaa0a03ed,0x3840158e,0xaa0b21cb,0xf10005ad,0x54ffffa1,0x11001f6c,0x53037d8c,0xb180140,
0x8b0c001a,0xeb08035f,0x54000ac8,0x4b0903e8,0x9ac82169,0x9ac82539,0xd2800008,0x340000cc,
0x8b0001e9,0x3840152a,0xaa082148,0xf100058c,0x54ffffa1,0x92800009,0x9adb2129,0xd2c0006a,
0xa904abf9,0xa29011b,0x290bffff,0xb9005bfb,0x9101a3e8,0x910043e0,0x97ffe040,0x9b137f82,
0x9100805a,0xf0000523,0x91266063,0x52800400,0xb100845f,0x540007c8,0xeb1a02fc,0x54000783,
0xd101e3a8,0x910082c1,0x9101a3e5,0x910123e6,0xaa1503e0,0xf94007e3,0xaa1803e4,0x9400472e,
0xd101e3a1,0x8b1a02c2,0x9101a3e4,0x91008287,0xaa1503e0,0xaa1c03e3,0xaa1903e5,0xaa1b03e6,
0x94000f4f,0xf9401be1,0xb4000101,0xaa0003f3,0xf94007e0,0x52800022,0x97fed414,0xaa1303e0,
0x14000002,0x52800000,0xa9567bfd,0xa9554ff4,0xa95457f6,0xa9535ff8,0xa95267fa,0xa9516ffc,
0x9105c3ff,0xd65f03c0,0xf0000523,0x912d2063,0xd2800000,0x52800401,0xaa0803e2,0x94018f0f,
0xf0000523,0x912d2063,0x52800400,0x52800801,0xaa0803e2,0x94018f09,0xf0000523,0x912d2063,
0xd2800000,0x52800401,0xaa1703e2,0x94018f03,0xf0000523,0x91338063,0xaa1803e0,0x14000003,
0xf0000523,0x91332063,0xaa0803f7,0xaa1a03e1,0xaa1703e2,0x94018ef9,0xd4200020,0xf9401be1,
0xb40000c1,0xaa0003f3,0xf94007e0,0x52800022,0x97fed3e6,0xaa1303e0,0x94018f93]
def sha2_256s_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800808,0xf90003e8,0x90000320,0x910e2000,0x94000201,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_256s_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_256s_image,0x100079648,sha2_256s_verifyWords,0x100079e84,dispatcher32,0x100070220,segmented32,0x10006f9a4⟩
def sha2_256s_slh_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800808,0xf90003e8,0x90000320,0x910e2000,0x9400026f,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_256s_slh_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_256s_image,0x100079490,sha2_256s_slh_verifyWords,0x100079e84,dispatcher32,0x100070220,segmented32,0x10006f9a4⟩
def sha2_256f_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800808,0xf90003e8,0xf00002e0,0x91126000,0x97ffef94,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_256f_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_256f_image,0x10007dffc,sha2_256f_verifyWords,0x100079e84,dispatcher32,0x100070220,segmented32,0x10006f9a4⟩
def sha2_256f_slh_verifyWords : Array Nat := #[0xd10083ff,0xa9017bfd,0x910043fd,0xaa0603e7,0xaa0503e6,0xaa0403e5,0xaa0303e4,0xaa0203e3,
0xaa0103e2,0xaa0003e1,0x52800808,0xf90003e8,0x90000300,0x91126000,0x97fff002,0xa9417bfd,
0x910083ff,0xd65f03c0]
def sha2_256f_slh_verify : Image := ⟨LinkedAppleSha2VerifyBody.sha2_256f_image,0x10007de44,sha2_256f_slh_verifyWords,0x100079e84,dispatcher32,0x100070220,segmented32,0x10006f9a4⟩
theorem sha2_128s_verify_paths (c m s : Bool) : run sha2_128s_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_128s_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_128s (input msg ctx choices) sig pk) :
    verified (a := sha2_128s_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_128s msg sig ctx pk) :=
  valid_eq sha2_128s_verify_paths LinkedAppleSha2VerifyBody.sha2_128s_checked (by decide) v
theorem sha2_128s_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_128s.sigBytes) (core : Bool) :
    (evaluate sha2_128s_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_128s msg sig ctx pk) :=
  malformed_eq sha2_128s_verify_paths msg ctx sig pk h core
theorem sha2_128s_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_128s_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_128s_verify_paths msg ctx sig h
theorem sha2_128s_slh_verify_paths (c m s : Bool) : run sha2_128s_slh_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_128s_slh_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_128s (input msg ctx choices) sig pk) :
    verified (a := sha2_128s_slh_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_128s msg sig ctx pk) :=
  valid_eq sha2_128s_slh_verify_paths LinkedAppleSha2VerifyBody.sha2_128s_checked (by decide) v
theorem sha2_128s_slh_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_128s.sigBytes) (core : Bool) :
    (evaluate sha2_128s_slh_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_128s msg sig ctx pk) :=
  malformed_eq sha2_128s_slh_verify_paths msg ctx sig pk h core
theorem sha2_128s_slh_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_128s_slh_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_128s_slh_verify_paths msg ctx sig h
theorem sha2_128f_verify_paths (c m s : Bool) : run sha2_128f_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_128f_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_128f (input msg ctx choices) sig pk) :
    verified (a := sha2_128f_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_128f msg sig ctx pk) :=
  valid_eq sha2_128f_verify_paths LinkedAppleSha2VerifyBody.sha2_128f_checked (by decide) v
theorem sha2_128f_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_128f.sigBytes) (core : Bool) :
    (evaluate sha2_128f_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_128f msg sig ctx pk) :=
  malformed_eq sha2_128f_verify_paths msg ctx sig pk h core
theorem sha2_128f_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_128f_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_128f_verify_paths msg ctx sig h
theorem sha2_128f_slh_verify_paths (c m s : Bool) : run sha2_128f_slh_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_128f_slh_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_128f (input msg ctx choices) sig pk) :
    verified (a := sha2_128f_slh_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_128f msg sig ctx pk) :=
  valid_eq sha2_128f_slh_verify_paths LinkedAppleSha2VerifyBody.sha2_128f_checked (by decide) v
theorem sha2_128f_slh_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_128f.sigBytes) (core : Bool) :
    (evaluate sha2_128f_slh_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_128f msg sig ctx pk) :=
  malformed_eq sha2_128f_slh_verify_paths msg ctx sig pk h core
theorem sha2_128f_slh_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_128f_slh_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_128f_slh_verify_paths msg ctx sig h
theorem sha2_192s_verify_paths (c m s : Bool) : run sha2_192s_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_192s_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_192s (input msg ctx choices) sig pk) :
    verified (a := sha2_192s_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_192s msg sig ctx pk) :=
  valid_eq sha2_192s_verify_paths LinkedAppleSha2VerifyBody.sha2_192s_checked (by decide) v
theorem sha2_192s_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_192s.sigBytes) (core : Bool) :
    (evaluate sha2_192s_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_192s msg sig ctx pk) :=
  malformed_eq sha2_192s_verify_paths msg ctx sig pk h core
theorem sha2_192s_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_192s_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_192s_verify_paths msg ctx sig h
theorem sha2_192s_slh_verify_paths (c m s : Bool) : run sha2_192s_slh_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_192s_slh_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_192s (input msg ctx choices) sig pk) :
    verified (a := sha2_192s_slh_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_192s msg sig ctx pk) :=
  valid_eq sha2_192s_slh_verify_paths LinkedAppleSha2VerifyBody.sha2_192s_checked (by decide) v
theorem sha2_192s_slh_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_192s.sigBytes) (core : Bool) :
    (evaluate sha2_192s_slh_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_192s msg sig ctx pk) :=
  malformed_eq sha2_192s_slh_verify_paths msg ctx sig pk h core
theorem sha2_192s_slh_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_192s_slh_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_192s_slh_verify_paths msg ctx sig h
theorem sha2_192f_verify_paths (c m s : Bool) : run sha2_192f_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_192f_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_192f (input msg ctx choices) sig pk) :
    verified (a := sha2_192f_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_192f msg sig ctx pk) :=
  valid_eq sha2_192f_verify_paths LinkedAppleSha2VerifyBody.sha2_192f_checked (by decide) v
theorem sha2_192f_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_192f.sigBytes) (core : Bool) :
    (evaluate sha2_192f_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_192f msg sig ctx pk) :=
  malformed_eq sha2_192f_verify_paths msg ctx sig pk h core
theorem sha2_192f_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_192f_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_192f_verify_paths msg ctx sig h
theorem sha2_192f_slh_verify_paths (c m s : Bool) : run sha2_192f_slh_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_192f_slh_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_192f (input msg ctx choices) sig pk) :
    verified (a := sha2_192f_slh_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_192f msg sig ctx pk) :=
  valid_eq sha2_192f_slh_verify_paths LinkedAppleSha2VerifyBody.sha2_192f_checked (by decide) v
theorem sha2_192f_slh_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_192f.sigBytes) (core : Bool) :
    (evaluate sha2_192f_slh_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_192f msg sig ctx pk) :=
  malformed_eq sha2_192f_slh_verify_paths msg ctx sig pk h core
theorem sha2_192f_slh_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_192f_slh_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_192f_slh_verify_paths msg ctx sig h
theorem sha2_256s_verify_paths (c m s : Bool) : run sha2_256s_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_256s_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_256s (input msg ctx choices) sig pk) :
    verified (a := sha2_256s_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_256s msg sig ctx pk) :=
  valid_eq sha2_256s_verify_paths LinkedAppleSha2VerifyBody.sha2_256s_checked (by decide) v
theorem sha2_256s_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_256s.sigBytes) (core : Bool) :
    (evaluate sha2_256s_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_256s msg sig ctx pk) :=
  malformed_eq sha2_256s_verify_paths msg ctx sig pk h core
theorem sha2_256s_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_256s_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_256s_verify_paths msg ctx sig h
theorem sha2_256s_slh_verify_paths (c m s : Bool) : run sha2_256s_slh_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_256s_slh_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_256s (input msg ctx choices) sig pk) :
    verified (a := sha2_256s_slh_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_256s msg sig ctx pk) :=
  valid_eq sha2_256s_slh_verify_paths LinkedAppleSha2VerifyBody.sha2_256s_checked (by decide) v
theorem sha2_256s_slh_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_256s.sigBytes) (core : Bool) :
    (evaluate sha2_256s_slh_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_256s msg sig ctx pk) :=
  malformed_eq sha2_256s_slh_verify_paths msg ctx sig pk h core
theorem sha2_256s_slh_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_256s_slh_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_256s_slh_verify_paths msg ctx sig h
theorem sha2_256f_verify_paths (c m s : Bool) : run sha2_256f_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_256f_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_256f (input msg ctx choices) sig pk) :
    verified (a := sha2_256f_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_256f msg sig ctx pk) :=
  valid_eq sha2_256f_verify_paths LinkedAppleSha2VerifyBody.sha2_256f_checked (by decide) v
theorem sha2_256f_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_256f.sigBytes) (core : Bool) :
    (evaluate sha2_256f_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_256f msg sig ctx pk) :=
  malformed_eq sha2_256f_verify_paths msg ctx sig pk h core
theorem sha2_256f_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_256f_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_256f_verify_paths msg ctx sig h
theorem sha2_256f_slh_verify_paths (c m s : Bool) : run sha2_256f_slh_verify c m s = some (route c m s) := by
  cases c <;> cases m <;> cases s <;> decide +kernel
theorem sha2_256f_slh_verify_eq {msg ctx sig pk : Spec.Bytes} {choices : Fin 8}
    (v : Spec.ArmSha2Verify.Callees Spec.sha2_256f (input msg ctx choices) sig pk) :
    verified (a := sha2_256f_slh_verify) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.sha2_256f msg sig ctx pk) :=
  valid_eq sha2_256f_slh_verify_paths LinkedAppleSha2VerifyBody.sha2_256f_checked (by decide) v
theorem sha2_256f_slh_verify_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.sha2_256f.sigBytes) (core : Bool) :
    (evaluate sha2_256f_slh_verify msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.sha2_256f msg sig ctx pk) :=
  malformed_eq sha2_256f_slh_verify_paths msg ctx sig pk h core
theorem sha2_256f_slh_verify_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate sha2_256f_slh_verify msg ctx sig = some .contextRejected :=
  oversized_ctx sha2_256f_slh_verify_paths msg ctx sig h
theorem contextBound_mutation : run { sha2_128s_verify with dispatchWords := dispatcher16.set! 6 (dispatcher16[6]! ^^^ 1024) } true true true ≠ some .framed := by decide +kernel
theorem messageBound_mutation : run { sha2_128s_verify with dispatchWords := dispatcher16.set! 13 (dispatcher16[13]! ^^^ 1024) } true true true ≠ some .framed := by decide +kernel
theorem framedSignature_mutation : run { sha2_128s_verify with dispatchWords := dispatcher16.set! 37 (dispatcher16[37]! ^^^ 65536) } true true true ≠ some .framed := by decide +kernel
theorem segmentedCtx_mutation : run { sha2_128s_verify with segmentedWords := segmented16.set! 28 (segmented16[28]! ^^^ 65536) } true false true ≠ some .segmented := by decide +kernel
theorem segmentedSeed_mutation : run { sha2_128s_verify with segmentedWords := segmented16.set! 118 (segmented16[118]! ^^^ 4096) } true false true ≠ some .segmented := by decide +kernel
theorem rootCompare_mutation : run { sha2_128s_verify with segmentedWords := segmented16.set! 208 (segmented16[208]! ^^^ 65536) } true false true ≠ some .segmented := by decide +kernel
#print axioms sha2_128s_verify_eq
#print axioms sha2_192s_verify_eq
#print axioms sha2_256s_verify_eq
end LinkedAppleSha2PublicVerify

import Integration.SlhDsaComposedClosedNum

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum Reduction

#check @Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed
#check @Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed
#check @Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed_num
#check @Reduction.Num.composedBoundFinal_num
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed_num
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed_num
#print axioms Reduction.Num.composedBoundFinal_num
-- parameters
example : Link.vp.params.n = 16 ∧ Link.vp.params.m = 30 ∧ Link.vp.params.h = 63 ∧ Link.vp.params.a = 12 ∧ Link.vp.params.k = 14 ∧ Link.vp.params.w = 16 ∧ Link.vp.params.len = 35 := by decide
#print Reduction.PortForger
#print Reduction.Caps

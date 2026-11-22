import MReduction.Headline
import MReduction.Linear
import MReduction.Resources

/-!
# At `.s128s` the statements are those of `security/Reduction`

Each `example` type-checks only if the two statements are definitionally equal (including the
`Inhabited`/`Fintype` instances on `Bytes 16`).
-/

example : @MReduction.slhdsa_sha2_128s_bytes_suf_cma_final =
    @Reduction.slhdsa_sha2_128s_bytes_suf_cma_final := rfl
example : @MReduction.slhdsa_sha2_128s_bytes_euf_cma_final =
    @Reduction.slhdsa_sha2_128s_bytes_euf_cma_final := rfl
example : @MReduction.slhdsa_sha2_128s_pure_bytes_suf_cma_final =
    @Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_final := rfl
example : @MReduction.slhdsa_sha2_128s_pure_bytes_euf_cma_final =
    @Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_final := rfl
example : @MReduction.slhdsa_sha2_128s_suf_cma_final_memo =
    @Reduction.slhdsa_sha2_128s_suf_cma_final_memo := rfl
example : @MReduction.slhdsa_sha2_128s_bytes_suf_cma_deterministic =
    @Reduction.slhdsa_sha2_128s_bytes_suf_cma_deterministic := rfl
example : @MReduction.slhdsa_sha2_128s_pure_bytes_suf_cma_hedged =
    @Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_hedged := rfl
example : @MReduction.slhdsa_sha2_128s_bytes_suf_cma_linear =
    @Reduction.slhdsa_bytes_suf_cma_linear_128s := rfl
example : @MReduction.final_resources_final_128s = @Reduction.final_resources_final_128s := rfl
example : @MReduction.slhdsa_sha2_bytes_suf_cma_final .s128s =
    @Reduction.slhdsa_sha2_128s_bytes_suf_cma_final := rfl

#check @MReduction.slhdsa_sha2_256f_bytes_suf_cma_final
#check @MReduction.slhdsa_sha2_192s_pure_bytes_euf_cma_deterministic

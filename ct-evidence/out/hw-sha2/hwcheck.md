### SHA-256 instructions executed under the emulator

crate under test: `slhdsa` built with `--features hw-sha2` (`sha256::hw_active()` = true), cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

| entry point | insns executed | SHA256H | SHA256H2 | SHA256SU0 | SHA256SU1 | emu==native output | verdict |
|---|---|---|---|---|---|---|---|
| sha256/len=64 | 1868 | 32 | 32 | 24 | 24 | yes | as expected |
| compress (copy inlined into the wrapper) | 392 | 16 | 16 | 12 | 12 | yes | as expected |
| thash_short/len=16 | 495 | 16 | 16 | 12 | 12 | yes | as expected |
| thash/len=224 | 2124 | 64 | 64 | 48 | 48 | yes | as expected |
| thash_values | 4071 | 160 | 160 | 120 | 120 | yes | as expected |
| prf_msg/mlen=32 | 2721 | 64 | 64 | 48 | 48 | yes | as expected |
| chain_blocks/n=1,steps=0..15 | 1877 | 226 | 211 | 180 | 180 | yes | as expected |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | 37889 | 4231 | 3949 | 3384 | 3384 | yes | as expected |
| chain_blocks_portable/n=4,steps=0..15 | 23290 | 960 | 960 | 720 | 720 | yes | as expected |
| wots_pk_gen | 75867 | 8562 | 8002 | 6840 | 6840 | yes | as expected |
| fors_node/z=7 | 82912 | 5754 | 5371 | 4596 | 4596 | yes | as expected |
| slh_keygen_internal | 39104965 | 4391936 | 4105216 | 3508224 | 3508224 | yes | as expected |
| slh::slh_sign_internal | 311239549 | 33328712 | 31150032 | 26621856 | 26621856 | yes | as expected |

SHA-256 instructions present in this binary's `__text` section (static count): SHA256H 315, SHA256H2 295, SHA256SU0 254, SHA256SU1 254.

overall: AS EXPECTED

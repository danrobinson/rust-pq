### SHA-256 instructions executed under the emulator

crate under test: `slhdsa` built with default features, cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

| entry point | insns executed | SHA256H | SHA256H2 | SHA256SU0 | SHA256SU1 | emu==native output | verdict |
|---|---|---|---|---|---|---|---|
| sha256/len=64 | 7520 | 0 | 0 | 0 | 0 | yes | as expected |
| compress (copy inlined into the wrapper) | 3207 | 0 | 0 | 0 | 0 | yes | as expected |
| thash_short/len=16 | 3252 | 0 | 0 | 0 | 0 | yes | as expected |
| thash/len=224 | 13360 | 0 | 0 | 0 | 0 | yes | as expected |
| thash_values | 32042 | 0 | 0 | 0 | 0 | yes | as expected |
| prf_msg/mlen=32 | 14107 | 0 | 0 | 0 | 0 | yes | as expected |
| chain_blocks/n=1,steps=0..15 | 43776 | 0 | 0 | 0 | 0 | yes | as expected |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | 822717 | 0 | 0 | 0 | 0 | yes | as expected |
| chain_blocks_portable/n=4,steps=0..15 | 174740 | 0 | 0 | 0 | 0 | yes | as expected |
| wots_pk_gen | 1666912 | 0 | 0 | 0 | 0 | yes | as expected |
| fors_node/z=7 | 1173585 | 0 | 0 | 0 | 0 | yes | as expected |
| slh_keygen_internal | 855131659 | 0 | 0 | 0 | 0 | yes | as expected |
| slh::slh_sign_internal | 6513220472 | 0 | 0 | 0 | 0 | yes | as expected |

SHA-256 instructions present in this binary's `__text` section (static count): SHA256H 0, SHA256H2 0, SHA256SU0 0, SHA256SU1 0.

overall: AS EXPECTED

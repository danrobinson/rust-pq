crate under test: `slhdsa` built with default features, cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

| function (public params) | varied input | public configs | pairs | identical traces | differing | insns/run | blocks/run | mem accesses/run | call-outs/run | emu==native output | verdict |
|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 1 | 65 | 65 | 0 | 4361 | 351 | 952 | 6 | yes | PASS (all identical) |
| sha256/len=16 | all message bytes | 1 | 65 | 65 | 0 | 4112 | 305 | 867 | 5 | yes | PASS (all identical) |
| sha256/len=55 | all message bytes | 1 | 65 | 65 | 0 | 3552 | 214 | 685 | 4 | yes | PASS (all identical) |
| sha256/len=56 | all message bytes | 1 | 65 | 65 | 0 | 7604 | 510 | 1428 | 5 | yes | PASS (all identical) |
| sha256/len=64 | all message bytes | 1 | 65 | 65 | 0 | 7520 | 569 | 1407 | 5 | yes | PASS (all identical) |
| sha256/len=119 | all message bytes | 1 | 65 | 65 | 0 | 6732 | 434 | 1149 | 4 | yes | PASS (all identical) |
| sha256/len=120 | all message bytes | 1 | 65 | 65 | 0 | 10784 | 730 | 1892 | 5 | yes | PASS (all identical) |
| sha256/len=256 | all message bytes | 1 | 65 | 65 | 0 | 17057 | 1232 | 2799 | 5 | yes | PASS (all identical) |
| sha256/len=560 | all message bytes | 1 | 65 | 65 | 0 | 29076 | 1994 | 4425 | 4 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 1 | 65 | 65 | 0 | 16248 | 1385 | 3446 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 1 | 65 | 65 | 0 | 22789 | 1861 | 4440 | 22 | yes | PASS (all identical) |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 1 | 65 | 65 | 0 | 19962 | 1742 | 4124 | 22 | yes | PASS (all identical) |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 1 | 65 | 65 | 0 | 16773 | 1492 | 3637 | 23 | yes | PASS (all identical) |
| compress (copy inlined into the wrapper) | state and block | 1 | 65 | 65 | 0 | 3207 | 157 | 500 | 0 | yes | PASS (all identical) |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 3252 | 228 | 581 | 1 | yes | PASS (all identical) |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 3252 | 228 | 581 | 1 | yes | PASS (all identical) |
| thash/len=16 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 4030 | 287 | 896 | 8 | yes | PASS (all identical) |
| thash/len=32 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 3822 | 255 | 832 | 8 | yes | PASS (all identical) |
| thash/len=224 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 13360 | 917 | 2224 | 8 | yes | PASS (all identical) |
| thash/len=560 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 33165 | 2369 | 5251 | 10 | yes | PASS (all identical) |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 4 | 68 | 68 | 0 | 32042 | 1583 | 4873 | 0 | yes | PASS (all identical) |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 14494 | 898 | 2659 | 11 | yes | PASS (all identical) |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 14107 | 836 | 2538 | 12 | yes | PASS (all identical) |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 17235 | 1048 | 2986 | 12 | yes | PASS (all identical) |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 65754 | 4433 | 10213 | 13 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 43776 | 1727 | 6407 | 1 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=3..10 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 20568 | 815 | 3127 | 1 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=5..5 (none) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 140 | 16 | 200 | 1 | yes | PASS (all identical) |
| chain_blocks/n=3,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 131086 | 5159 | 18835 | 1 | yes | PASS (all identical) |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 174741 | 6875 | 25049 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 1527902 | 60043 | 217651 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 904066 | 35532 | 129444 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=d_i..15 (wots_pk_from_sig) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 976470 | 38381 | 139637 | 1 | yes | PASS (all identical) |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 68 | 68 | 0 | 42665 | 1684 | 6821 | 1 | yes | PASS (all identical) |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 388760 | 15259 | 60737 | 1 | yes | PASS (all identical) |
| chain_blocks/n=7,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 144 | 144 | 0 | 111097 | 4383 | 16107 | 1 | yes | PASS (all identical) |
| chain_blocks/n=64,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 665004 | 26198 | 96212 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,random ranges,distinct prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 369193 | 14547 | 53491 | 1 | yes | PASS (all identical) |
| chain_blocks_portable/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 174740 | 6874 | 25049 | 1 | yes | PASS (all identical) |
| chain_blocks_portable/n=35,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 36 | 36 | 0 | 360126 | 14201 | 52090 | 1 | yes | PASS (all identical) |
| wots_pk_gen | SK.seed | 4 | 68 | 68 | 0 | 1666912 | 65859 | 239449 | 2 | yes | PASS (all identical) |
| wots_sign | SK.seed (message m public, fixed) | 8 | 72 | 72 | 0 | 1027524 | 40775 | 149220 | 20 | yes | PASS (all identical) |
| xmss_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 1666938 | 65863 | 239479 | 2 | yes | PASS (all identical) |
| xmss_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 3337117 | 131955 | 479495 | 5 | yes | PASS (all identical) |
| xmss_node/z=2 | SK.seed | 4 | 68 | 68 | 0 | 6677475 | 264139 | 959527 | 11 | yes | PASS (all identical) |
| xmss_node/z=3 | SK.seed | 2 | 34 | 34 | 0 | 13358191 | 528507 | 1919591 | 23 | yes | PASS (all identical) |
| xmss_node/z=4 | SK.seed | 2 | 34 | 34 | 0 | 26719623 | 1057243 | 3839719 | 47 | yes | PASS (all identical) |
| xmss_sign | SK.seed (m, idx public, fixed) | 2 | 18 | 18 | 0 | 854372796 | 33808295 | 122780035 | 1544 | yes | PASS (all identical) |
| fors_sk_gen | SK.seed | 4 | 68 | 68 | 0 | 3270 | 230 | 598 | 1 | yes | PASS (all identical) |
| fors_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 6441 | 262 | 1298 | 2 | yes | PASS (all identical) |
| fors_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 15722 | 632 | 2843 | 2 | yes | PASS (all identical) |
| fors_node/z=3 | SK.seed | 4 | 68 | 68 | 0 | 70987 | 2811 | 11859 | 2 | yes | PASS (all identical) |
| fors_node/z=6 | SK.seed | 4 | 68 | 68 | 0 | 585620 | 23062 | 95131 | 2 | yes | PASS (all identical) |
| fors_node/z=7 | SK.seed | 4 | 68 | 68 | 0 | 1173585 | 46189 | 190163 | 2 | yes | PASS (all identical) |
| fors_node/z=8 | SK.seed | 2 | 18 | 18 | 0 | 2350413 | 92606 | 380864 | 5 | yes | PASS (all identical) |
| fors_node/z=12 | SK.seed | 2 | 18 | 18 | 0 | 37655253 | 1485116 | 6101894 | 95 | yes | PASS (all identical) |
| fors_sign | SK.seed (md public, fixed) | 2 | 18 | 18 | 0 | 526649311 | 20767300 | 85367011 | 1457 | yes | PASS (all identical) |
| fors_pk_gen | SK.seed | 2 | 18 | 18 | 0 | 527187174 | 20792653 | 85428490 | 1344 | yes | PASS (all identical) |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 2 | 26 | 26 | 0 | 855131659 | 33839032 | 122888215 | 1535 | yes | PASS (all identical) |
| slh_keygen_internal/all-inputs | SK.seed, SK.prf and PK.seed | 1 | 13 | 13 | 0 | 855131659 | 33839032 | 122888215 | 1535 | yes | PASS (all identical) |
| api::keygen | SK.seed and SK.prf (PK.seed fixed) | 2 | 18 | 18 | 0 | 855131683 | 33839034 | 122888251 | 1535 | yes | PASS (all identical) |
| wots_pk_from_sig | WOTS+ signature bytes (m public, fixed) | 4 | 36 | 36 | 0 | 822120 | 32870 | 118744 | 10 | yes | PASS (all identical) |
| xmss_pk_from_sig | XMSS signature bytes (m, idx public, fixed) | 4 | 36 | 36 | 0 | 938408 | 38357 | 136133 | 19 | yes | PASS (all identical) |
| fors_pk_from_sig | FORS signature bytes (md public, fixed) | 4 | 36 | 36 | 0 | 579119 | 23529 | 98738 | 19 | yes | PASS (all identical) |
| INFO fors_sign, PUBLIC md varied | public digest md (SK.seed fixed) | 1 | 9 | 9 | 0 | 526649311 | 20767300 | 85367011 | 1457 | yes | info: identical |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 1 | 65 | 35 | 30 | 15 | 2 | 5 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_table (secret-indexed lookup) | secret index (leaky by construction) | 1 | 64 | 0 | 64 | 14 | 1 | 7 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 1 | 65 | 12 | 53 | 11544 | 776 | 2327 | 12 | yes | PASS (control: difference detected) |
| CONTROL wots_sign, PUBLIC m varied | public message m (chain lengths are public) | 2 | 34 | 0 | 34 | 897100 | 35646 | 130827 | 20 | yes | PASS (control: difference detected) |
| CONTROL chain_blocks n=4, PUBLIC end of block 0 varied | public step count of one block (0..255) | 1 | 33 | 0 | 33 | 108018 | 4253 | 15619 | 1 | yes | PASS (control: difference detected) |
| CONTROL sha256, PUBLIC length varied | public message length (0..255) | 1 | 33 | 0 | 33 | 6979 | 471 | 1225 | 4 | yes | PASS (control: difference detected) |
| PREFIX chain_blocks n=8, PUBLIC: whether block 2 shares the others' 16-byte prefix | one public bit: block 2 starts like the other blocks, or not | 1 | 8 | 8 | 0 | 94034 | 3700 | 13817 | 1 | yes | info: identical |

Divergence details (first differing pair of each row):

- `CONTROL leaky_cmp (early-exit compare of secret)`: first divergence at event #5: last common event: read 0x50007ffefb (size/arg 1) in basic block ct_evidence::w_leaky_cmp+0x0; A: exec block ct_evidence::w_leaky_cmp+0x6c (size/arg 16) in basic block ct_evidence::w_leaky_cmp+0x6c | B: exec block ct_evidence::w_leaky_cmp+0x2c (size/arg 36) in basic block ct_evidence::w_leaky_cmp+0x2c
- `CONTROL leaky_table (secret-indexed lookup)`: first divergence at event #6: last common event: read 0x50007ffef8 (size/arg 8) in basic block ct_evidence::w_leaky_table+0x0; A: read 0x10254821c (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0 | B: read 0x102548150 (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0
- `CONTROL leaky_loop (secret-dependent iteration count)`: first divergence at event #12: last common event: write 0x50007ffeb8 (size/arg 8) in basic block ct_evidence::w_leaky_loop+0x0; A: exec block ct_evidence::w_leaky_loop+0x30 (size/arg 28) in basic block ct_evidence::w_leaky_loop+0x30 | B: exec block ct_evidence::w_leaky_loop+0x5c (size/arg 24) in basic block ct_evidence::w_leaky_loop+0x5c
- `CONTROL wots_sign, PUBLIC m varied`: first divergence at event #22197: last common event: write 0x50007ff3ac (size/arg 4) in basic block slhdsa::hash::chain_blocks_portable+0x98; A: exec block slhdsa::hash::chain_blocks_portable+0xb0 (size/arg 464) in basic block slhdsa::hash::chain_blocks_portable+0xb0 | B: exec block slhdsa::hash::chain_blocks_portable+0x7c (size/arg 12) in basic block slhdsa::hash::chain_blocks_portable+0x7c
- `CONTROL chain_blocks n=4, PUBLIC end of block 0 varied`: first divergence at event #213: last common event: write 0x50007ff93c (size/arg 4) in basic block slhdsa::hash::chain_blocks_portable+0x98; A: exec block slhdsa::hash::chain_blocks_portable+0xb0 (size/arg 464) in basic block slhdsa::hash::chain_blocks_portable+0xb0 | B: exec block slhdsa::hash::chain_blocks_portable+0x7c (size/arg 12) in basic block slhdsa::hash::chain_blocks_portable+0x7c
- `CONTROL sha256, PUBLIC length varied`: first divergence at event #33: last common event: write 0x50007ffd40 (size/arg 8) in basic block slhdsa::sha256::sha256_from+0x0; A: exec block slhdsa::sha256::sha256_from+0x58 (size/arg 36) in basic block slhdsa::sha256::sha256_from+0x58 | B: exec block slhdsa::sha256::sha256_from+0x4c (size/arg 12) in basic block slhdsa::sha256::sha256_from+0x4c

overall: ALL ROWS AS EXPECTED

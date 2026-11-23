use super::*;

pub(super) fn recover<const N: usize>(
    seed: &Seed<N>,
    adrs: Adrs,
    sig: &[u8],
    digits: &[u32],
) -> [u8; N] {
    let mut endpoints = [[0u8; 64]; LEN_MAX];
    crate::sha256::x86::recover::<N>(&seed.state, adrs, sig, digits, &mut endpoints);
    thash_values(
        seed,
        &adrs.with_type(WOTS_PK).with_keypair(adrs.keypair),
        &endpoints[..digits.len()],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::{chain_blocks_portable, seed_ctx};

    fn check<const N: usize>() {
        if !crate::sha256::x86::avx512_available() {
            return;
        }
        let seed = seed_ctx(&[0x6a; N]);
        let adrs = Adrs::new()
            .with_tree(0x0102030405060708)
            .with_keypair(0x11224455);
        let signature: [u8; 32 * LEN_MAX] = core::array::from_fn(|i| (i * 13 + i / 11) as u8);
        let len = 2 * N + LEN2;
        for variant in 0..20 {
            let digits: [u32; LEN_MAX] = core::array::from_fn(|i| match variant {
                0 => 0,
                1 => 15,
                2 if i < 16 => 15,
                2 => 0,
                n => ((i * 23 + i / 5 + n * 7) % 16) as u32,
            });
            let mut expected = [[0u8; 64]; LEN_MAX];
            for i in 0..len {
                expected[i] =
                    short_block(&adrs.with_word2(i as u32), &signature[i * N..(i + 1) * N]);
            }
            chain_blocks_portable::<N>(&seed.state, &mut expected[..len], &digits, &[15; LEN_MAX]);
            let mut actual = [[0u8; 64]; LEN_MAX];
            crate::sha256::x86::recover::<N>(
                &seed.state,
                adrs,
                &signature,
                &digits[..len],
                &mut actual[..len],
            );
            for i in 0..len {
                assert_eq!(&actual[i][22..22 + N], &expected[i][22..22 + N]);
            }
        }
    }

    #[test]
    fn refill_matches_every_independent_endpoint() {
        check::<16>();
        check::<24>();
        check::<32>();
    }
}

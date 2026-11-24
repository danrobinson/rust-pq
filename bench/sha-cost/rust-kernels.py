#!/usr/bin/env python3
"""Append an ignored raw SHA benchmark to an isolated copy of the Rust crate."""
import argparse
from pathlib import Path

TEMPLATE = '''
#[cfg(test)]
mod wide_raw {
    extern crate std;
    use super::*;
    use core::hint::black_box;

    #[target_feature(enable="avx512f,avx512bw")]
    fn measure() -> f64 {
        let seeds: [[WORD; LANES]; 8] = core::array::from_fn(|i|
            core::array::from_fn(|l| (l*37+i*11+5) as WORD));
        let words: [[WORD; LANES]; 16] = core::array::from_fn(|i|
            core::array::from_fn(|l| (l*11+i*7+3) as WORD));
        let inputs = words.map(|x| unsafe { _mm512_loadu_si512(x.as_ptr().cast()) });
        let mut state = seeds.map(|x| unsafe { _mm512_loadu_si512(x.as_ptr().cast()) });
        let run = |initial: [__m512i;8]| {
            let words = *black_box(&inputs);
            FULL_COMPRESS
        };
        let first = run(state);
        for lane in 0..LANES {
            let mut bytes = [0u8; BLOCK];
            for i in 0..16 {
                bytes[i*WIDTH..(i+1)*WIDTH].copy_from_slice(&words[i][lane].to_be_bytes());
            }
            let expected = crate::SHA::compress_portable(
                &core::array::from_fn(|i| seeds[i][lane]), &bytes, 0);
            for i in 0..8 {
                let lanes: [WORD; LANES] = unsafe { core::mem::transmute(first[i]) };
                assert_eq!(lanes[lane], expected[i]);
            }
        }
        let count = 1usize << 20;
        let start = std::time::Instant::now();
        for _ in 0..count/LANES {
            state = run(state);
        }
        black_box(state);
        start.elapsed().as_nanos() as f64 / count as f64
    }

    #[test]
    #[ignore]
    fn raw_SHA() {
        assert!(crate::sha256::x86::avx512_available());
        std::println!("WIDE_RAW,NAME,{:.6}", unsafe { measure() });
    }
}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("crate", type=Path, help="temporary copy of rust/")
    root = parser.parse_args().crate.resolve()
    if root == Path(__file__).resolve().parents[2] / "rust":
        parser.error("use a temporary crate copy to keep benchmark instrumentation isolated")
    for bits, filename in [(256, "sha256/x86/avx512.rs"), (512, "sha512/x86.rs")]:
        lanes, width = 4096 // bits, bits // 64
        path = root / "src" / filename
        complete = "compress(initial, words)"
        if bits == 256:
            complete = """let mut prefix = initial;
            for i in 0..4 { prefix = round(prefix, words[i], super::super::super::K[i]); }
            compress(initial, prefix, words)"""
        source = TEMPLATE.replace("FULL_COMPRESS", complete).replace("SHA", f"sha{bits}")
        source = source.replace("LANES", str(lanes)).replace("WIDTH", str(width))
        source = source.replace("WORD", f"u{width*8}").replace("BLOCK", str(bits//4))
        source = source.replace("NAME", f"rust{bits}_{lanes}").replace("let mut run", "let run")
        with path.open("a") as output:
            output.write(source)


if __name__ == "__main__":
    main()

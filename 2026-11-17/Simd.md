Https://matklad.github.io/2023/04/09/can-you-trust-a-compiler-to-optimize-your-code.html

How can rewrite 

// 80 milliseconds
fn common_prefix5(xs: &[u8], ys: &[u8]) -> usize {
  let chunk_size = 16;
  let off =
    zip(xs.chunks_exact(chunk_size), ys.chunks_exact(chunk_size))
      .take_while(|(xs_chunk, ys_chunk)| xs_chunk == ys_chunk)
      .count() * chunk_size;
  off + zip(&xs[off..], &ys[off..])
    .take_while(|(x, y)| x == y)
    .count()
}

Ising Simd datatype and other std::simd funcs?
---
#![feature(portable_simd)]

use std::simd::cmp::SimdPartialEq;
use std::simd::Simd;

pub fn common_prefix_simd(xs: &[u8], ys: &[u8]) -> usize {
    const LANES: usize = 16;
    let min_len = xs.len().min(ys.len());
    let mut off = 0;

    while off + LANES <= min_len {
        let a = Simd::<u8, LANES>::from_slice(&xs[off..off + LANES]);
        let b = Simd::<u8, LANES>::from_slice(&ys[off..off + LANES]);

        // Lane `i` is true where bytes differ; `to_bitmask()` packs lanes into bits `0..LANES`.
        let mismatch_bits = a.simd_ne(b).to_bitmask();
        if mismatch_bits != 0 {
            return off + mismatch_bits.trailing_zeros() as usize;
        }

        off += LANES;
    }

    // Handle remaining bytes shorter than 16 lanes.
    off + xs[off..min_len]
        .iter()
        .zip(&ys[off..min_len])
        .take_while(|(x, y)| x == y)
        .count()
}

---
use wide::u8x16;

pub fn common_prefix_wide(xs: &[u8], ys: &[u8]) -> usize {
    const LANES: usize = 16;
    let min_len = xs.len().min(ys.len());
    let mut off = 0;

    while off + LANES <= min_len {
        // Convert 16-byte slice windows directly into `[u8; 16]` for `u8x16::from`.
        let a = u8x16::from(<&[u8; LANES]>::try_from(&xs[off..off + LANES]).unwrap());
        let b = u8x16::from(<&[u8; LANES]>::try_from(&ys[off..off + LANES]).unwrap());

        // `simd_ne` produces a mask vector; `to_bitmask()` packs lane results into a `u32`.
        let mismatch_bits = a.simd_ne(b).to_bitmask();
        if mismatch_bits != 0 {
            return off + mismatch_bits.trailing_zeros() as usize;
        }

        off += LANES;
    }

    // Scalar tail for remaining bytes (`min_len - off < 16`).
    off + xs[off..min_len]
        .iter()
        .zip(&ys[off..min_len])
        .take_while(|(x, y)| x == y)
        .count()
}

---
use pulp::Arch;

pub fn common_prefix_pulp(xs: &[u8], ys: &[u8]) -> usize {
    let arch = Arch::new();
    arch.dispatch(|| common_prefix_chunked(xs, ys, 16))
}

#[inline(always)]
fn common_prefix_chunked(xs: &[u8], ys: &[u8], chunk_size: usize) -> usize {
    let min_len = xs.len().min(ys.len());
    let mut off = 0;

    while off + chunk_size <= min_len {
        if xs[off..off + chunk_size] != ys[off..off + chunk_size] {
            break;
        }
        off += chunk_size;
    }

    off + xs[off..min_len]
        .iter()
        .zip(&ys[off..min_len])
        .take_while(|(x, y)| x == y)
        .count()
}

---

use macerator::{vload_unaligned, AutoArch, Simd, WithSimd};

struct CommonPrefix<'a> {
    xs: &'a [u8],
    ys: &'a [u8],
}

impl<'a> WithSimd for CommonPrefix<'a> {
    type Output = usize;

    #[inline(always)]
    fn with_simd<S: Simd>(self, simd: S) -> Self::Output {
        let _ = simd;
        let min_len = self.xs.len().min(self.ys.len());
        let step = core::mem::size_of::<S::Vector<u8>>(); // or vector lane count for `u8`
        let mut off = 0;

        while step > 0 && off + step <= min_len {
            // `vload_unaligned` is `unsafe`: `ptr` must be valid for a full vector read.
            let eq = unsafe {
                let a = vload_unaligned::<S, u8>(self.xs[off..].as_ptr());
                let b = vload_unaligned::<S, u8>(self.ys[off..].as_ptr());
                // Compare vectors `a` and `b` using `S` / `Mask` operations
                a == b
            };

            if !eq {
                break;
            }
            off += step;
        }

        off + self.xs[off..min_len]
            .iter()
            .zip(&self.ys[off..min_len])
            .take_while(|(x, y)| x == y)
            .count()
    }
}

pub fn common_prefix_macerator(xs: &[u8], ys: &[u8]) -> usize {
    AutoArch::new().dispatch(CommonPrefix { xs, ys })
}



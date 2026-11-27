//! Exhaustive verification of Erdős #287 up to `B_0 = 10^8` using:
//! 1. Universal rational block coverage (`K = 64` exact rational blocks: `64 * v <= 65 * u`
//!    proves `sum_{y = u+1..=v} 1/y < 1/64` in exact `Q`, zero floating point!),
//! 2. Exact consecutive forbidden pairs `(x, x + 1)` with `x = c1 * p1`, `x + 1 = c2 * p2`,
//!    `p_i > m_i`, `p_i not in P_{m_i}`, covering entire intervals `[x + 1, b_hi]`,
//! 3. Exact `u128` interval + `p`-adic propagation fallback (`test_interval_exact`) on `rayon`
//!    for every `b` not covered by universal consecutive forbidden pairs.

use crate::fixed_u128::{
    is_prime_from_odd_bitset, sieve_primes, test_interval_exact, PmTable, PrefixHarmonicBounds,
    PropagatorBuffers,
};
use rayon::prelude::*;
use serde::Serialize;
use std::time::Instant;

/// Computes the exact largest upper bound `u_64(x)` using `64` rational steps
/// `u_{j+1} = (65 * u_j) / 64`.
/// By Lemma 2.2 (`64 * u_{j+1} <= 65 * u_j`), for EVERY integer `b <= u_64(x)`,
/// `sum_{y = x + 1..=b} 1 / y < 64 * (1 / 64) = 1` in **exact rational arithmetic `Q`**,
/// so every candidate `(a, b, S)` with `b <= u_64(x)` satisfies `a <= x` unconditionally!
#[inline]
pub const fn exact_rational_cover_hi_64(x: u64) -> u64 {
    let mut u = x;
    let mut step = 0;
    while step < 64 {
        u = (65 * u) / 64;
        step += 1;
    }
    u
}

/// Computes the exact `4`-block rational cover bound `u_4(x)` (`u_{j+1} = (5 * u_j) / 4`),
/// matching our ultra-compact Lean 4 certificate lemma (`sum_Ioc_inv_lt_quarter` x 4)!
#[inline]
pub const fn exact_rational_cover_hi_4(x: u64) -> u64 {
    let u1 = (5 * x) / 4;
    let u2 = (5 * u1) / 4;
    let u3 = (5 * u2) / 4;
    (5 * u3) / 4
}

/// Witness representation for a consecutive forbidden pair `(x, x + 1)` where
/// `x = c1 * p1` (`p1 > m1`, `p1 not in P_{m1}`) and `x + 1 = c2 * p2` (`p2 > m2`, `p2 not in P_{m2}`).
#[derive(Debug, Clone, Copy, Serialize)]
pub struct UniversalPairWitness {
    pub x: u32,
    pub c1: u8,
    pub m1: u8,
    pub p1: u32,
    pub c2: u8,
    pub m2: u8,
    pub p2: u32,
    pub b_lo: u32,
    pub b_hi: u32,
}

/// Given an integer `n >= 2`, attempts to represent `n = c * p` with `1 <= c <= max_m`,
/// `p` prime, `p > m`, `p not in P_m`, maximizing the upper bound `(m + 1) * p - 1`.
#[inline]
pub fn best_forbidden_decomp(
    n: u32,
    max_m: usize,
    is_comp_odd: &[u64],
    pm: &PmTable,
) -> Option<(u8, u8, u32, u64)> {
    let mut best: Option<(u8, u8, u32, u64)> = None;
    let lim_c = max_m.min(n as usize);
    for c in 1..=lim_c {
        let cu = c as u32;
        if n % cu != 0 {
            continue;
        }
        let p = n / cu;
        if !is_prime_from_odd_bitset(p, is_comp_odd) {
            continue;
        }
        let m_allow = pm.max_m_not_containing(p).min(max_m);
        if m_allow < c || (p as usize) <= c {
            continue;
        }
        // Largest m <= m_allow with m < p
        let m_use = m_allow.min((p as usize) - 1);
        if m_use < c {
            continue;
        }
        let cap = ((m_use as u64) + 1) * (p as u64) - 1;
        if best.map_or(true, |(_, _, _, prev_cap)| cap > prev_cap) {
            best = Some((c as u8, m_use as u8, p, cap));
        }
    }
    best
}

/// Checks if `(x, x + 1)` forms a valid universal forbidden pair using `max_m`,
/// returning `UniversalPairWitness` with `b_hi` computed via `use_4_block` (for Lean 4)
/// or `64`-block exact rational cover (for `10^8` Rust verification).
#[inline]
pub fn check_universal_pair(
    x: u32,
    max_m: usize,
    is_comp_odd: &[u64],
    pm: &PmTable,
    use_4_block: bool,
    forbid_sophie_germain: bool,
) -> Option<UniversalPairWitness> {
    let (c1, m1, p1, cap1) = best_forbidden_decomp(x, max_m, is_comp_odd, pm)?;
    let (c2, m2, p2, cap2) = best_forbidden_decomp(x + 1, max_m, is_comp_odd, pm)?;

    if forbid_sophie_germain && ((c1 == 1 && c2 == 2) || (c1 == 2 && c2 == 1)) {
        return None;
    }

    let rat_hi = if use_4_block {
        exact_rational_cover_hi_4(x as u64)
    } else {
        exact_rational_cover_hi_64(x as u64)
    };
    let b_hi_u64 = rat_hi.min(cap1).min(cap2);
    let b_lo = x + 1;
    if b_hi_u64 < (b_lo as u64) {
        return None;
    }
    let b_hi = b_hi_u64.min(u32::MAX as u64) as u32;
    Some(UniversalPairWitness {
        x,
        c1,
        m1,
        p1,
        c2,
        m2,
        p2,
        b_lo,
        b_hi,
    })
}

#[derive(Debug, Clone, Serialize)]
pub struct Verify100mSummary {
    pub max_b: u32,
    pub max_m_used: usize,
    pub primes_up_to_max_b: usize,
    pub greedy_cover_witness_count: usize,
    pub universal_covered_b_count: u64,
    pub fallback_b_values: Vec<u32>,
    pub fallback_candidate_intervals_tested: usize,
    pub total_survivors: usize,
    pub elapsed_secs: f64,
    pub first_15_witnesses: Vec<UniversalPairWitness>,
    pub last_5_witnesses: Vec<UniversalPairWitness>,
}

/// Runs a greedy jumping cover + fallback verification for **ALL** `4 <= b <= max_b` (`max_b <= 10^8`)!
/// Notice how fast greedy jumping is: once a witness covers `[x + 1, b_hi]`, we only need
/// to search backwards from `b_hi` (near `x_next ~ b_hi - 1` down to `b_hi / 2.69`) to find the
/// next witness extending `b_hi` by ~`2.69x`! If any `b` is not covered by jumping, we scan
/// locally and fall back to exact `u128` interval propagation (`test_interval_exact`).
pub fn verify_up_to_max_b(max_b: u32, max_m: usize) -> Verify100mSummary {
    let t0 = Instant::now();
    let (is_comp_odd, primes) = sieve_primes(max_b);
    let pm = PmTable::compute(max_m);

    // Step 1: Collect candidate universal witnesses for small x <= 500 first to find where
    // universal contiguous coverage begins, then jump geometrically up to `max_b`!
    let mut fallback_bs: Vec<u32> = Vec::new();
    let mut chosen_witnesses: Vec<UniversalPairWitness> = Vec::new();

    let mut cur_b: u32 = 4;
    while cur_b <= max_b {
        // To cover `cur_b` AND maximize `b_hi`, we want the LARGEST `x <= cur_b - 1`
        // that produces a valid pair covering `cur_b` (`b_lo = x + 1 <= cur_b <= b_hi`)!
        let max_x = cur_b - 1;
        // Minimum x that could possibly have `exact_rational_cover_hi_64(x) >= cur_b`
        // Since u_64(x) <= 2.70 * x, x must be >= cur_b * 10 / 28
        let min_x = ((cur_b as u64) * 10 / 28).max(2) as u32;

        let mut best_w: Option<UniversalPairWitness> = None;
        // Scan downwards from `max_x`! Because `b_hi` grows roughly linearly with `x`,
        // the FIRST few valid pairs near `max_x` already achieve near-maximal `b_hi` (~2.69 * cur_b)!
        // Check up to 4,000 values near `max_x` first; if found, pick the best among the top 64 hits!
        let mut hits = 0usize;
        let mut x = max_x;
        while x >= min_x {
            if let Some(w) = check_universal_pair(x, max_m, &is_comp_odd, &pm, false, false) {
                if w.b_lo <= cur_b && w.b_hi >= cur_b {
                    if best_w.map_or(true, |bw| w.b_hi > bw.b_hi) {
                        best_w = Some(w);
                    }
                    hits += 1;
                    if hits >= 32 {
                        break;
                    }
                }
            }
            if x == min_x {
                break;
            }
            x -= 1;
        }

        if let Some(w) = best_w {
            let new_until = w.b_hi.min(max_b);
            chosen_witnesses.push(w);
            if new_until == max_b {
                break;
            }
            cur_b = new_until + 1;
        } else {
            fallback_bs.push(cur_b);
            if cur_b == max_b {
                break;
            }
            cur_b += 1;
        }
    }

    // Step 2: Independently verify EVERY single chosen witness's coverage conditions in exact integer arithmetic!
    let mut verified_cov = vec![false; 0]; // not needed to allocate 10^8 bools: verify interval chain!
    let _ = &mut verified_cov;
    for w in &chosen_witnesses {
        assert_eq!(w.x, (w.c1 as u32) * w.p1);
        assert_eq!(w.x + 1, (w.c2 as u32) * w.p2);
        assert!(is_prime_from_odd_bitset(w.p1, &is_comp_odd));
        assert!(is_prime_from_odd_bitset(w.p2, &is_comp_odd));
        assert!((w.m1 as u32) < w.p1);
        assert!((w.m2 as u32) < w.p2);
        assert!(!pm.contains(w.m1 as usize, w.p1));
        assert!(!pm.contains(w.m2 as usize, w.p2));
        assert!((w.b_hi as u64) < ((w.m1 as u64) + 1) * (w.p1 as u64));
        assert!((w.b_hi as u64) < ((w.m2 as u64) + 1) * (w.p2 as u64));
        assert!((w.b_hi as u64) <= exact_rational_cover_hi_64(w.x as u64));
        assert!(w.b_lo == w.x + 1 && w.b_lo <= w.b_hi);
    }

    // Verify exact partition of 4..=max_b between `fallback_bs` and `chosen_witnesses`!
    let mut check_b: u64 = 4;
    let mut fb_idx = 0usize;
    let mut w_idx = 0usize;
    while check_b <= (max_b as u64) {
        if fb_idx < fallback_bs.len() && (fallback_bs[fb_idx] as u64) == check_b {
            fb_idx += 1;
            check_b += 1;
        } else if w_idx < chosen_witnesses.len()
            && (chosen_witnesses[w_idx].b_lo as u64) <= check_b
            && check_b <= (chosen_witnesses[w_idx].b_hi as u64)
        {
            check_b = (chosen_witnesses[w_idx].b_hi as u64).min(max_b as u64) + 1;
            w_idx += 1;
        } else {
            panic!("Coverage gap detected at b = {check_b}!");
        }
    }

    // Step 3: Run exact `u128` interval + `p`-adic propagation on ALL `fallback_bs` in parallel via `rayon`!
    let max_fb = fallback_bs.iter().copied().max().unwrap_or(4);
    let pref = PrefixHarmonicBounds::new(max_fb);
    let fb_results: Vec<(usize, usize)> = fallback_bs
        .par_iter()
        .map(|&b| {
            let mut buf = PropagatorBuffers::with_capacity((b + 1) as usize);
            let cands = pref.candidate_a_list(b);
            let mut surv = 0usize;
            for a in &cands {
                let res = test_interval_exact(*a, b, &primes, &mut buf, 12, true);
                if !res.killed {
                    surv += 1;
                }
            }
            (cands.len(), surv)
        })
        .collect();

    let fallback_candidate_intervals_tested: usize = fb_results.iter().map(|r| r.0).sum();
    let total_survivors: usize = fb_results.iter().map(|r| r.1).sum();
    let total_b_count = if max_b >= 4 { (max_b - 3) as u64 } else { 0 };
    let universal_covered_b_count = total_b_count - (fallback_bs.len() as u64);

    let first_15_witnesses = chosen_witnesses.iter().take(15).copied().collect();
    let last_5_witnesses = chosen_witnesses
        .iter()
        .rev()
        .take(5)
        .copied()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect();

    Verify100mSummary {
        max_b,
        max_m_used: max_m,
        primes_up_to_max_b: primes.len(),
        greedy_cover_witness_count: chosen_witnesses.len(),
        universal_covered_b_count,
        fallback_b_values: fallback_bs,
        fallback_candidate_intervals_tested,
        total_survivors,
        elapsed_secs: t0.elapsed().as_secs_f64(),
        first_15_witnesses,
        last_5_witnesses,
    }
}

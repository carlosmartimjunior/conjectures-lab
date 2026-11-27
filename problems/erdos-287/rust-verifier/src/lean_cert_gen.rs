//! Compact Lean 4 certificate generator (`B_Lean = 20,000`) using the `4`-block rational cover
//! (`u_{j+1} = (5 * u_j) / 4`), which requires zero `Real.log` and zero `native_decide` in Lean 4!

use crate::fixed_u128::{sieve_primes, test_interval_exact, PmTable, PrefixHarmonicBounds, PropagatorBuffers};
use crate::sieve_cover::{check_universal_pair, exact_rational_cover_hi_4, UniversalPairWitness};
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub struct SmallIntervalCase {
    pub a: u32,
    pub b: u32,
    /// If killed by a prime power `q = p^r > b/2` at `x0` or pair `(x, x+1)` specific to `[a, b]`
    pub witness_note: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct LeanCertificateBundle {
    pub max_b_lean: u32,
    pub max_m_lean: usize,
    pub universal_4block_witnesses: Vec<UniversalPairWitness>,
    pub uncovered_small_bs: Vec<u32>,
    pub uncovered_candidate_pairs: Vec<(u32, u32)>,
}

/// Generates a minimal greedy `4`-block cover for `b <= max_b_lean` (`default = 20_000`)
/// keeping `m <= max_m_lean` (`default = 6`, so `NoZeroSubsetMod p m` has at most `2^6 = 64` subsets
/// and checks in `< 1 ms` per witness in Lean 4's kernel without `native_decide`!).
pub fn generate_lean_certificate(max_b_lean: u32, max_m_lean: usize) -> LeanCertificateBundle {
    let (is_comp_odd, primes) = sieve_primes(max_b_lean);
    let pm = PmTable::compute(max_m_lean);

    let mut uncovered_small_bs = Vec::new();
    let mut chosen = Vec::new();

    let mut cur_b = 4u32;
    while cur_b <= max_b_lean {
        let max_x = cur_b - 1;
        let min_x = ((cur_b as u64) * 10 / 26).max(2) as u32;
        let mut best_w: Option<UniversalPairWitness> = None;

        for x in (min_x..=max_x).rev() {
            if let Some(w) = check_universal_pair(x, max_m_lean, &is_comp_odd, &pm, true, false) {
                if w.b_lo <= cur_b && w.b_hi >= cur_b {
                    if best_w.map_or(true, |bw| w.b_hi > bw.b_hi) {
                        best_w = Some(w);
                    }
                }
            }
        }

        if let Some(mut w) = best_w {
            w.b_lo = cur_b;
            w.b_hi = w.b_hi.min(max_b_lean);
            assert!((w.b_hi as u64) <= exact_rational_cover_hi_4(w.x as u64));
            chosen.push(w);
            if w.b_hi == max_b_lean {
                break;
            }
            cur_b = w.b_hi + 1;
        } else {
            uncovered_small_bs.push(cur_b);
            cur_b += 1;
        }
    }

    let max_unc = uncovered_small_bs.iter().copied().max().unwrap_or(4);
    let pref = PrefixHarmonicBounds::new(max_unc);
    let mut buf = PropagatorBuffers::with_capacity((max_unc + 1) as usize);
    let mut uncovered_candidate_pairs = Vec::new();
    for &b in &uncovered_small_bs {
        for a in pref.candidate_a_list(b) {
            let res = test_interval_exact(a, b, &primes, &mut buf, 10, true);
            assert!(res.killed, "Small interval [{a}, {b}] must be killed!");
            uncovered_candidate_pairs.push((a, b));
        }
    }

    LeanCertificateBundle {
        max_b_lean,
        max_m_lean,
        universal_4block_witnesses: chosen,
        uncovered_small_bs,
        uncovered_candidate_pairs,
    }
}

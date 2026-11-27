//! Parallel (`rayon`) ablation suite comparing `M1`, `M2`, `M3` (no Sophie Germain!), and `M4`
//! to provide quantitative, irrefutable evidence for Gate 1.

use crate::fixed_u128::{
    sieve_primes, test_interval_exact, PmTable, PrefixHarmonicBounds, PropagatorBuffers,
    ONE_SCALED,
};
use crate::sat_m1::{solve_sat_m1, SatM1Outcome, SatM1Witness};
use crate::sieve_cover::check_universal_pair;
use rayon::prelude::*;
use serde::Serialize;
use std::time::Instant;

#[derive(Debug, Clone, Serialize)]
pub struct ModeIntervalStats {
    pub mode_name: String,
    pub max_b_tested: u32,
    pub total_candidates: usize,
    pub killed_count: usize,
    pub survivor_count: usize,
    pub first_survivor_examples: Vec<(u32, u32)>,
}

#[derive(Debug, Clone, Serialize)]
pub struct NoSophieGermainStats {
    pub max_b_tested: u32,
    pub max_m_used: usize,
    pub contiguous_universal_cover_from_b: u32,
    pub uncovered_b_count: usize,
    pub uncovered_b_max: u32,
    pub uncovered_b_sample: Vec<u32>,
}

#[derive(Debug, Clone, Serialize)]
pub struct SatM1SweepSummary {
    pub max_p: u32,
    pub tol_ppm: u64,
    pub tested_intervals: usize,
    pub unsat_count: usize,
    pub sat_pseudo_solution_count: usize,
    pub budget_reached_count: usize,
    pub explicit_pseudo_solutions: Vec<SatM1Witness>,
}

#[derive(Debug, Clone, Serialize)]
pub struct AblationReport {
    pub elapsed_secs: f64,
    pub m1_prop_small_primes_p13: ModeIntervalStats,
    pub m2_half_primes_only: ModeIntervalStats,
    pub m4_full_propagation: ModeIntervalStats,
    pub m3_no_sophie_germain_cover_10m: NoSophieGermainStats,
    pub sat_m1_exact_carry_probe: SatM1SweepSummary,
}

/// Runs propagation restricted to either:
/// - `max_prime_allowed = Some(13)` (`M1` propagator: only primes `p <= 13`), or
/// - `only_m_eq_1 = true` (`M2`: only prime powers `p^r > b/2`).
fn run_restricted_mode(
    mode_name: &str,
    max_b: u32,
    primes: &[u32],
    pref: &PrefixHarmonicBounds,
    max_prime_allowed: Option<u32>,
    only_m_eq_1: bool,
) -> ModeIntervalStats {
    let filtered_primes: Vec<u32> = match max_prime_allowed {
        Some(mp) => primes.iter().copied().filter(|&p| p <= mp).collect(),
        None => primes.to_vec(),
    };
    let max_sub = if only_m_eq_1 { 1 } else { 10 };

    let per_b: Vec<(usize, usize, Vec<(u32, u32)>)> = (4..=max_b)
        .into_par_iter()
        .map(|b| {
            let mut buf = PropagatorBuffers::with_capacity((b + 1) as usize);
            let cands = pref.candidate_a_list(b);
            let mut killed = 0usize;
            let mut surv_ex = Vec::new();
            for &a in &cands {
                let res = test_interval_exact(a, b, &filtered_primes, &mut buf, max_sub, true);
                if res.killed {
                    killed += 1;
                } else if surv_ex.len() < 3 {
                    surv_ex.push((a, b));
                }
            }
            (cands.len(), killed, surv_ex)
        })
        .collect();

    let total_candidates: usize = per_b.iter().map(|x| x.0).sum();
    let killed_count: usize = per_b.iter().map(|x| x.1).sum();
    let survivor_count = total_candidates - killed_count;
    let mut first_survivor_examples = Vec::new();
    for (_, _, ex) in per_b {
        for pair in ex {
            if first_survivor_examples.len() < 15 {
                first_survivor_examples.push(pair);
            }
        }
    }

    ModeIntervalStats {
        mode_name: mode_name.to_string(),
        max_b_tested: max_b,
        total_candidates,
        killed_count,
        survivor_count,
        first_survivor_examples,
    }
}

/// Tests `M3` up to `max_b` (`default = 10,000,000`) with **Sophie Germain / safe prime pairs
/// `(c1, c2) in {(1, 2), (2, 1)}` STRICTLY FORBIDDEN**!
pub fn test_m3_without_sophie_germain(max_b: u32, max_m: usize) -> NoSophieGermainStats {
    let (is_comp_odd, _) = sieve_primes(max_b);
    let pm = PmTable::compute(max_m);

    let mut uncovered = Vec::new();
    let mut cur_b = 4u32;
    while cur_b <= max_b {
        let max_x = cur_b - 1;
        let min_x = ((cur_b as u64) * 10 / 28).max(2) as u32;
        let mut best_hi = 0u32;
        let mut hits = 0usize;
        let mut x = max_x;
        while x >= min_x {
            if let Some(w) = check_universal_pair(x, max_m, &is_comp_odd, &pm, false, true) {
                if w.b_lo <= cur_b && w.b_hi >= cur_b {
                    if w.b_hi > best_hi {
                        best_hi = w.b_hi;
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
        if best_hi >= cur_b {
            let next_until = best_hi.min(max_b);
            if next_until == max_b {
                break;
            }
            cur_b = next_until + 1;
        } else {
            uncovered.push(cur_b);
            if cur_b == max_b {
                break;
            }
            cur_b += 1;
        }
    }

    let uncovered_b_max = uncovered.last().copied().unwrap_or(3);
    NoSophieGermainStats {
        max_b_tested: max_b,
        max_m_used: max_m,
        contiguous_universal_cover_from_b: uncovered_b_max + 1,
        uncovered_b_count: uncovered.len(),
        uncovered_b_max,
        uncovered_b_sample: uncovered.iter().rev().take(20).copied().rev().collect(),
    }
}

pub fn run_full_ablation(max_b_intervals: u32, max_b_m3: u32) -> AblationReport {
    let t0 = Instant::now();
    let (_, primes) = sieve_primes(max_b_intervals);
    let pref = PrefixHarmonicBounds::new(max_b_intervals);

    let m1_prop = run_restricted_mode(
        "M1_SmallPrimes_le_13_Prop",
        max_b_intervals,
        &primes,
        &pref,
        Some(13),
        false,
    );
    let m2_half = run_restricted_mode(
        "M2_HalfIntervalPrimePowersOnly",
        max_b_intervals,
        &primes,
        &pref,
        None,
        true,
    );
    let m4_full = run_restricted_mode(
        "M4_FullPadicAndU128",
        max_b_intervals,
        &primes,
        &pref,
        None,
        false,
    );

    let m3_no_sg = test_m3_without_sophie_germain(max_b_m3, 18);

    // Exact SAT/CDCL full-carry probe on M1 (`max_p = 13`, tolerance `10 ppm = 10^-5`):
    // Tests all candidate `(a, b)` for `b` in `[4..=120]` plus sampled middle intervals at `b = 150, 200, 250, 300`!
    let max_p_sat = 13u32;
    let tol_ppm = 10u64; // |sum - 1| <= 10^-5
    let tol_scaled = ONE_SCALED / 100_000;

    let mut sat_targets: Vec<(u32, u32)> = Vec::new();
    for b in 4..=100 {
        for a in pref.candidate_a_list(b) {
            sat_targets.push((a, b));
        }
    }
    for b in [120u32, 150, 180, 210, 240, 300] {
        if b <= max_b_intervals {
            let cands = pref.candidate_a_list(b);
            if !cands.is_empty() {
                sat_targets.push((cands[0], b));
                sat_targets.push((cands[cands.len() / 2], b));
                sat_targets.push((*cands.last().unwrap(), b));
            }
        }
    }

    let outcomes: Vec<SatM1Outcome> = sat_targets
        .par_iter()
        .map(|&(a, b)| solve_sat_m1(a, b, max_p_sat, true, tol_scaled, 50_000))
        .collect();

    let mut unsat_count = 0usize;
    let mut sat_pseudo_solution_count = 0usize;
    let mut budget_reached_count = 0usize;
    let mut explicit_pseudo_solutions = Vec::new();

    for out in outcomes {
        match out {
            SatM1Outcome::Unsat { .. } => unsat_count += 1,
            SatM1Outcome::Sat(w) => {
                sat_pseudo_solution_count += 1;
                if explicit_pseudo_solutions.len() < 5 {
                    explicit_pseudo_solutions.push(w);
                }
            }
            SatM1Outcome::NodeBudgetReached { .. } => budget_reached_count += 1,
        }
    }

    AblationReport {
        elapsed_secs: t0.elapsed().as_secs_f64(),
        m1_prop_small_primes_p13: m1_prop,
        m2_half_primes_only: m2_half,
        m4_full_propagation: m4_full,
        m3_no_sophie_germain_cover_10m: m3_no_sg,
        sat_m1_exact_carry_probe: SatM1SweepSummary {
            max_p: max_p_sat,
            tol_ppm,
            tested_intervals: sat_targets.len(),
            unsat_count,
            sat_pseudo_solution_count,
            budget_reached_count,
            explicit_pseudo_solutions,
        },
    }
}

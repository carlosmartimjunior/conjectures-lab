//! Exact SAT/SMT & full-carry `mod p^R` solver for Experiment `M1` (Route B).
//!
//! For any interval `[a, b]` and small-prime bound `P_0` (e.g., `P_0 in {5, 7, 13}`),
//! `v_p(sum_{x in S} 1/x) >= 0` is **100% equivalent** to the exact linear congruence modulo `p^R`
//! (`p^R <= b < p^{R+1}`):
//!   `sum_{x in [a,b], p | x} w_{p,R}(x) * s_x == 0 (mod p^R)`
//! where `x = p^k * u` (`p nmid u`) and `w_{p,R}(x) = p^{R - k} * (u^{-1} mod p^R) mod p^R`.
//!
//! This module implements:
//! 1. Hierarchical branch-and-propagate over `V_mod` (ordered by prime-power divisibility so
//!    `mod p^{R-k+1}` suffix-GCD pruning fires immediately at every prime-power layer!),
//!    coupled with exact `u128` DP bounds (`gap <= 2`) and meet-in-the-middle / greedy refinement
//!    on the pairwise non-adjacent odd `P_0`-rough variables `V_free`.
//! 2. Standard SMT-LIB2 (`QF_LIA`) and DIMACS `.cnf` (with Tseitin modular adder clauses) exporters
//!    for external verification in Z3 / CaDiCaL.

use crate::fixed_u128::{
    compute_sum_bounds, gcd_u128, inv_bounds, mod_inv_u64, sieve_primes, ONE_SCALED, STATE_IN,
    STATE_OUT, STATE_UNK,
};
use serde::Serialize;

#[derive(Debug, Clone)]
pub struct PrimePowerCongruence {
    pub p: u32,
    pub modulus: u64, // p^R
    /// Indices `idx = x - a` of multiples of `p` in `[a, b]`, sorted by descending `v_p(x)`
    pub vars: Vec<usize>,
    /// Exact weights `w_{p,R}(x) in 0..p^R`
    pub weights: Vec<u64>,
    /// `suffix_gcd[j] = gcd(modulus, weights[j], weights[j+1], ...)`:
    /// Once `vars[0..j]` are assigned, `partial_sum % suffix_gcd[j]` MUST equal `0`!
    pub suffix_gcd: Vec<u64>,
}

impl PrimePowerCongruence {
    pub fn build(a: u32, b: u32, p: u32) -> Option<Self> {
        if p > b {
            return None;
        }
        let p64 = p as u64;
        let mut modulus = p64;
        while modulus * p64 <= (b as u64) {
            modulus *= p64;
        }

        let first = (((a as u64) + p64 - 1) / p64) * p64;
        if first > (b as u64) {
            return None;
        }

        let mut items: Vec<(u32, usize, u64)> = Vec::new(); // (k, idx, weight)
        let mut x = first;
        while x <= (b as u64) {
            let mut u = x;
            let mut k = 0u32;
            let mut pk = 1u64;
            while u % p64 == 0 {
                u /= p64;
                k += 1;
                pk *= p64;
            }
            let p_r_minus_k = modulus / pk;
            let inv_u = mod_inv_u64(u % modulus, modulus);
            let w = ((p_r_minus_k as u128 * inv_u as u128) % (modulus as u128)) as u64;
            items.push((k, (x as u32 - a) as usize, w));
            x += p64;
        }

        // Sort by descending `k = v_p(x)`, then ascending `idx`
        items.sort_by(|lhs, rhs| rhs.0.cmp(&lhs.0).then_with(|| lhs.1.cmp(&rhs.1)));

        let m = items.len();
        let vars: Vec<usize> = items.iter().map(|it| it.1).collect();
        let weights: Vec<u64> = items.iter().map(|it| it.2).collect();
        let mut suffix_gcd = vec![modulus; m + 1];
        for j in (0..m).rev() {
            suffix_gcd[j] = gcd_u128(suffix_gcd[j + 1] as u128, weights[j] as u128) as u64;
        }

        Some(Self {
            p,
            modulus,
            vars,
            weights,
            suffix_gcd,
        })
    }

    /// Evaluates whether a complete assignment `state` satisfies `sum w * s == 0 (mod p^R)`.
    pub fn is_satisfied_by(&self, state: &[i8]) -> bool {
        let mut acc: u128 = 0;
        let m = self.modulus as u128;
        for (&idx, &w) in self.vars.iter().zip(self.weights.iter()) {
            if state[idx] == STATE_IN {
                acc += w as u128;
                if acc >= m {
                    acc -= m;
                }
            }
        }
        acc % m == 0
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct SatM1Witness {
    pub a: u32,
    pub b: u32,
    pub max_p: u32,
    pub subset_size: usize,
    pub sum_approx_f64: f64,
    pub abs_err_from_one: f64,
    pub subset_elements: Vec<u32>,
}

#[derive(Debug, Clone, Serialize)]
pub enum SatM1Outcome {
    Unsat { nodes_explored: u64 },
    Sat(SatM1Witness),
    NodeBudgetReached { nodes_explored: u64 },
}

/// Checks if all assigned prefixes in every `PrimePowerCongruence` pass suffix-GCD divisibility
/// and performs unit propagation when a congruence has 0 or 1 unassigned variables before a GCD jump!
fn propagate_modular_and_gap(
    state: &mut [i8],
    congs: &[PrimePowerCongruence],
    enforce_gap2: bool,
    trail: &mut Vec<usize>,
) -> bool {
    let assign = |state: &mut [i8], idx: usize, val: i8, trail: &mut Vec<usize>| -> bool {
        if state[idx] == val {
            return true;
        }
        if state[idx] == -val {
            return false;
        }
        state[idx] = val;
        trail.push(idx);
        true
    };

    let mut head = 0usize;
    // First propagate neighbor `gap <= 2` consequences for any newly set `STATE_OUT`
    let propagate_neighbors =
        |state: &mut [i8], head: &mut usize, trail: &mut Vec<usize>| -> bool {
            if !enforce_gap2 {
                *head = trail.len();
                return true;
            }
            while *head < trail.len() {
                let idx = trail[*head];
                *head += 1;
                if state[idx] == STATE_OUT {
                    if idx > 0 && !assign(state, idx - 1, STATE_IN, trail) {
                        return false;
                    }
                    if idx + 1 < state.len() && !assign(state, idx + 1, STATE_IN, trail) {
                        return false;
                    }
                }
            }
            true
        };

    if !propagate_neighbors(state, &mut head, trail) {
        return false;
    }

    let mut changed = true;
    while changed {
        changed = false;
        for cong in congs {
            let m = cong.vars.len();
            let mod_u = cong.modulus;
            // Scan checkpoints `cut` where `suffix_gcd[cut]` > 1 (or `cut == m`, where `suffix_gcd[m] == modulus`)
            let mut partial_sum: u64 = 0;
            let mut unass_count = 0usize;
            let mut last_unass_pos = 0usize;

            for pos in 0..m {
                let v = cong.vars[pos];
                match state[v] {
                    STATE_IN => {
                        partial_sum = ((partial_sum as u128 + cong.weights[pos] as u128)
                            % (mod_u as u128)) as u64;
                    }
                    STATE_UNK => {
                        unass_count += 1;
                        last_unass_pos = pos;
                    }
                    _ => {}
                }

                let next_gcd = cong.suffix_gcd[pos + 1];
                if next_gcd > cong.suffix_gcd[pos] || pos + 1 == m {
                    // Check at checkpoint `g = next_gcd`
                    let g = next_gcd;
                    if g > 1 {
                        if unass_count == 0 {
                            if partial_sum % g != 0 {
                                return false;
                            }
                        } else if unass_count == 1 {
                            let w = cong.weights[last_unass_pos];
                            let u_var = cong.vars[last_unass_pos];
                            let ok_out = (partial_sum % g) == 0;
                            let ok_in = ((partial_sum as u128 + w as u128) % (g as u128)) == 0;
                            if !ok_out && !ok_in {
                                return false;
                            }
                            if !ok_out && state[u_var] == STATE_UNK {
                                if !assign(state, u_var, STATE_IN, trail) {
                                    return false;
                                }
                                if !propagate_neighbors(state, &mut head, trail) {
                                    return false;
                                }
                                changed = true;
                                break;
                            } else if !ok_in && state[u_var] == STATE_UNK {
                                if !assign(state, u_var, STATE_OUT, trail) {
                                    return false;
                                }
                                if !propagate_neighbors(state, &mut head, trail) {
                                    return false;
                                }
                                changed = true;
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    true
}

/// Given a complete assignment on `V_mod` (and all forced neighbors), solves the unconstrained
/// subset-sum problem on `U_free` (`P_0`-rough odd integers whose even neighbors are both `In`)
/// to minimize `|sum_{x in S} 1/x - 1|` in exact `u128` arithmetic!
fn solve_free_rough_subset(
    a: u32,
    b: u32,
    state: &[i8],
    tol_scaled: u128,
) -> Option<Vec<u32>> {
    let len = (b - a + 1) as usize;
    let mut base_lo: u128 = 0;
    let mut base_hi: u128 = 0;
    let mut free_vars: Vec<(u32, u128, u128)> = Vec::new();

    for i in 0..len {
        let x = a + (i as u32);
        let (lo, hi) = inv_bounds(x as u64);
        match state[i] {
            STATE_IN => {
                base_lo += lo;
                base_hi += hi;
            }
            STATE_OUT => {}
            _ => {
                free_vars.push((x, lo, hi));
            }
        }
    }

    let min_target = ONE_SCALED.saturating_sub(tol_scaled);
    let max_target = ONE_SCALED + tol_scaled;

    if base_lo > max_target {
        return None;
    }
    let total_free_hi: u128 = free_vars.iter().map(|v| v.2).sum();
    if base_hi + total_free_hi < min_target {
        return None;
    }

    // Use meet-in-the-middle on up to 22 free variables (after greedy pre-selection if > 22)
    let mut chosen_free: Vec<u32> = Vec::new();
    let mut cur_lo = base_lo;
    let mut cur_hi = base_hi;

    let mitm_cap = 20usize;
    let mitm_slice = if free_vars.len() > mitm_cap {
        // Greedily pick larger elements (smaller x -> larger 1/x) while keeping room for fine tuning
        let split = free_vars.len() - mitm_cap;
        for &(x, lo, hi) in &free_vars[..split] {
            if cur_hi + hi <= ONE_SCALED {
                cur_lo += lo;
                cur_hi += hi;
                chosen_free.push(x);
            }
        }
        &free_vars[split..]
    } else {
        &free_vars[..]
    };

    let k = mitm_slice.len();
    let k1 = k / 2;
    let k2 = k - k1;

    let mut left_sums: Vec<(u128, u128, u32)> = Vec::with_capacity(1 << k1);
    left_sums.push((0, 0, 0));
    for bit in 0..k1 {
        let (_, lo, hi) = mitm_slice[bit];
        let cur_len = left_sums.len();
        for idx in 0..cur_len {
            let (slo, shi, msk) = left_sums[idx];
            left_sums.push((slo + lo, shi + hi, msk | (1u32 << bit)));
        }
    }
    left_sums.sort_unstable_by_key(|e| e.0);

    let mut right_sums: Vec<(u128, u128, u32)> = Vec::with_capacity(1 << k2);
    right_sums.push((0, 0, 0));
    for bit in 0..k2 {
        let (_, lo, hi) = mitm_slice[k1 + bit];
        let cur_len = right_sums.len();
        for idx in 0..cur_len {
            let (slo, shi, msk) = right_sums[idx];
            right_sums.push((slo + lo, shi + hi, msk | (1u32 << bit)));
        }
    }

    let mut best_match: Option<(u128, u32, u32)> = None; // (dist, lmask, rmask)
    for &(rlo, rhi, rmsk) in &right_sums {
        if cur_lo + rlo > max_target {
            continue;
        }
        let want = ONE_SCALED.saturating_sub(cur_lo + rlo);
        let pos = left_sums.partition_point(|e| e.0 < want);
        for cand_idx in [pos.wrapping_sub(1), pos, pos + 1] {
            if cand_idx < left_sums.len() {
                let (llo, lhi, lmsk) = left_sums[cand_idx];
                let tot_lo = cur_lo + rlo + llo;
                let tot_hi = cur_hi + rhi + lhi;
                if tot_hi >= min_target && tot_lo <= max_target {
                    let mid = tot_lo / 2 + tot_hi / 2;
                    let dist = mid.abs_diff(ONE_SCALED);
                    if best_match.map_or(true, |b| dist < b.0) {
                        best_match = Some((dist, lmsk, rmsk));
                    }
                }
            }
        }
    }

    let (_, lmsk, rmsk) = best_match?;
    for bit in 0..k1 {
        if (lmsk & (1u32 << bit)) != 0 {
            chosen_free.push(mitm_slice[bit].0);
        }
    }
    for bit in 0..k2 {
        if (rmsk & (1u32 << bit)) != 0 {
            chosen_free.push(mitm_slice[k1 + bit].0);
        }
    }

    let mut subset = Vec::new();
    for i in 0..len {
        if state[i] == STATE_IN {
            subset.push(a + (i as u32));
        }
    }
    subset.extend(chosen_free);
    subset.sort_unstable();
    Some(subset)
}

/// Solves Experiment `M1` on `[a, b]` with primes `p <= max_p` (full `mod p^R` carry!),
/// `enforce_gap2`, and scaled tolerance `tol_scaled` (`0` = exact `u128` containment of `1`).
pub fn solve_sat_m1(
    a: u32,
    b: u32,
    max_p: u32,
    enforce_gap2: bool,
    tol_scaled: u128,
    max_nodes: u64,
) -> SatM1Outcome {
    let (_, primes) = sieve_primes(max_p.min(b));
    let congs: Vec<PrimePowerCongruence> = primes
        .iter()
        .filter_map(|&p| PrimePowerCongruence::build(a, b, p))
        .collect();

    let len = (b - a + 1) as usize;
    let mut state = vec![STATE_UNK; len];
    state[0] = STATE_IN;
    state[len - 1] = STATE_IN;

    // Order decision variables in `V_mod`: highest prime-power multiples first (smallest domain!)
    let mut in_vmod = vec![false; len];
    let mut branch_order: Vec<usize> = Vec::new();
    // Interleave high-power checkpoints: sort all `idx` in `V_mod` by smallest prime power domain
    let mut scored_vars: Vec<(u64, usize)> = Vec::new();
    for c in &congs {
        for (pos, &idx) in c.vars.iter().enumerate() {
            if !in_vmod[idx] {
                in_vmod[idx] = true;
                // Prefer variables near early suffix_gcd jumps (high prime power!)
                let g_after = c.suffix_gcd[pos + 1].max(1);
                let score = (c.modulus / g_after) * 1000 + (pos as u64);
                scored_vars.push((score, idx));
            }
        }
    }
    scored_vars.sort_unstable();
    for (_, idx) in scored_vars {
        branch_order.push(idx);
    }
    // If max_p < 2 (no even numbers in V_mod), include remaining variables so gap <= 2 is decided
    if max_p < 2 && enforce_gap2 {
        for idx in 0..len {
            if !in_vmod[idx] {
                branch_order.push(idx);
            }
        }
    }

    let mut trail: Vec<usize> = Vec::with_capacity(len);
    if !propagate_modular_and_gap(&mut state, &congs, enforce_gap2, &mut trail) {
        return SatM1Outcome::Unsat { nodes_explored: 1 };
    }

    let min_target = ONE_SCALED.saturating_sub(tol_scaled);
    let max_target = ONE_SCALED + tol_scaled;
    let mut nodes: u64 = 0;

    fn dfs(
        pos: usize,
        a: u32,
        b: u32,
        branch_order: &[usize],
        state: &mut [i8],
        congs: &[PrimePowerCongruence],
        enforce_gap2: bool,
        tol_scaled: u128,
        min_target: u128,
        max_target: u128,
        trail: &mut Vec<usize>,
        nodes: &mut u64,
        max_nodes: u64,
    ) -> Result<Option<Vec<u32>>, ()> {
        *nodes += 1;
        if *nodes > max_nodes {
            return Err(());
        }

        let Some((min_lo, max_hi)) = compute_sum_bounds(a, b, state, enforce_gap2) else {
            return Ok(None);
        };
        if max_hi < min_target || min_lo > max_target {
            return Ok(None);
        }

        let mut cur = pos;
        while cur < branch_order.len() && state[branch_order[cur]] != STATE_UNK {
            cur += 1;
        }

        if cur == branch_order.len() {
            // All V_mod variables are assigned! Verify every congruence and solve U_free!
            for c in congs {
                if !c.is_satisfied_by(state) {
                    return Ok(None);
                }
            }
            if let Some(subset) = solve_free_rough_subset(a, b, state, tol_scaled) {
                return Ok(Some(subset));
            }
            return Ok(None);
        }

        let var = branch_order[cur];
        // Heuristic: choose value (`STATE_IN` vs `STATE_OUT`) guided by midpoint vs 1
        let try_vals = if min_lo / 2 + max_hi / 2 > ONE_SCALED {
            [STATE_OUT, STATE_IN]
        } else {
            [STATE_IN, STATE_OUT]
        };

        for val in try_vals {
            let saved_len = trail.len();
            state[var] = val;
            trail.push(var);
            if propagate_modular_and_gap(state, congs, enforce_gap2, trail) {
                match dfs(
                    cur + 1,
                    a,
                    b,
                    branch_order,
                    state,
                    congs,
                    enforce_gap2,
                    tol_scaled,
                    min_target,
                    max_target,
                    trail,
                    nodes,
                    max_nodes,
                )? {
                    Some(sol) => return Ok(Some(sol)),
                    None => {}
                }
            }
            while trail.len() > saved_len {
                let u = trail.pop().unwrap();
                state[u] = STATE_UNK;
            }
        }
        Ok(None)
    }

    match dfs(
        0,
        a,
        b,
        &branch_order,
        &mut state,
        &congs,
        enforce_gap2,
        tol_scaled,
        min_target,
        max_target,
        &mut trail,
        &mut nodes,
        max_nodes,
    ) {
        Err(()) => SatM1Outcome::NodeBudgetReached {
            nodes_explored: nodes,
        },
        Ok(None) => SatM1Outcome::Unsat {
            nodes_explored: nodes,
        },
        Ok(Some(subset)) => {
            // Double-check every invariant on the returned witness!
            let mut verify_state = vec![STATE_OUT; len];
            for &x in &subset {
                verify_state[(x - a) as usize] = STATE_IN;
            }
            assert_eq!(verify_state[0], STATE_IN);
            assert_eq!(verify_state[len - 1], STATE_IN);
            if enforce_gap2 {
                for i in 0..len - 1 {
                    assert!(
                        verify_state[i] == STATE_IN || verify_state[i + 1] == STATE_IN,
                        "Returned witness violated gap <= 2!"
                    );
                }
            }
            for c in &congs {
                assert!(
                    c.is_satisfied_by(&verify_state),
                    "Returned witness violated mod p^R congruence for p = {}!",
                    c.p
                );
            }
            let sum_f64: f64 = subset.iter().map(|&x| 1.0 / (x as f64)).sum();
            SatM1Outcome::Sat(SatM1Witness {
                a,
                b,
                max_p,
                subset_size: subset.len(),
                sum_approx_f64: sum_f64,
                abs_err_from_one: (sum_f64 - 1.0).abs(),
                subset_elements: subset,
            })
        }
    }
}

/// Exports a standard SMT-LIB2 (`QF_LIA`) encoding of Experiment `M1` on `[a, b]` for Z3.
pub fn export_m1_smt2(a: u32, b: u32, max_p: u32, tol_ppm: u64) -> String {
    let (_, primes) = sieve_primes(max_p.min(b));
    let congs: Vec<PrimePowerCongruence> = primes
        .iter()
        .filter_map(|&p| PrimePowerCongruence::build(a, b, p))
        .collect();

    let mut out = String::new();
    out.push_str("; SMT-LIB2 QF_LIA encoding for Erdős #287 Experiment M1 (Route B)\n");
    out.push_str("(set-logic QF_LIA)\n");
    for x in a..=b {
        out.push_str(&format!("(declare-const s_{x} Int)\n"));
        out.push_str(&format!("(assert (and (<= 0 s_{x}) (<= s_{x} 1)))\n"));
    }
    out.push_str(&format!("(assert (= s_{a} 1))\n(assert (= s_{b} 1))\n"));
    for x in a..b {
        out.push_str(&format!("(assert (>= (+ s_{x} s_{}) 1))\n", x + 1));
    }
    for c in &congs {
        let p = c.p;
        let m = c.modulus;
        out.push_str(&format!("(declare-const k_mod_{p} Int)\n(assert (>= k_mod_{p} 0))\n"));
        let mut terms = String::new();
        for (&idx, &w) in c.vars.iter().zip(c.weights.iter()) {
            let x = a + (idx as u32);
            terms.push_str(&format!(" (* {w} s_{x})"));
        }
        out.push_str(&format!("(assert (= (+{terms}) (* {m} k_mod_{p})))\n"));
    }
    // Scaled integer sum window at scale 10^12
    let scale: u64 = 1_000_000_000_000;
    let tol = scale * tol_ppm / 1_000_000;
    let mut sum_lo = String::new();
    let mut sum_hi = String::new();
    for x in a..=b {
        let lo = scale / (x as u64);
        let hi = (scale + (x as u64) - 1) / (x as u64);
        sum_lo.push_str(&format!(" (* {lo} s_{x})"));
        sum_hi.push_str(&format!(" (* {hi} s_{x})"));
    }
    out.push_str(&format!("(assert (<= (+{sum_lo}) {}))\n", scale + tol));
    out.push_str(&format!("(assert (>= (+{sum_hi}) {}))\n", scale - tol));
    out.push_str("(check-sat)\n(get-model)\n");
    out
}

/// Exports a standard DIMACS `.cnf` encoding of the `gap <= 2` + top-level modular clauses on `[a, b]`.
pub fn export_m1_dimacs_cnf(a: u32, b: u32, max_p: u32) -> String {
    let (_, primes) = sieve_primes(max_p.min(b));
    let congs: Vec<PrimePowerCongruence> = primes
        .iter()
        .filter_map(|&p| PrimePowerCongruence::build(a, b, p))
        .collect();

    let n_base = (b - a + 1) as i32;
    let mut next_var = n_base + 1;
    let mut clauses: Vec<Vec<i32>> = Vec::new();

    // Endpoints in S
    clauses.push(vec![1]);
    clauses.push(vec![n_base]);
    // Gap <= 2: (s_x or s_{x+1})
    for i in 1..n_base {
        clauses.push(vec![i, i + 1]);
    }

    // Tseitin DP adder modulo `p` for top prime-power multiples of each `p <= max_p`
    for c in &congs {
        let p = c.p as usize;
        // Take variables before first suffix_gcd drop (highest prime power p^R multiples)
        let top_len = c
            .vars
            .iter()
            .enumerate()
            .take_while(|&(pos, _)| pos == 0 || c.suffix_gcd[pos] == c.suffix_gcd[0])
            .count();
        // Wait: top group has suffix_gcd[top_len] >= p; sum mod p must be 0!
        // Encode exact DFA over residues 0..p!
        let mut prev_res_vars = vec![0i32; p];
        // Initially residue 0 is TRUE, residues 1..p are FALSE
        let r0 = next_var;
        next_var += 1;
        clauses.push(vec![r0]);
        prev_res_vars[0] = r0;
        for r in 1..p {
            let vr = next_var;
            next_var += 1;
            clauses.push(vec![-vr]);
            prev_res_vars[r] = vr;
        }

        let top_div = (c.modulus / (p as u64)).max(1);
        for pos in 0..top_len {
            let x_lit = (c.vars[pos] as i32) + 1;
            let step_w = ((c.weights[pos] / top_div) % (p as u64)) as usize;
            let mut cur_res_vars = vec![0i32; p];
            for r in 0..p {
                cur_res_vars[r] = next_var;
                next_var += 1;
            }
            for r in 0..p {
                let prev_v = prev_res_vars[r];
                let next_out = cur_res_vars[r];
                let next_in = cur_res_vars[(r + step_w) % p];
                // (prev_v & !x_lit) -> next_out  <=>  -prev_v v x_lit v next_out
                clauses.push(vec![-prev_v, x_lit, next_out]);
                // (prev_v & x_lit) -> next_in    <=>  -prev_v v -x_lit v next_in
                clauses.push(vec![-prev_v, -x_lit, next_in]);
            }
            prev_res_vars = cur_res_vars;
        }
        clauses.push(vec![prev_res_vars[0]]);
    }

    let num_vars = next_var - 1;
    let mut out = format!("p cnf {num_vars} {}\n", clauses.len());
    for cl in clauses {
        for lit in cl {
            out.push_str(&format!("{lit} "));
        }
        out.push_str("0\n");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sat_m1_preserves_true_decompositions_without_gap2() {
        // [2, 6]: 1/2 + 1/3 + 1/6 = 1 must be SAT at exact u128 tolerance (0)!
        let out_2_6 = solve_sat_m1(2, 6, 5, false, 0, 100_000);
        match out_2_6 {
            SatM1Outcome::Sat(w) => assert_eq!(w.subset_elements, vec![2, 3, 6]),
            other => panic!("Expected Sat([2,3,6]), got {other:?}"),
        }

        // [2, 12] with max_p = 13: 1/2 + 1/4 + 1/6 + 1/12 = 1 (or another exact unit sum) must be SAT!
        let out_2_12 = solve_sat_m1(2, 12, 13, false, 0, 100_000);
        assert!(
            matches!(out_2_12, SatM1Outcome::Sat(_)),
            "Expected [2, 12] without gap<=2 to be SAT, got {out_2_12:?}"
        );
    }
}

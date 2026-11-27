//! Exact fixed-point interval arithmetic in `u128` (scale `2^96`),
//! exact dynamic programming for `gap <= 2` harmonic sum bounds,
//! exact computation of `D_m = lcm(1..=m)` and prime divisor sets `P_m` (`1 <= m <= 18`),
//! and exact full `p`-adic + `u128` interval constraint propagation.

use serde::Serialize;

pub const SCALE_SHIFT: u32 = 96;
pub const ONE_SCALED: u128 = 1u128 << SCALE_SHIFT;
pub const INF_SCALED: u128 = u128::MAX / 4;

/// State of an integer `x` in `[a, b]` during constraint propagation:
/// `1` = forced In (`x in S`), `-1` = forced Out (`x not in S`), `0` = Unknown.
pub const STATE_IN: i8 = 1;
pub const STATE_OUT: i8 = -1;
pub const STATE_UNK: i8 = 0;

/// Exact lower and upper scaled bounds for `1 / x` at scale `2^96`:
/// `lo = floor(2^96 / x)`, `hi = ceil(2^96 / x) = (2^96 + x - 1) / x`.
/// Zero floating point is used anywhere.
#[inline]
pub const fn inv_bounds(x: u64) -> (u128, u128) {
    let d = x as u128;
    let lo = ONE_SCALED / d;
    let hi = (ONE_SCALED + d - 1) / d;
    (lo, hi)
}

/// Exact DP in `u128` computing `(min_sum_lo, max_sum_hi)` for `state` on `[a, b]`.
/// Returns `None` if `state` already violates `enforce_gap2` (e.g., two consecutive `Out`).
/// An interval `[a, b]` is eliminated by sum iff `max_sum_hi < ONE_SCALED || min_sum_lo > ONE_SCALED`.
pub fn compute_sum_bounds(
    a: u32,
    b: u32,
    state: &[i8],
    enforce_gap2: bool,
) -> Option<(u128, u128)> {
    let len = (b - a + 1) as usize;
    debug_assert_eq!(state.len(), len);
    if len == 0 {
        return Some((0, 0));
    }

    let mut max_sum_hi: u128 = 0;
    for i in 0..len {
        if state[i] != STATE_OUT {
            let (_, hi) = inv_bounds((a as u64) + (i as u64));
            max_sum_hi += hi;
        } else if enforce_gap2 && i > 0 && state[i - 1] == STATE_OUT {
            return None;
        }
    }

    if !enforce_gap2 {
        let mut min_sum_lo: u128 = 0;
        for i in 0..len {
            if state[i] == STATE_IN {
                let (lo, _) = inv_bounds((a as u64) + (i as u64));
                min_sum_lo += lo;
            }
        }
        return Some((min_sum_lo, max_sum_hi));
    }

    let (lo0, _) = inv_bounds(a as u64);
    let (mut dp_in, mut dp_out) = match state[0] {
        STATE_IN => (lo0, INF_SCALED),
        STATE_OUT => (INF_SCALED, 0),
        _ => (lo0, 0),
    };

    for i in 1..len {
        let (w_lo, _) = inv_bounds((a as u64) + (i as u64));
        let prev_min = dp_in.min(dp_out);
        let add_in = if prev_min >= INF_SCALED {
            INF_SCALED
        } else {
            prev_min + w_lo
        };
        let (next_in, next_out) = match state[i] {
            STATE_IN => (add_in, INF_SCALED),
            STATE_OUT => (INF_SCALED, dp_in),
            _ => (add_in, dp_in),
        };
        dp_in = next_in;
        dp_out = next_out;
    }

    let min_sum_lo = dp_in.min(dp_out);
    if min_sum_lo >= INF_SCALED {
        None
    } else {
        Some((min_sum_lo, max_sum_hi))
    }
}

/// Forward-backward `u128` DP reduced-cost domain filtering on `state` (`enforce_gap2 = true`).
/// Returns `false` if `state` is infeasible (`min_sum_lo > ONE_SCALED` or `max_sum_hi < ONE_SCALED`
/// or `gap <= 2` violated). Forces variables whose opposite value violates `ONE_SCALED`,
/// returning `(feasible, any_changed, min_sum_lo, max_sum_hi)`.
pub fn propagate_sum_bounds_reduced_cost(
    a: u32,
    b: u32,
    state: &mut [i8],
    enforce_gap2: bool,
    l_in: &mut [u128],
    l_out: &mut [u128],
    r_in: &mut [u128],
    r_out: &mut [u128],
) -> (bool, bool, u128, u128) {
    let len = (b - a + 1) as usize;
    if !enforce_gap2 {
        let Some((min_lo, max_hi)) = compute_sum_bounds(a, b, state, false) else {
            return (false, false, INF_SCALED, 0);
        };
        if max_hi < ONE_SCALED || min_lo > ONE_SCALED {
            return (false, false, min_lo, max_hi);
        }
        let mut changed = false;
        for i in 0..len {
            if state[i] == STATE_UNK {
                let (lo, hi) = inv_bounds((a as u64) + (i as u64));
                if max_hi - hi < ONE_SCALED {
                    state[i] = STATE_IN;
                    changed = true;
                } else if min_lo + lo > ONE_SCALED {
                    state[i] = STATE_OUT;
                    changed = true;
                }
            }
        }
        return (true, changed, min_lo, max_hi);
    }

    let mut max_hi: u128 = 0;
    for i in 0..len {
        if state[i] != STATE_OUT {
            max_hi += inv_bounds((a as u64) + (i as u64)).1;
        } else if i > 0 && state[i - 1] == STATE_OUT {
            return (false, false, INF_SCALED, 0);
        }
    }
    if max_hi < ONE_SCALED {
        return (false, false, 0, max_hi);
    }

    // Forward DP
    let (lo0, _) = inv_bounds(a as u64);
    match state[0] {
        STATE_IN => {
            l_in[0] = lo0;
            l_out[0] = INF_SCALED;
        }
        STATE_OUT => {
            l_in[0] = INF_SCALED;
            l_out[0] = 0;
        }
        _ => {
            l_in[0] = lo0;
            l_out[0] = 0;
        }
    }
    for i in 1..len {
        let (w_lo, _) = inv_bounds((a as u64) + (i as u64));
        let prev_min = l_in[i - 1].min(l_out[i - 1]);
        let add_in = if prev_min >= INF_SCALED {
            INF_SCALED
        } else {
            prev_min + w_lo
        };
        match state[i] {
            STATE_IN => {
                l_in[i] = add_in;
                l_out[i] = INF_SCALED;
            }
            STATE_OUT => {
                l_in[i] = INF_SCALED;
                l_out[i] = l_in[i - 1];
            }
            _ => {
                l_in[i] = add_in;
                l_out[i] = l_in[i - 1];
            }
        }
    }

    let min_lo = l_in[len - 1].min(l_out[len - 1]);
    if min_lo > ONE_SCALED {
        return (false, false, min_lo, max_hi);
    }

    // Backward DP
    let (lo_last, _) = inv_bounds(b as u64);
    match state[len - 1] {
        STATE_IN => {
            r_in[len - 1] = lo_last;
            r_out[len - 1] = INF_SCALED;
        }
        STATE_OUT => {
            r_in[len - 1] = INF_SCALED;
            r_out[len - 1] = 0;
        }
        _ => {
            r_in[len - 1] = lo_last;
            r_out[len - 1] = 0;
        }
    }
    for i in (0..len - 1).rev() {
        let (w_lo, _) = inv_bounds((a as u64) + (i as u64));
        let next_min = r_in[i + 1].min(r_out[i + 1]);
        let add_in = if next_min >= INF_SCALED {
            INF_SCALED
        } else {
            next_min + w_lo
        };
        match state[i] {
            STATE_IN => {
                r_in[i] = add_in;
                r_out[i] = INF_SCALED;
            }
            STATE_OUT => {
                r_in[i] = INF_SCALED;
                r_out[i] = r_in[i + 1];
            }
            _ => {
                r_in[i] = add_in;
                r_out[i] = r_in[i + 1];
            }
        }
    }

    let mut changed = false;
    for i in 0..len {
        if state[i] != STATE_UNK {
            continue;
        }
        let (w_lo, w_hi) = inv_bounds((a as u64) + (i as u64));
        // Can i be OUT?
        let out_impossible = (max_hi - w_hi < ONE_SCALED)
            || (l_out[i] >= INF_SCALED)
            || (r_out[i] >= INF_SCALED)
            || (l_out[i] + r_out[i] > ONE_SCALED);
        // Can i be IN?
        let in_impossible = (l_in[i] >= INF_SCALED)
            || (r_in[i] >= INF_SCALED)
            || (l_in[i] + r_in[i] - w_lo > ONE_SCALED);

        if out_impossible && in_impossible {
            return (false, changed, min_lo, max_hi);
        }
        if out_impossible {
            state[i] = STATE_IN;
            changed = true;
        } else if in_impossible {
            // Setting i to OUT also requires neighbors to be IN; check immediate conflict
            if (i > 0 && state[i - 1] == STATE_OUT)
                || (i + 1 < len && state[i + 1] == STATE_OUT)
            {
                return (false, changed, min_lo, max_hi);
            }
            state[i] = STATE_OUT;
            if i > 0 && state[i - 1] == STATE_UNK {
                state[i - 1] = STATE_IN;
            }
            if i + 1 < len && state[i + 1] == STATE_UNK {
                state[i + 1] = STATE_IN;
            }
            max_hi -= w_hi;
            if max_hi < ONE_SCALED {
                return (false, true, min_lo, max_hi);
            }
            changed = true;
        }
    }

    (true, changed, min_lo, max_hi)
}

#[inline]
pub const fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

#[inline]
pub const fn lcm_u128(a: u128, b: u128) -> u128 {
    if a == 0 || b == 0 {
        0
    } else {
        (a / gcd_u128(a, b)) * b
    }
}

/// Modular inverse `a^{-1} mod m` using extended Euclidean algorithm (`gcd(a, m) == 1`).
#[inline]
pub fn mod_inv_u64(a: u64, m: u64) -> u64 {
    if m <= 1 {
        return 0;
    }
    let mut t: i128 = 0;
    let mut new_t: i128 = 1;
    let mut r: i128 = m as i128;
    let mut new_r: i128 = (a % m) as i128;
    while new_r != 0 {
        let q = r / new_r;
        let tmp_t = t - q * new_t;
        t = new_t;
        new_t = tmp_t;
        let tmp_r = r - q * new_r;
        r = new_r;
        new_r = tmp_r;
    }
    debug_assert_eq!(r, 1, "mod_inv_u64 called with non-coprime arguments");
    if t < 0 {
        (t + m as i128) as u64
    } else {
        t as u64
    }
}

/// Fast simple sieve of primes up to `limit` (`limit <= 10^8`).
/// Uses an odd-only bitset (~6.25 MB at `10^8`).
pub fn sieve_primes(limit: u32) -> (Vec<u64>, Vec<u32>) {
    if limit < 2 {
        return (Vec::new(), Vec::new());
    }
    let odd_count = ((limit as usize) / 2) + 1; // index k represents 2*k + 1
    let words = (odd_count + 63) / 64;
    let mut is_comp_odd = vec![0u64; words];
    is_comp_odd[0] |= 1; // 1 is not prime (k = 0 -> 1)

    let sqrt_lim = (limit as f64).sqrt() as usize + 1;
    let max_k = sqrt_lim / 2;
    for k in 1..=max_k {
        if (is_comp_odd[k >> 6] >> (k & 63)) & 1 == 0 {
            let p = 2 * k + 1;
            let mut j = (p * p) / 2;
            while j < odd_count {
                is_comp_odd[j >> 6] |= 1u64 << (j & 63);
                j += p;
            }
        }
    }

    // Approximate prime count pi(x) ~ x / (ln(x) - 1.1)
    let est = if limit > 100 {
        ((limit as f64) / ((limit as f64).ln() - 1.15)) as usize + 64
    } else {
        limit as usize
    };
    let mut primes = Vec::with_capacity(est);
    primes.push(2);
    let max_idx = ((limit - 1) / 2) as usize;
    for k in 1..=max_idx {
        if (is_comp_odd[k >> 6] >> (k & 63)) & 1 == 0 {
            primes.push((2 * k + 1) as u32);
        }
    }
    (is_comp_odd, primes)
}

#[inline]
pub fn is_prime_from_odd_bitset(n: u32, is_comp_odd: &[u64]) -> bool {
    if n < 2 {
        return false;
    }
    if n == 2 {
        return true;
    }
    if (n & 1) == 0 {
        return false;
    }
    let k = (n >> 1) as usize;
    ((is_comp_odd[k >> 6] >> (k & 63)) & 1) == 0
}

#[derive(Debug, Clone, Serialize)]
pub struct PmEntry {
    pub m: usize,
    pub d_m: u128,
    pub max_n_c: u128,
    pub num_primes: usize,
    pub max_prime: u32,
    pub small_primes_sample: Vec<u32>,
}

/// Precomputed exact data for `D_m = lcm(1..=m)` and `P_m` (`1 <= m <= max_m`, default `18`).
/// Also stores `max_m_allowed[p]` (encoded per prime or up to `max_n_c`) = largest `m <= max_m`
/// such that `p not in P_m` (`>= 1` for every prime since `P_1 = empty`).
pub struct PmTable {
    pub max_m: usize,
    pub d_m: Vec<u128>,
    pub max_n_c: Vec<u128>,
    pub p_m_sets: Vec<Vec<u32>>,
    max_prime_in_any: u32,
    /// Indexed by `p` up to `max_prime_in_any`: smallest `m` (`2..=max_m`) where `p in P_m`,
    /// or `0` if `p not in P_{max_m}`. Then `max_m_allowed(p) = if first == 0 { max_m } else { first - 1 }`.
    first_m_in_pm: Vec<u8>,
}

impl PmTable {
    /// Computes `D_m` and `P_m` in exact `u128` arithmetic for all `1 <= m <= max_m` (`max_m <= 18`).
    pub fn compute(max_m: usize) -> Self {
        assert!((1..=18).contains(&max_m), "max_m must be in 1..=18");
        let mut d_m = vec![0u128; max_m + 1];
        let mut max_n_c = vec![0u128; max_m + 1];
        d_m[0] = 1;
        for m in 1..=max_m {
            d_m[m] = lcm_u128(d_m[m - 1], m as u128);
            let mut sum = 0u128;
            for c in 1..=m {
                sum += d_m[m] / (c as u128);
            }
            max_n_c[m] = sum;
        }

        let top_nc = max_n_c[max_m] as u32;
        let (_, primes) = sieve_primes(top_nc);
        let mut first_m_in_pm = vec![0u8; (top_nc as usize) + 1];
        let mut p_m_sets = vec![Vec::new(); max_m + 1];

        // Reusable bitset for N_C values up to max_n_c[m]
        let mut seen_words = vec![0u64; ((top_nc as usize) + 64) / 64];

        for m in 1..=max_m {
            let dm = d_m[m];
            let max_nc = max_n_c[m] as usize;
            let used_words = (max_nc + 64) / 64;
            seen_words[..used_words].fill(0);

            let mut weights = [0u128; 18];
            for c in 1..=m {
                weights[c - 1] = dm / (c as u128);
            }

            // Subset-sum DP / binary tree over 1 <= mask < (1 << m) in exact u128
            let total_masks = 1usize << m;
            let mut subset_sums = vec![0u128; total_masks];
            for bit in 0..m {
                let w = weights[bit];
                let half = 1usize << bit;
                for prev in 0..half {
                    let s = subset_sums[prev] + w;
                    subset_sums[half + prev] = s;
                    let idx = s as usize;
                    seen_words[idx >> 6] |= 1u64 << (idx & 63);
                }
            }

            let mut pm_list = Vec::new();
            for &p in &primes {
                if (p as usize) > max_nc {
                    break;
                }
                // Check if any multiple of p up to max_nc has bit set in seen_words
                let pu = p as usize;
                let mut found = if first_m_in_pm[pu] != 0 {
                    // Since P_1 subseteq P_2 subseteq ... subseteq P_m, verify monotonicity!
                    true
                } else {
                    false
                };
                if !found {
                    let mut mult = pu;
                    while mult <= max_nc {
                        if ((seen_words[mult >> 6] >> (mult & 63)) & 1) != 0 {
                            found = true;
                            break;
                        }
                        mult += pu;
                    }
                    if found {
                        first_m_in_pm[pu] = m as u8;
                    }
                }
                if found {
                    pm_list.push(p);
                }
            }
            p_m_sets[m] = pm_list;
        }

        let max_prime_in_any = p_m_sets[max_m].last().copied().unwrap_or(0);
        Self {
            max_m,
            d_m,
            max_n_c,
            p_m_sets,
            max_prime_in_any,
            first_m_in_pm,
        }
    }

    /// Returns `true` iff `p in P_m` (`1 <= m <= self.max_m`).
    #[inline]
    pub fn contains(&self, m: usize, p: u32) -> bool {
        debug_assert!((1..=self.max_m).contains(&m));
        if p > self.max_prime_in_any || (p as usize) >= self.first_m_in_pm.len() {
            return false;
        }
        let fm = self.first_m_in_pm[p as usize];
        fm != 0 && (fm as usize) <= m
    }

    /// Largest `m` in `1..=self.max_m` such that `p not in P_m`.
    /// Always `>= 1` because `P_1 = empty`.
    #[inline]
    pub fn max_m_not_containing(&self, p: u32) -> usize {
        if p > self.max_prime_in_any || (p as usize) >= self.first_m_in_pm.len() {
            return self.max_m;
        }
        let fm = self.first_m_in_pm[p as usize];
        if fm == 0 {
            self.max_m
        } else {
            (fm as usize) - 1
        }
    }

    pub fn summary(&self) -> Vec<PmEntry> {
        (1..=self.max_m)
            .map(|m| {
                let set = &self.p_m_sets[m];
                PmEntry {
                    m,
                    d_m: self.d_m[m],
                    max_n_c: self.max_n_c[m],
                    num_primes: set.len(),
                    max_prime: set.last().copied().unwrap_or(0),
                    small_primes_sample: set.iter().take(12).copied().collect(),
                }
            })
            .collect()
    }
}

/// Prefix tables in `u128` for `O(1)` exact initial candidate `(a, b)` filtering up to `max_b`.
pub struct PrefixHarmonicBounds {
    pub pref_hi: Vec<u128>,
    pub pref_lo_even: Vec<u128>,
    pub pref_lo_odd: Vec<u128>,
}

impl PrefixHarmonicBounds {
    pub fn new(max_b: u32) -> Self {
        let n = (max_b as usize) + 1;
        let mut pref_hi = vec![0u128; n];
        let mut pref_lo_even = vec![0u128; n];
        let mut pref_lo_odd = vec![0u128; n];
        for x in 1..=max_b {
            let idx = x as usize;
            let (lo, hi) = inv_bounds(x as u64);
            pref_hi[idx] = pref_hi[idx - 1] + hi;
            pref_lo_even[idx] = pref_lo_even[idx - 1] + if (x & 1) == 0 { lo } else { 0 };
            pref_lo_odd[idx] = pref_lo_odd[idx - 1] + if (x & 1) == 1 { lo } else { 0 };
        }
        Self {
            pref_hi,
            pref_lo_even,
            pref_lo_odd,
        }
    }

    /// Exact initial `(min_sum_lo, max_sum_hi)` for `[a, b]` with `a in S`, `b in S`, `enforce_gap2 = true`.
    #[inline]
    pub fn initial_bounds_gap2(&self, a: u32, b: u32) -> (u128, u128) {
        let ai = a as usize;
        let bi = b as usize;
        let max_hi = self.pref_hi[bi] - self.pref_hi[ai - 1];
        let base_lo = if (a & 1) == 0 {
            self.pref_lo_even[bi] - self.pref_lo_even[ai - 1]
        } else {
            self.pref_lo_odd[bi] - self.pref_lo_odd[ai - 1]
        };
        let extra = if ((b - a) & 1) == 1 {
            inv_bounds(b as u64).0
        } else {
            0
        };
        (base_lo + extra, max_hi)
    }

    #[inline]
    pub fn is_candidate(&self, a: u32, b: u32) -> bool {
        if a < 2 || a >= b {
            return false;
        }
        let (min_lo, max_hi) = self.initial_bounds_gap2(a, b);
        max_hi >= ONE_SCALED && min_lo <= ONE_SCALED
    }

    /// Returns all candidate `a` values in `2..b` for a fixed `b` in ascending order,
    /// found via binary search in `O(log b + #candidates)`.
    pub fn candidate_a_list(&self, b: u32) -> Vec<u32> {
        if b < 4 {
            return Vec::new();
        }
        let bi = b as usize;
        // Find largest a in 2..b with pref_hi[b] - pref_hi[a-1] >= ONE_SCALED
        let mut lo = 2u32;
        let mut hi = b; // exclusive
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.pref_hi[bi] - self.pref_hi[(mid - 1) as usize] >= ONE_SCALED {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let a_max = lo - 1;
        if a_max < 2 || self.pref_hi[bi] - self.pref_hi[(a_max - 1) as usize] < ONE_SCALED {
            return Vec::new();
        }

        // Binary search minimum even a >= 2 and odd a >= 3 with min_lo <= ONE_SCALED
        let find_min_parity = |parity: u32| -> u32 {
            let first = if parity == 0 { 2u32 } else { 3u32 };
            if first > a_max {
                return a_max + 2;
            }
            let max_k = (a_max - first) / 2;
            let mut klo = 0u32;
            let mut khi = max_k + 1;
            while klo < khi {
                let kmid = klo + (khi - klo) / 2;
                let a = first + 2 * kmid;
                if self.initial_bounds_gap2(a, b).0 <= ONE_SCALED {
                    khi = kmid;
                } else {
                    klo = kmid + 1;
                }
            }
            first + 2 * klo
        };

        let min_even = find_min_parity(0);
        let min_odd = find_min_parity(1);
        let a_start = min_even.min(min_odd);
        if a_start > a_max {
            return Vec::new();
        }
        let mut out = Vec::with_capacity((a_max - a_start + 1) as usize);
        for a in a_start..=a_max {
            let ok = if (a & 1) == 0 {
                a >= min_even
            } else {
                a >= min_odd
            };
            if ok {
                out.push(a);
            }
        }
        out
    }

    /// Exact count of candidate `a` values in `2..b` in `O(log b)` time (without allocating a Vec).
    pub fn candidate_a_range_and_count(&self, b: u32) -> (u32, u32, usize) {
        if b < 4 {
            return (0, 0, 0);
        }
        let bi = b as usize;
        let mut lo = 2u32;
        let mut hi = b;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.pref_hi[bi] - self.pref_hi[(mid - 1) as usize] >= ONE_SCALED {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let a_max = lo - 1;
        if a_max < 2 || self.pref_hi[bi] - self.pref_hi[(a_max - 1) as usize] < ONE_SCALED {
            return (0, 0, 0);
        }

        let count_parity = |parity: u32| -> (u32, usize) {
            let first = if parity == 0 { 2u32 } else { 3u32 };
            if first > a_max {
                return (u32::MAX, 0);
            }
            let max_k = (a_max - first) / 2;
            let mut klo = 0u32;
            let mut khi = max_k + 1;
            while klo < khi {
                let kmid = klo + (khi - klo) / 2;
                let a = first + 2 * kmid;
                if self.initial_bounds_gap2(a, b).0 <= ONE_SCALED {
                    khi = kmid;
                } else {
                    klo = kmid + 1;
                }
            }
            if klo > max_k {
                (u32::MAX, 0)
            } else {
                (first + 2 * klo, (max_k - klo + 1) as usize)
            }
        };

        let (min_even, cnt_even) = count_parity(0);
        let (min_odd, cnt_odd) = count_parity(1);
        let total = cnt_even + cnt_odd;
        if total == 0 {
            (0, 0, 0)
        } else {
            (min_even.min(min_odd), a_max, total)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum KillReason {
    PadicConflict,
    SumBounds,
}

#[derive(Debug, Clone, Serialize)]
pub struct PropagationResult {
    pub killed: bool,
    pub reason: Option<KillReason>,
    pub forced_in: usize,
    pub forced_out: usize,
    pub unknown: usize,
    pub min_sum_lo: u128,
    pub max_sum_hi: u128,
}

/// Reusable workspace buffers for exact `u128` + `p`-adic propagation.
pub struct PropagatorBuffers {
    pub state: Vec<i8>,
    pub list: Vec<u32>,
    pub l_in: Vec<u128>,
    pub l_out: Vec<u128>,
    pub r_in: Vec<u128>,
    pub r_out: Vec<u128>,
}

impl PropagatorBuffers {
    pub fn with_capacity(max_len: usize) -> Self {
        Self {
            state: vec![0; max_len],
            list: Vec::with_capacity(64),
            l_in: vec![0; max_len],
            l_out: vec![0; max_len],
            r_in: vec![0; max_len],
            r_out: vec![0; max_len],
        }
    }

    pub fn ensure_len(&mut self, len: usize) {
        if self.state.len() < len {
            self.state.resize(len, 0);
            self.l_in.resize(len, 0);
            self.l_out.resize(len, 0);
            self.r_in.resize(len, 0);
            self.r_out.resize(len, 0);
        }
    }
}

#[inline]
fn set_in(state: &mut [i8], idx: usize) -> bool {
    if state[idx] == STATE_OUT {
        return false;
    }
    state[idx] = STATE_IN;
    true
}

#[inline]
fn set_out(state: &mut [i8], idx: usize, enforce_gap2: bool) -> bool {
    if state[idx] == STATE_IN {
        return false;
    }
    state[idx] = STATE_OUT;
    if enforce_gap2 {
        if idx > 0 && !set_in(state, idx - 1) {
            return false;
        }
        if idx + 1 < state.len() && !set_in(state, idx + 1) {
            return false;
        }
    }
    true
}

/// Exact `u128` + `p`-adic + `gap <= 2` constraint propagation on `[a, b]`.
/// Zero floating point is used anywhere.
pub fn test_interval_exact(
    a: u32,
    b: u32,
    primes: &[u32],
    buf: &mut PropagatorBuffers,
    max_subset_size: usize,
    enforce_gap2: bool,
) -> PropagationResult {
    let len = (b - a + 1) as usize;
    buf.ensure_len(len);
    let state = &mut buf.state[..len];
    state.fill(STATE_UNK);
    state[0] = STATE_IN;
    state[len - 1] = STATE_IN;

    let max_pi = primes.partition_point(|&p| p <= b);

    let mut changed = true;
    let mut pass = 0usize;
    let mut invs = [0u32; 20];
    let max_m = max_subset_size.min(20);

    while changed {
        changed = false;
        pass += 1;
        let limit_m = if pass == 1 { 3.min(max_m) } else { max_m };

        for pi in (0..max_pi).rev() {
            let p = primes[pi] as u64;
            let mut pk = p;
            while pk * p <= (b as u64) {
                pk *= p;
            }

            let mut found_q: u64 = 0;
            buf.list.clear();
            while pk >= p {
                let first = (((a as u64) + pk - 1) / pk) * pk;
                if first <= (b as u64) {
                    let mut x = first;
                    while x <= (b as u64) {
                        if state[(x as u32 - a) as usize] != STATE_OUT {
                            buf.list.push(x as u32);
                        }
                        x += pk;
                    }
                    if !buf.list.is_empty() {
                        found_q = pk;
                        break;
                    }
                }
                pk /= p;
            }

            if found_q == 0 {
                continue;
            }
            let m = buf.list.len();

            if m == 1 {
                let idx = (buf.list[0] - a) as usize;
                if !set_out(state, idx, enforce_gap2) {
                    return PropagationResult {
                        killed: true,
                        reason: Some(KillReason::PadicConflict),
                        forced_in: 0,
                        forced_out: 0,
                        unknown: 0,
                        min_sum_lo: 0,
                        max_sum_hi: 0,
                    };
                }
                changed = true;
                continue;
            }

            if m == 2 && max_m >= 2 {
                let x0 = buf.list[0] as u64;
                let x1 = buf.list[1] as u64;
                let i0 = (buf.list[0] - a) as usize;
                let i1 = (buf.list[1] - a) as usize;
                let c0 = (x0 / found_q) % p;
                let c1 = (x1 / found_q) % p;
                if (c0 + c1) % p != 0 {
                    if !set_out(state, i0, enforce_gap2) || !set_out(state, i1, enforce_gap2) {
                        return PropagationResult {
                            killed: true,
                            reason: Some(KillReason::PadicConflict),
                            forced_in: 0,
                            forced_out: 0,
                            unknown: 0,
                            min_sum_lo: 0,
                            max_sum_hi: 0,
                        };
                    }
                    changed = true;
                } else if state[i0] == STATE_IN && state[i1] == STATE_UNK {
                    if !set_in(state, i1) {
                        return PropagationResult {
                            killed: true,
                            reason: Some(KillReason::PadicConflict),
                            forced_in: 0,
                            forced_out: 0,
                            unknown: 0,
                            min_sum_lo: 0,
                            max_sum_hi: 0,
                        };
                    }
                    changed = true;
                } else if state[i1] == STATE_IN && state[i0] == STATE_UNK {
                    if !set_in(state, i0) {
                        return PropagationResult {
                            killed: true,
                            reason: Some(KillReason::PadicConflict),
                            forced_in: 0,
                            forced_out: 0,
                            unknown: 0,
                            min_sum_lo: 0,
                            max_sum_hi: 0,
                        };
                    }
                    changed = true;
                }
                continue;
            }

            if m <= limit_m {
                let p_u32 = p as u32;
                let mut forced_in_mask = 0u32;
                for i in 0..m {
                    let c = ((buf.list[i] as u64) / found_q) % p;
                    invs[i] = mod_inv_u64(c, p) as u32;
                    if state[(buf.list[i] - a) as usize] == STATE_IN {
                        forced_in_mask |= 1u32 << i;
                    }
                }

                let total_masks = 1u32 << m;
                let mut valid_count = 0u32;
                let mut always_in = total_masks - 1;
                let mut ever_in = 0u32;

                for mask in 0..total_masks {
                    if (mask & forced_in_mask) != forced_in_mask {
                        continue;
                    }
                    let mut sum = 0u32;
                    for i in 0..m {
                        if (mask & (1u32 << i)) != 0 {
                            sum += invs[i];
                            if sum >= p_u32 {
                                sum -= p_u32;
                            }
                        }
                    }
                    if sum == 0 {
                        valid_count += 1;
                        always_in &= mask;
                        ever_in |= mask;
                    }
                }

                if valid_count == 0 {
                    return PropagationResult {
                        killed: true,
                        reason: Some(KillReason::PadicConflict),
                        forced_in: 0,
                        forced_out: 0,
                        unknown: 0,
                        min_sum_lo: 0,
                        max_sum_hi: 0,
                    };
                }

                for i in 0..m {
                    let idx = (buf.list[i] - a) as usize;
                    let bit = 1u32 << i;
                    if (always_in & bit) != 0 && state[idx] == STATE_UNK {
                        if !set_in(state, idx) {
                            return PropagationResult {
                                killed: true,
                                reason: Some(KillReason::PadicConflict),
                                forced_in: 0,
                                forced_out: 0,
                                unknown: 0,
                                min_sum_lo: 0,
                                max_sum_hi: 0,
                            };
                        }
                        changed = true;
                    } else if (ever_in & bit) == 0 && state[idx] == STATE_UNK {
                        if !set_out(state, idx, enforce_gap2) {
                            return PropagationResult {
                                killed: true,
                                reason: Some(KillReason::PadicConflict),
                                forced_in: 0,
                                forced_out: 0,
                                unknown: 0,
                                min_sum_lo: 0,
                                max_sum_hi: 0,
                            };
                        }
                        changed = true;
                    }
                }
            }
        }

        if !changed && pass == 1 {
            changed = true;
            continue;
        }

        let (feasible, rc_changed, min_lo, max_hi) = propagate_sum_bounds_reduced_cost(
            a,
            b,
            state,
            enforce_gap2,
            &mut buf.l_in[..len],
            &mut buf.l_out[..len],
            &mut buf.r_in[..len],
            &mut buf.r_out[..len],
        );
        if !feasible {
            return PropagationResult {
                killed: true,
                reason: Some(KillReason::SumBounds),
                forced_in: 0,
                forced_out: 0,
                unknown: 0,
                min_sum_lo: min_lo,
                max_sum_hi: max_hi,
            };
        }
        if rc_changed {
            changed = true;
        }
    }

    let mut forced_in = 0usize;
    let mut forced_out = 0usize;
    let mut unknown = 0usize;
    for &s in state.iter() {
        if s == STATE_IN {
            forced_in += 1;
        } else if s == STATE_OUT {
            forced_out += 1;
        } else {
            unknown += 1;
        }
    }
    let (min_sum_lo, max_sum_hi) = compute_sum_bounds(a, b, state, enforce_gap2).unwrap();
    PropagationResult {
        killed: false,
        reason: None,
        forced_in,
        forced_out,
        unknown,
        min_sum_lo,
        max_sum_hi,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Verifies that genuine Egyptian fraction decompositions of 1 SURVIVE
    /// when `enforce_gap2 = false` (and stay consistent even when we pre-fix the
    /// exact witness subset into `state`!).
    #[test]
    fn test_sanity_egyptian_decompositions_survive_without_gap2() {
        let (_, primes) = sieve_primes(100);
        let mut buf = PropagatorBuffers::with_capacity(100);

        let witnesses: &[(&[u32], u32, u32)] = &[
            (&[2, 3, 6], 2, 6),
            (&[2, 4, 6, 12], 2, 12),
            (&[2, 3, 7, 42], 2, 42),
        ];

        for &(subset, a, b) in witnesses {
            // 1. Interval [a, b] must NOT be killed when enforce_gap2 = false
            let res = test_interval_exact(a, b, &primes, &mut buf, 12, false);
            assert!(
                !res.killed,
                "Interval [{a}, {b}] for genuine decomposition {subset:?} was wrongly killed!"
            );
            assert!(res.min_sum_lo <= ONE_SCALED && res.max_sum_hi >= ONE_SCALED);

            // 2. Moreover, no element of `subset` may be forced OUT, and no element outside `subset`
            //    may be forced IN unless all genuine decompositions on [a, b] share it!
            let len = (b - a + 1) as usize;
            let state = &buf.state[..len];
            for &x in subset {
                assert_ne!(
                    state[(x - a) as usize],
                    STATE_OUT,
                    "Element {x} of {subset:?} was wrongly forced OUT in [{a}, {b}]!"
                );
            }

            // 3. Direct sum bounds check on exact subset assignment
            let mut exact_state = vec![STATE_OUT; len];
            for &x in subset {
                exact_state[(x - a) as usize] = STATE_IN;
            }
            let (lo, hi) = compute_sum_bounds(a, b, &exact_state, false).unwrap();
            assert!(
                lo <= ONE_SCALED && ONE_SCALED <= hi,
                "Exact subset {subset:?} failed u128 interval containment: lo={lo}, ONE={ONE_SCALED}, hi={hi}"
            );
        }
    }

    #[test]
    fn test_b_le_2000_exact_464286_candidates_and_zero_survivors() {
        let max_b = 2000u32;
        let (_, primes) = sieve_primes(max_b);
        let pref = PrefixHarmonicBounds::new(max_b);
        let mut buf = PropagatorBuffers::with_capacity((max_b + 1) as usize);

        let mut total_candidates = 0usize;
        let mut survivors = 0usize;
        for b in 4..=max_b {
            let cands = pref.candidate_a_list(b);
            let (_, _, fast_cnt) = pref.candidate_a_range_and_count(b);
            assert_eq!(cands.len(), fast_cnt);
            total_candidates += cands.len();
            for a in cands {
                let res = test_interval_exact(a, b, &primes, &mut buf, 10, true);
                if !res.killed {
                    survivors += 1;
                }
            }
        }
        assert_eq!(
            total_candidates, 464_286,
            "Candidate count for b <= 2000 must match 464,286"
        );
        assert_eq!(survivors, 0, "Expected 0 survivors for b <= 2000");
    }

    #[test]
    fn test_pm_table_exact_small_and_up_to_18() {
        let pm = PmTable::compute(18);
        assert!(pm.p_m_sets[1].is_empty());
        assert_eq!(pm.p_m_sets[2], vec![2, 3]);
        // m = 3: D_3 = 6; subsets of {6, 3, 2}: 2, 3, 5, 6, 8, 9, 11 -> primes {2, 3, 5, 11}
        assert_eq!(pm.p_m_sets[3], vec![2, 3, 5, 11]);
        assert!(!pm.contains(3, 7)); // 7 is NOT in P_3!
        assert_eq!(pm.d_m[18], 12_252_240);
        assert_eq!(pm.max_n_c[18], 42_822_903);
        // Check monotonicity P_1 subseteq P_2 subseteq ... subseteq P_18
        for m in 1..18 {
            for &p in &pm.p_m_sets[m] {
                assert!(pm.contains(m + 1, p));
            }
        }
    }
}

# Erdős #287 — Our Contribution (Partial Results & Reduction)

**Language:** **English** · [Português](pt/CONTRIBUTION.md)

**Tabs:** [Home](../../README.md) · [Proposition](README.md) · [State of the Art](STATUS.md) · **Contribution** · [Computational](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · [Barriers](BARRIERS.md) · [Collaborate](OPEN_QUESTIONS.md)

---

While the full conjecture remains open, our investigation establishes **five concrete contributions** (strictly separating unconditional results from conditional ones):

## 1. Exact Harmonic Window & Pure-Rational $N$-Block Lemma (**Unconditional**)
For **every** candidate triple $(a, b, S)$ ($b \ge 4$), we prove without asymptotic error terms:
$$\frac{b + 1}{e^2} < a < \frac{b}{e} + 1.$$
Moreover, for formal certificates free of `Real.log`, we prove in $\mathbb{Q}$ that $N v \le (N + 1) u \implies \sum_{y = u + 1}^v \frac{1}{y} < \frac{1}{N}$. Iterating $u \mapsto \lfloor 5 u / 4 \rfloor$ four times (`coverHi4 x` $\approx 2.441 x$), any candidate with $b \le \mathrm{coverHi4}(x)$ must satisfy $a \le x$.

## 2. Exponential Sharpening of the $p$-adic Threshold (**Unconditional**)
Instead of $p > m! H_m$, we prove that $p > m$, $b < (m + 1)p$, and $p \notin \widetilde{\mathcal{P}}_m$ (in particular $p > \operatorname{lcm}(1, \dots, m) H_m$) already forbid **all** multiples $c p$ from $S$. This lifts the asymptotic reach from $m(b) \sim \frac{\ln b}{\ln \ln b}$ to $m(b) \sim (1 - \varepsilon)\ln b$. We computed $\widetilde{\mathcal{P}}_m$ exactly in `u128` up to $m = 18$ ($D_{18} = 12\,252\,240$, $D_{18} H_{18} = 42\,822\,903$).

## 3. Unconditional Shrinking of Both Window Boundaries (**Unconditional — Paper**)
In [docs/ROUTE_B_ANALYSIS.md](docs/ROUTE_B_ANALYSIS.md):
- **Theorem B.1 (Upper edge $a \approx b/e$):** Using forbidden primes in $(b/2, b]$ and Dusart (2010), we unconditionally eliminate $a - 1 \ge \frac{b}{e} - \frac{0.20\, b}{\ln b}$ for $b \ge 20\,744$ (and $\Theta(\frac{b \ln \ln b}{\ln b})$ via $\mathcal{F}_1(b)$).
- **Theorem B.2 (Lower edge $a \approx b/e^2$):** We prove the convexity charging inequality $H_b - H_{a-1} < 2 - \sum_{x \in S} \frac{2 - \nu_T(x)}{2x}$, showing that each parity switch in $T$ between odd primes $p \in (2b/3, b)$ and even semiprimes $2q$ ($q \in (b/3, b/2)$) incurs a penalty $> \frac{1}{b}$, shrinking the lower edge unconditionally by $\Omega(\ln^2 b)$.

## 4. Weak Conditional Reduction Without Sophie Germain Primes (**Conditional — Verified in Lean 4**)
We formalize `erdos_287_of_linear_prime_collision_hyp` ([ConditionalReduction.lean](lean/Erdos287/ConditionalReduction.lean)): the full conjecture follows from `LinearPrimeCollisionHyp 20000`, which requires only **one** consecutive forbidden pair $(c_1 p_1, c_2 p_2)$ in each wide multiplicative window $[b / 2.441,\; b - 1]$ — **strictly weaker** than Sophie Germain primes in short intervals (and ablation `M3` confirms contiguous coverage from $b = 87$ to $10^7$ even when $(c_1, c_2) \in \{(1,2), (2,1)\}$ is completely forbidden).

## 5. Exact Finite Certificates (**Unconditional on Tested Ranges**)
- **Lean 4 kernel (zero `native_decide`):** `erdos_287_upto_20000` formally proves $\max\text{-gap} \ge 3$ for all $b \le 20\,000$ using only **13 witness pairs**.
- **Rust verifier (exact `u128`):** $0$ counterexamples for all $4 \le b \le 10^8$ in `0.61s`.

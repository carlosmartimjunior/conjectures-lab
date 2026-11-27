# Erdős #287 — Why We Did Not Close the Full Proof (Barriers & Discarded Routes)

**Language:** **English** · [Português](pt/BARRIERS.md)

**Tabs:** [Home](../../README.md) · [Proposition](README.md) · [State of the Art](STATUS.md) · [Contribution](CONTRIBUTION.md) · [Computational](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · **Barriers** · [Collaborate](OPEN_QUESTIONS.md)

---

This page documents **where** our unconditional proof attempt stalled and **why**, combining mathematical barrier proofs with constructive SAT counterexamples.

## 1. Vanishing Density Barrier (Failure of Pigeonhole)
Even after sharpening the $p$-adic threshold to $p > \operatorname{lcm}(1, \dots, m) H_m$ (allowing $m(b) \sim \frac{1}{2} \ln b$), the single-prime forbidden set $\mathcal{F}_1(b) \subseteq [b/e, b]$ has cardinality
$$|\mathcal{F}_1(b)| \sim \frac{(1 - e^{-1})\, b \ln \ln b}{\ln b},$$
whose relative density $\sim \frac{\ln \ln b}{\ln b} \to 0$ lies far below $1/2$. Counting alone therefore cannot force two consecutive forbidden integers.

## 2. The Selberg Parity Barrier in Sieve Theory (Route A)
Although we removed any reliance on Sophie Germain primes $(p, 2p \pm 1)$ — any solution to $c_1 p_1 - c_2 p_2 = \pm 1$ ($c_i \le m$, $p_i \notin \widetilde{\mathcal{P}}_m$) inside each wide window $[b / 2.441, b - 1]$ suffices — guaranteeing a solution to this **binary** linear prime equation for every large $b$ runs directly into the classical Selberg parity barrier (the same fundamental obstacle behind Twin Primes, Sophie Germain primes, and binary Goldbach).

## 3. Impossibility of Closing the Interior via Small Primes Alone (Route B — Theorem B.3)
We tested whether full-carry $p$-adic congruences $\bmod\, p^R$ for small primes ($p \le P_0$) combined with `gap <= 2` and harmonic sum bounds could refute central intervals without large primes. **We refuted this route in two independent ways:**

1. **Analytical proof (Theorem B.3 in [docs/ROUTE_B_ANALYSIS.md](docs/ROUTE_B_ANALYSIS.md)):** Near the center of the window ($a \approx b / 4.5$), there are $\Theta(b)$ odd variables coprime to all $p \le P_0$ (yielding $2^{\Theta(b)}$ subsets), whereas all congruences $\bmod\, p^{R_p}$ combined have only polynomial order $b^{\pi(P_0)}$. This produces exponentially many pseudo-solutions satisfying `gap <= 2`, $v_p(\sum 1/x) \ge 0$ for every $p \le P_0$, and $\left|\sum_{x \in S} \frac{1}{x} - 1\right| \le e^{-c_{P_0} b}$.
2. **Constructive SAT evidence (`M1`):** For $p \le 13$, our solver [sat_m1.rs](rust-verifier/src/sat_m1.rs) found **58 explicit pseudo-solutions** already for $b \le 300$ — for instance, on $[18, 80]$, a 42-element subset with no two consecutive omitted integers, exact $v_p \ge 0$ for all $p \in \{2, 3, 5, 7, 11, 13\}$, and sum $\approx 1.000003755$.

## 4. Summary of Tested Routes

| Route | Verdict | Reason |
| :--- | :---: | :--- |
| Isolated prime powers in $(b/2, b]$ (`M2`) | **Discarded** | 71.6% of candidate intervals up to $b = 6\,000$ survive |
| Small primes $p \le P_0$ with full carry (`M1`) | **Discarded (Theorem B.3)** | Constructive pseudo-solutions exist in the middle of the window ($a \approx b/4.5$) |
| Collisions $c_1 p_1 - c_2 p_2 = \pm 1$ in wide windows (`M3`) | **Conditional (`LinearPrimeCollisionHyp`)** | Empirically covers $100\%$ up to $10^8$, but requires overcoming the parity barrier |

# Erdős Problem #287 — Main Proposition

**Language:** **English** · [Português](pt/README.md)

**Tabs:** [Home](../../README.md) · **Proposition** · [State of the Art](STATUS.md) · [Contribution](CONTRIBUTION.md) · [Computational](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · [Barriers](BARRIERS.md) · [Collaborate](OPEN_QUESTIONS.md)

---

> **Honest status:** The general conjecture remains **open**. This directory provides unconditional partial results, an exact computational verification up to $b \le 10^8$, a Lean 4 formalization of the full conditional reduction (without needing Sophie Germain primes), and a rigorous analysis of the barriers preventing an unconditional closure.

## 1. Official Statement (Erdős & Graham, 1980)

Primary source: Paul Erdős & Ronald L. Graham, *Old and New Problems and Results in Combinatorial Number Theory* (1980), pp. 33–35; catalogued at [erdosproblems.com/287](https://www.erdosproblems.com/287).

> **Conjecture (Erdős #287):** For every integer $k \ge 2$ and any distinct integers $2 \le n_1 < n_2 < \dots < n_k$ such that
> $$\sum_{i=1}^{k} \frac{1}{n_i} = 1,$$
> one must have
> $$\max_{1 \le i < k} (n_{i+1} - n_i) \ge 3.$$

## 2. Sharpness of the Constant $3$

The bound $3$ is **best possible** (formally verified as `erdos_287_sharp_2_3_6` in [Defs.lean](lean/Erdos287/Defs.lean)):
$$\frac{1}{2} + \frac{1}{3} + \frac{1}{6} = 1, \qquad (n_1, n_2, n_3) = (2, 3, 6),$$
with consecutive gaps $3 - 2 = 1$ and $6 - 3 = 3$, achieving $\max_i (n_{i+1} - n_i) = 3$.

## 3. Equivalent Formulation by Contradiction

We prove formally in Lean 4 (`erdos_287_iff_no_candidate_set`) that Erdős #287 is equivalent to:

> **Interval–Path Formulation:** There exist no integers $2 \le a < b$ and no subset $S \subseteq [a, b]$ with $a, b \in S$ such that:
> 1. $T = [a, b] \setminus S$ is an independent set of the path $[a, b]$ (no two consecutive integers are omitted: $\forall x \in [a, b - 1],\; x \in S \lor x + 1 \in S$);
> 2. $\sum_{x \in S} \frac{1}{x} = 1$.

## 4. Quick Summary Across the 3 Layers

| Layer | What Has Been Established | Reference |
| :--- | :--- | :--- |
| **Theory (Paper)** | Exact harmonic window $\frac{b+1}{e^2} < a < \frac{b}{e} + 1$, unconditional boundary shrinking (Theorems B.1–B.2), and impossibility of closing the interior with small primes (Theorem B.3). | [Contribution](CONTRIBUTION.md) · [Barriers](BARRIERS.md) |
| **Computational (Rust `u128`)** | $0$ counterexamples for all $b \le 10^8$ in exact interval arithmetic (`0.61s`); ablation without Sophie Germain covering $87 \le b \le 10^7$; 58 SAT pseudo-solutions for $p \le 13$. | [Computational](COMPUTATIONAL.md) |
| **Formalization (Lean 4)** | Zero `sorry`, zero `native_decide`: unconditional $\max\text{-gap} \ge 2$, general $p$-adic engine, unconditional certificate up to $b \le 20\,000$, and reduction to `LinearPrimeCollisionHyp 20000`. | [Lean 4](LEAN.md) |

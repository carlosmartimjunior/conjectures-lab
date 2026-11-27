# Erdős #287 — Next Steps & How to Collaborate

**Language:** **English** · [Português](pt/OPEN_QUESTIONS.md)

**Tabs:** [Home](../../README.md) · [Proposition](README.md) · [State of the Art](STATUS.md) · [Contribution](CONTRIBUTION.md) · [Computational](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · [Barriers](BARRIERS.md) · **Collaborate**

---

Progress on any of the three fronts below plugs directly into the verified infrastructure already in this repository:

1. **Discharge `LinearPrimeCollisionHyp 20000` (or an asymptotic density-1 version):**
   - In [ConditionalReduction.lean](lean/Erdos287/ConditionalReduction.lean), the entire bridge to `Erdos287Conjecture` is already formalized with zero `sorry`.
   - Even an unconditional analytic proof that the set of exceptional scales $b$ lacking a collision in $[b / 2.441, b - 1]$ has **asymptotic density zero** (via circle-method / dyadic averaging) would be a genuine new unconditional result on Erdős #287.

2. **Global obstructions bypassing adjacent pairs $c_1 p_1, c_2 p_2$:**
   - Since Theorem B.3 rules out small primes alone, any unconditional proof bypassing the parity barrier must couple large primes $p(b) \to \infty$ globally with $\sum_{x \in S} \frac{1}{x} = 1$ (e.g., adapting Croot's 2001 exponential-sum framework to `gap <= 2`).

3. **Extend the Lean 4 finite certificate:**
   - Currently [FiniteCertificate.lean](lean/Erdos287/FiniteCertificate.lean) proves $b \le 20\,000$ via 13 witness pairs. Because coverage grows geometrically by $\approx 2.44\times$ per witness, adding ~10 extra witnesses (with primality certified by Pratt/Pocklington certificates without `native_decide`) would extend the formal Lean 4 certificate from $20\,000$ to $b \le 10^8$.

Contributions, mathematical audits, and pull requests are very welcome — provided they adhere to our [Rigor & Methodology](../../METHODOLOGY.md).

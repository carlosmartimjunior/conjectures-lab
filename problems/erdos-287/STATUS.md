# Erdős #287 — State of the Art

**Language:** **English** · [Português](pt/STATUS.md)

**Tabs:** [Home](../../README.md) · [Proposition](README.md) · **State of the Art** · [Contribution](CONTRIBUTION.md) · [Computational](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · [Barriers](BARRIERS.md) · [Collaborate](OPEN_QUESTIONS.md)

---

## 1. Known Classical & Modern Results

- **The $\max(n_{i+1} - n_i) \ge 2$ case (classical):**
  - **Theisinger (1915):** $H_n = \sum_{x=1}^n \frac{1}{x} \notin \mathbb{Z}$ for all $n \ge 2$.
  - **Kürschák (1918):** No nontrivial block $[a, b]$ ($1 \le a < b$) of consecutive integers has an integer reciprocal sum, proved via the unique multiple of the highest power of $2$ in $[a, b]$. *(Formally verified in [GapAtLeastTwo.lean](lean/Erdos287/GapAtLeastTwo.lean)).*
  - **Erdős (1932) / Shorey–Tijdeman (1990):** Extensions to arithmetic progressions $\sum_{j=0}^{k-1} \frac{1}{a + jd} \notin \mathbb{Z}$.

- **The structural tension with Erdős #286 (Croot, 2001):**
  - **Ernest S. Croot III (2001)** (*Acta Arith.* 99, 99–114) resolved Erdős #286 affirmatively, proving that for sufficiently large $N$ there exists $S \subseteq [N, (e + o(1))N]$ with $\sum_{x \in S} \frac{1}{x} = 1$.
  - **Why this does not refute #287:** Croot restricts $S$ to **$y$-smooth integers** ($P^+(x) \le N^\theta$). Integers with large prime factors fall into $T = [a, b] \setminus S$ and form arbitrarily long consecutive runs, forcing $\max(n_{i+1} - n_i) \to \infty$.

- **$p$-adic valuations of harmonic sums:**
  - Eswarathasan & Levine (1991), Boyd (1994), and Sanna (2016) studied prime divisors of numerators of $H_n$. In our attack on #287, we analyze all $2^m - 1$ nonempty subsets of $\{1, \frac{1}{2}, \dots, \frac{1}{m}\}$, defining the finite exceptional prime sets $\mathcal{P}_m$.

- **Formal benchmark:**
  - The conjecture is tracked as an open research problem in `FormalConjectures/ErdosProblems/287.lean`.

For the full literature review and detailed proofs of the base lemmas (currently written in Portuguese), see [docs/LITERATURE_AND_LEMMAS.md](docs/LITERATURE_AND_LEMMAS.md).

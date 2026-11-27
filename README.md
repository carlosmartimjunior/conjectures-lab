# Conjectures Lab

> **An open research notebook combining mathematical analysis, exact computational verification (Rust `u128` / SAT), and Lean 4 formalizations for open mathematical conjectures.**

**Language:** **English** · [Português](pt/README.md)

**Navigation:** [Home](README.md) · [Rigor & Methodology](METHODOLOGY.md) · [Erdős #287](problems/erdos-287/README.md)

---

## Purpose

This repository documents real attempts to investigate and prove open mathematical conjectures — **without hiding dead ends, without mislabeling conditional reductions as unconditional proofs, and without hidden `sorry`s**.

For every conjecture investigated, we strictly separate results into **three layers**:
1. **On Paper (Theory):** unconditional lemmas, explicit conditional reductions, and honest analyses of the barriers encountered.
2. **Computational (Reproducible):** exact-arithmetic verifiers (zero floating point in exclusion proofs) and ablation / SAT experiments.
3. **Formalization (Lean 4):** machine-checked theorems verified by the Lean 4 kernel with zero `sorry`, zero custom axioms, and zero `native_decide`.

---

## Problem Catalogue

| Problem | Global Status | Theory (Paper) | Computational Verification | Formalization (Lean 4) | Page |
| :--- | :---: | :--- | :--- | :--- | :--- |
| **Erdős #287** *(Egyptian fractions with gaps $\le 2$)* | **Open** *(Conditional reduction + partial results)* | Exact window $\frac{b+1}{e^2} < a < \frac{b}{e}+1$, unconditional boundary shrinking (B.1–B.2), small-prime impossibility (B.3), and `LinearPrimeCollisionHyp` reduction | $0$ counterexamples for all $b \le 10^8$ in Rust (exact `u128`, `0.61s`) + ablation & 58 SAT pseudo-solutions (`M1`) | **100% kernel-verified (Plan B):** equivalence, sharpness $\{2,3,6\}$, $\max\text{-gap} \ge 2$, general $p$-adic engine, certificate up to $b \le 20\,000$, and conditional reduction | [Open Erdős #287](problems/erdos-287/README.md) |

---

## Standard Structure for Each Problem

Every folder under `problems/<slug>/` follows the same 7 pure-Markdown tabs (in English, with a Portuguese mirror under `pt/`):
1. **`README.md`** — Main proposition, equivalences, and sharp examples.
2. **`STATUS.md`** — Literature state of the art prior to our investigation.
3. **`CONTRIBUTION.md`** — Our contribution (unconditional partial theorems and conditional reductions).
4. **`COMPUTATIONAL.md`** — Computational lab and reproduction commands.
5. **`LEAN.md`** — Lean 4 module DAG and `#print axioms` audit.
6. **`BARRIERS.md`** — Why we did not close the full proof (barriers and discarded routes).
7. **`OPEN_QUESTIONS.md`** — What remains open and how to collaborate.

---

## License

Code and documentation are released under the [MIT License](LICENSE).

# Erdős #287 — Lean 4 Formalization & Axiom Audit

**Language:** **English** · [Português](pt/LEAN.md)

**Tabs:** [Home](../../README.md) · [Proposition](README.md) · [State of the Art](STATUS.md) · [Contribution](CONTRIBUTION.md) · [Computational](COMPUTATIONAL.md) · **Lean 4** · [Barriers](BARRIERS.md) · [Collaborate](OPEN_QUESTIONS.md)

---

The complete Plan B formalization resides in [lean/](lean/), built on **Lean 4 (`v4.35.0`) + Mathlib**, strictly adhering to:
- **Zero `sorry`**
- **Zero custom axioms**
- **Zero `native_decide`** (`Lean.ofReduceBool` is absent from the entire proof chain)

## 1. Modular Architecture (DAG)

```
Defs.lean
  └── PadicObstruction.lean
        ├── GapAtLeastTwo.lean
        └── FiniteCertificate.lean
              └── ConditionalReduction.lean
                    └── Main.lean (#print axioms audit)
```

| Module | Main Contents | Status |
| :--- | :--- | :---: |
| [Defs.lean](lean/Erdos287/Defs.lean) | Literal statement matching `FormalConjectures/ErdosProblems/287.lean`, equivalence `erdos_287_iff_no_candidate_set`, and sharpness witness `erdos_287_sharp_2_3_6`. | Verified |
| [PadicObstruction.lean](lean/Erdos287/PadicObstruction.lean) | Elementary `Finset.lcm` criteria in `ℕ`/`ℚ`: `not_mem_of_unique_prime_pow_dvd`, `prime_pow_gt_half_not_mem`, `NoZeroSubsetMod`, `multiples_not_mem_of_no_zero_subset_mod`, and `not_candidateSet_of_forbidden_mul_pair`. | Verified |
| [GapAtLeastTwo.lean](lean/Erdos287/GapAtLeastTwo.lean) | Complete unconditional proof of `erdos_287_gap_at_least_two` ($\max_i(n_{i+1}-n_i) \ge 2$, Kürschák 1918). | Verified |
| [FiniteCertificate.lean](lean/Erdos287/FiniteCertificate.lean) | Pure-rational 4-block lemma (`coverHi4`, zero `Real.log`) + unconditional certificate `erdos_287_upto_20000` covering all $b \le 20\,000$ via 13 witness pairs. | Verified |
| [ConditionalReduction.lean](lean/Erdos287/ConditionalReduction.lean) | Explicit definition of `LinearPrimeCollisionHyp` and reduction theorem `erdos_287_of_linear_prime_collision_hyp`. | Verified |
| [Main.lean](lean/Erdos287/Main.lean) | Entry point and `#print axioms` audit for all 5 exported theorems. | Verified |

## 2. Axiom Audit Output (`lake build Erdos287`)

```text
'Erdos287.erdos_287_iff_no_candidate_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.erdos_287_sharp_2_3_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.erdos_287_gap_at_least_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.erdos_287_upto_20000' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.erdos_287_of_linear_prime_collision_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. How to Reproduce Locally

```bash
cd problems/erdos-287/lean
lake exe cache get
lake build Erdos287
```

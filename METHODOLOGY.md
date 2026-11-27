# Rigor & Scientific Honesty Standards

**Language:** **English** · [Português](pt/METHODOLOGY.md)

**Navigation:** [Home](README.md) · **Rigor & Methodology** · [Erdős #287](problems/erdos-287/README.md)

---

This repository enforces five non-negotiable standards so that anyone using this material knows **precisely** what is proved and what remains open:

1. **Strict separation between unconditional proofs, conditional reductions, and finite computation:**
   - A conditional reduction (*if hypothesis $H$ holds, then the conjecture holds*) is **never** labeled as a full proof of the conjecture.
   - A finite computational search (even up to $10^8$) proves only the tested finite range — never the universal statement $\forall n$.

2. **Exact arithmetic in computational verifiers:**
   - No candidate interval is eliminated using floating-point tolerances (`f64`). All sum-based eliminations use exact integer interval arithmetic (e.g., fixed-point `u128` lower/upper bounds) or purely rational/integer criteria.

3. **Strict Lean 4 kernel audit:**
   - Every published Lean 4 module compiles with **zero `sorry`**, **zero custom `axiom`**, and **zero `native_decide`** (`Lean.ofReduceBool` is strictly forbidden).
   - The only permitted transitive axioms in `#print axioms` are the three standard Lean/Mathlib axioms: `propext`, `Classical.choice`, and `Quot.sound`.

4. **Transparent reporting of barriers and discarded routes:**
   - Whenever an attack hits a fundamental open barrier (such as the Selberg parity barrier or local-global pseudo-solutions), we document the barrier proof explicitly in `BARRIERS.md` to save time for future researchers.

5. **Full reproducibility:**
   - All JSON certificates, SAT/SMT instances, Rust verifier source code, and portable Lean 4 files are versioned alongside exact commands to rebuild and re-verify everything from scratch.

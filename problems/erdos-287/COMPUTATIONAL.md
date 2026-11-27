# Erdős #287 — Computational Lab (Rust `u128` + SAT/SMT)

**Language:** **English** · [Português](pt/COMPUTATIONAL.md)

**Tabs:** [Home](../../README.md) · [Proposition](README.md) · [State of the Art](STATUS.md) · [Contribution](CONTRIBUTION.md) · **Computational** · [Lean 4](LEAN.md) · [Barriers](BARRIERS.md) · [Collaborate](OPEN_QUESTIONS.md)

---

The entire computational engine lives in [rust-verifier/](rust-verifier/) (pure Rust with `rayon` and exact `u128` fixed-point interval arithmetic at scale $2^{96}$, **zero `f64`** in exclusion proofs).

## 1. Verified Results

| Experiment | Scope | Exact Result | Certificate |
| :--- | :--- | :--- | :--- |
| **Sanity Checks** | $\{2,3,6\}$, $\{2,4,6,12\}$, $\{2,3,7,42\}$ without `gap <= 2` | **100% survive** (no false positives in `u128` propagator or `sat-m1` solver) | Unit tests (`cargo test`) |
| **Exact Baseline Concordance** | All candidate intervals with $b \le 2\,000$ | **464,286** intervals tested, **`0` survivors** (`0.21s`) | Unit tests |
| **Exhaustive Verification up to $10^8$** | All $4 \le b \le 100\,000\,000$ | **`0` survivors** in **`0.61s`**: **16 universal pairs** (64 rational blocks) cover $68 \le b \le 10^8$; $4 \le b \le 67$ ($496$ intervals) eliminated by `u128` propagation | [verify_100m_summary.json](certificates/verify_100m_summary.json) |
| **Ablation `M1` ($p \le 13$ only)** | $b \le 6\,000$ (`4,183,383` intervals) | **4,117,211 survivors** ($98.4\%$) — confirms small primes are insufficient | [ablation_report.json](certificates/ablation_report.json) |
| **Ablation `M2` ($p^r > b/2$ only)** | $b \le 6\,000$ (`4,183,383` intervals) | **2,994,529 survivors** ($71.6\%$) | [ablation_report.json](certificates/ablation_report.json) |
| **Ablation `M3` (NO Sophie Germain)** | $b \le 10^7$, forbidding $(c_1, c_2) \in \{(1,2),(2,1)\}$ | **Contiguous universal cover from $b = 87$ to $10^7$** | [ablation_report.json](certificates/ablation_report.json) |
| **Ablation `M4` (Full engine)** | $b \le 6\,000$ (`4,183,383` intervals) | **`0` survivors** | [ablation_report.json](certificates/ablation_report.json) |
| **SAT Solver `M1` (full carry $\bmod\, p^R$)** | $p \le 13$, tolerance $10^{-5}$ ($1,143$ intervals) | **58 explicit pseudo-solutions found** (e.g., $42$ elements in $[18, 80]$ summing to $\approx 1.000003755$) | [ablation_report.json](certificates/ablation_report.json) · [.smt2](certificates/m1_instance_46_180.smt2) · [.cnf](certificates/m1_instance_46_180.cnf) |

## 2. How to Reproduce from Scratch

```bash
cd problems/erdos-287/rust-verifier
cargo test --release
cargo run --release -- verify-100m --max-b 100000000
cargo run --release -- ablation --max-b 6000 --max-b-m3 10000000
cargo run --release -- sat-m1 --b 180 --max-p 13
cargo run --release -- export-lean-cert --max-b 20000 --max-m 6
```

*(Windows note for `x86_64-pc-windows-gnu`: if your workspace path contains non-ASCII characters, point `CARGO_TARGET_DIR` to an ASCII path before running `cargo`.)*

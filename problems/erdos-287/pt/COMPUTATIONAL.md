# Erdős #287 — Laboratório Computacional (Rust `u128` + SAT/SMT)

**Idioma:** [English](../COMPUTATIONAL.md) � **Portugu�s**

**Abas:** [Início](../../../pt/README.md) · [Proposição](README.md) · [Estado da Arte](STATUS.md) · [Contribuição](CONTRIBUTION.md) · **Computacional** · [Lean 4](LEAN.md) · [Barreiras](BARRIERS.md) · [Como Colaborar](OPEN_QUESTIONS.md)

---

Todo o motor computacional reside em [rust-verifier/](../rust-verifier/) (Rust puro com `rayon` e aritmética intervalar inteira exata em `u128` na escala $2^{96}$, **zero `f64`** nas provas de eliminação).

## 1. Resultados Verificados

| Experimento | Escopo | Resultado Exato | Certificado |
| :--- | :--- | :--- | :--- |
| **Sanity Checks** | $\{2,3,6\}$, $\{2,4,6,12\}$, $\{2,3,7,42\}$ sem `gap <= 2` | **100% sobrevivem** (ausência de falsos positivos no propagador `u128` e no solver `sat-m1`) | Testes unitários (`cargo test`) |
| **Concordância Exata** | Todos os intervalos candidatos com $b \le 2\,000$ | **464.286** intervalos testados, **`0` sobreviventes** (`0,21s`) | Testes unitários |
| **Varredura Exaustiva até $10^8$** | Todo $4 \le b \le 100\,000\,000$ | **`0` sobreviventes** em **`0,61s`**: **16 pares universais** (64 blocos racionais) cobrem $68 \le b \le 10^8$; $4 \le b \le 67$ ($496$ intervalos) eliminados por propagação `u128` | [verify_100m_summary.json](../certificates/verify_100m_summary.json) |
| **Ablação `M1` (só $p \le 13$)** | $b \le 6\,000$ (`4.183.383` intervalos) | **4.117.211 sobreviventes** ($98{,}4\%$) — confirma que primos pequenos não bastam | [ablation_report.json](../certificates/ablation_report.json) |
| **Ablação `M2` (só $p^r > b/2$)** | $b \le 6\,000$ (`4.183.383` intervalos) | **2.994.529 sobreviventes** ($71{,}6\%$) | [ablation_report.json](../certificates/ablation_report.json) |
| **Ablação `M3` (SEM Sophie Germain)** | $b \le 10^7$, proibindo $(c_1, c_2) \in \{(1,2),(2,1)\}$ | **Cobertura universal contígua a partir de $b = 87$ até $10^7$** | [ablation_report.json](../certificates/ablation_report.json) |
| **Ablação `M4` (Motor completo)** | $b \le 6\,000$ (`4.183.383` intervalos) | **`0` sobreviventes** | [ablation_report.json](../certificates/ablation_report.json) |
| **Solver SAT `M1` (*carry* completo $\bmod\, p^R$)** | $p \le 13$, tolerância $10^{-5}$ ($1.143$ intervalos) | **58 pseudo-soluções explícitas encontradas** (ex.: $42$ elementos em $[18, 80]$ com soma $\approx 1{,}000003755$) | [ablation_report.json](../certificates/ablation_report.json) · [.smt2](../certificates/m1_instance_46_180.smt2) · [.cnf](../certificates/m1_instance_46_180.cnf) |

## 2. Como Reproduzir do Zero

```bash
cd problems/erdos-287/rust-verifier
cargo test --release
cargo run --release -- verify-100m --max-b 100000000
cargo run --release -- ablation --max-b 6000 --max-b-m3 10000000
cargo run --release -- sat-m1 --b 180 --max-p 13
cargo run --release -- export-lean-cert --max-b 20000 --max-m 6
```

*(Nota no Windows com toolchain `x86_64-pc-windows-gnu`: se o caminho do repositório contiver caracteres acentuados, defina `CARGO_TARGET_DIR` para um caminho ASCII antes de rodar `cargo`.)*

# Erdős #287 — Formalização em Lean 4 e Auditoria de Axiomas

**Idioma:** [English](../LEAN.md) � **Portugu�s**

**Abas:** [Início](../../../pt/README.md) · [Proposição](README.md) · [Estado da Arte](STATUS.md) · [Contribuição](CONTRIBUTION.md) · [Computacional](COMPUTATIONAL.md) · **Lean 4** · [Barreiras](BARRIERS.md) · [Como Colaborar](OPEN_QUESTIONS.md)

---

A formalização completa do Plano B encontra-se em [lean/](../lean/), construída em **Lean 4 (`v4.35.0`) + Mathlib**, respeitando estritamente:
- **Zero `sorry`**
- **Zero axiomas customizados**
- **Zero `native_decide`** (`Lean.ofReduceBool` ausente de toda a cadeia)

## 1. Arquitetura Modular (DAG)

```
Defs.lean
  └── PadicObstruction.lean
        ├── GapAtLeastTwo.lean
        └── FiniteCertificate.lean
              └── ConditionalReduction.lean
                    └── Main.lean (auditoria #print axioms)
```

| Módulo | Conteúdo Principal | Status |
| :--- | :--- | :---: |
| [Defs.lean](../lean/Erdos287/Defs.lean) | Enunciado literal compatível com `FormalConjectures/ErdosProblems/287.lean`, equivalência `erdos_287_iff_no_candidate_set` e nitidez `erdos_287_sharp_2_3_6`. | Verificado |
| [PadicObstruction.lean](../lean/Erdos287/PadicObstruction.lean) | Critérios elementares via `Finset.lcm` em `ℕ`/`ℚ`: `not_mem_of_unique_prime_pow_dvd`, `prime_pow_gt_half_not_mem`, `NoZeroSubsetMod`, `multiples_not_mem_of_no_zero_subset_mod` e `not_candidateSet_of_forbidden_mul_pair`. | Verificado |
| [GapAtLeastTwo.lean](../lean/Erdos287/GapAtLeastTwo.lean) | Prova incondicional completa de `erdos_287_gap_at_least_two` ($\max_i(n_{i+1}-n_i) \ge 2$, Kürschák 1918). | Verificado |
| [FiniteCertificate.lean](../lean/Erdos287/FiniteCertificate.lean) | Lema racional puro de 4 blocos (`coverHi4`, sem `Real.log`) + certificado incondicional `erdos_287_upto_20000` cobrindo todo $b \le 20\,000$ com 13 pares testemunhas. | Verificado |
| [ConditionalReduction.lean](../lean/Erdos287/ConditionalReduction.lean) | Definição explícita de `LinearPrimeCollisionHyp` e teorema `erdos_287_of_linear_prime_collision_hyp`. | Verificado |
| [Main.lean](../lean/Erdos287/Main.lean) | Ponto de entrada e auditoria de axiomas dos 5 teoremas exportados. | Verificado |

## 2. Saída da Auditoria de Axiomas (`lake build Erdos287`)

```text
'Erdos287.erdos_287_iff_no_candidate_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.erdos_287_sharp_2_3_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.erdos_287_gap_at_least_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.erdos_287_upto_20000' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.erdos_287_of_linear_prime_collision_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Como Reproduzir Localmente

```bash
cd problems/erdos-287/lean
lake exe cache get
lake build Erdos287
```

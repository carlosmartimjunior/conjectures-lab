# Erdős Problem #287 — Proposição Principal

**Idioma:** [English](../README.md) � **Portugu�s**

**Abas:** [Início](../../../pt/README.md) · **Proposição** · [Estado da Arte](STATUS.md) · [Contribuição](CONTRIBUTION.md) · [Computacional](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · [Barreiras](BARRIERS.md) · [Como Colaborar](OPEN_QUESTIONS.md)

---

> **Status honesto:** A conjectura geral permanece **em aberto**. Este diretório contém resultados parciais incondicionais, uma verificação computacional exata até $b \le 10^8$, uma redução condicional formalizada em Lean 4 (sem depender de primos de Sophie Germain) e a análise rigorosa das barreiras que impedem o fechamento incondicional completo.

## 1. Enunciado Oficial (Erdős & Graham, 1980)

Fonte primária: Paul Erdős & Ronald L. Graham, *Old and New Problems and Results in Combinatorial Number Theory* (1980), p. 33–35; catálogo [erdosproblems.com/287](https://www.erdosproblems.com/287).

> **Conjectura (Erdős #287):** Para todo inteiro $k \ge 2$ e quaisquer inteiros distintos $2 \le n_1 < n_2 < \dots < n_k$ tais que
> $$\sum_{i=1}^{k} \frac{1}{n_i} = 1,$$
> vale necessariamente
> $$\max_{1 \le i < k} (n_{i+1} - n_i) \ge 3.$$

## 2. Nitidez da Constante $3$

A cota $3$ é **melhor possível** (formalizada em `erdos_287_sharp_2_3_6` em [Defs.lean](../lean/Erdos287/Defs.lean)):
$$\frac{1}{2} + \frac{1}{3} + \frac{1}{6} = 1, \qquad (n_1, n_2, n_3) = (2, 3, 6),$$
cujos saltos consecutivos são $3 - 2 = 1$ e $6 - 3 = 3$, atingindo exatamente $\max_i (n_{i+1} - n_i) = 3$.

## 3. Formulação Equivalente por Contradição

Provamos formalmente em Lean 4 (`erdos_287_iff_no_candidate_set`) que Erdős #287 equivale a:

> **Formulação Caminho–Intervalo:** Não existem inteiros $2 \le a < b$ nem subconjunto $S \subseteq [a, b]$ com $a, b \in S$ tais que:
> 1. $T = [a, b] \setminus S$ é um conjunto independente do caminho $[a, b]$ (não há dois inteiros consecutivos omitidos: $\forall x \in [a, b - 1],\; x \in S \lor x + 1 \in S$);
> 2. $\sum_{x \in S} \frac{1}{x} = 1$.

## 4. Resumo Rápido das 3 Camadas

| Camada | O que foi estabelecido | Referência |
| :--- | :--- | :--- |
| **Teoria (Papel)** | Janela harmônica exata $\frac{b+1}{e^2} < a < \frac{b}{e} + 1$, estreitamento incondicional das bordas (Teoremas B.1–B.2) e impossibilidade de fechar o centro com primos pequenos (Teorema B.3). | [Contribuição](CONTRIBUTION.md) · [Barreiras](BARRIERS.md) |
| **Computacional (Rust `u128`)** | $0$ contraexemplos para todo $b \le 10^8$ em aritmética intervalar exata (`0,61s`); ablação sem Sophie Germain cobrindo $87 \le b \le 10^7$; 58 pseudo-soluções SAT para $p \le 13$. | [Computacional](COMPUTATIONAL.md) |
| **Formalização (Lean 4)** | Zero `sorry`, zero `native_decide`: $\max\text{-gap} \ge 2$ incondicional, motor $p$-ádico geral, certificado incondicional até $b \le 20\,000$ e redução a `LinearPrimeCollisionHyp 20000`. | [Lean 4](LEAN.md) |

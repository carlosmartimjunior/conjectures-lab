# Conjectures Lab

> **Laboratório aberto de pesquisa, experimentação computacional e formalização em Lean 4 sobre conjecturas matemáticas em aberto.**

**Navegação:** [Início](README.md) · [Padrão de Rigor](METHODOLOGY.md) · [Erdős #287](../problems/erdos-287/pt/README.md)

---

## Propósito

Este repositório documenta tentativas reais de atacar conjecturas matemáticas em aberto — **sem esconder falhas, sem mascarar resultados condicionais como provas completas e sem `sorry` oculto**.

Para cada conjectura investigada, mantemos uma separação explícita em **três camadas**:
1. **No papel (Teoria):** lemas incondicionais, reduções condicionais explícitas e análise honesta das barreiras encontradas.
2. **Computacional (Reprodutível):** verificadores em aritmética exata (sem ponto flutuante) e experimentos de ablação / SAT.
3. **Formalização (Lean 4):** teoremas verificados pelo kernel do Lean 4 com zero `sorry`, zero axiomas customizados e zero `native_decide`.

---

## Catálogo de Problemas

| Problema | Status Global | Teoria (Papel) | Verificação Computacional | Formalização (Lean 4) | Página |
| :--- | :---: | :--- | :--- | :--- | :--- |
| **Erdős #287** *(Frações egípcias com gaps $\le 2$)* | **Em aberto** *(Redução condicional + parciais)* | Janela exata $\frac{b+1}{e^2} < a < \frac{b}{e}+1$, estreitamento das bordas (B.1–B.2), impossibilidade de primos pequenos (B.3) e redução `LinearPrimeCollisionHyp` | $0$ contraexemplos para todo $b \le 10^8$ em Rust (`u128` exato, `0,61s`) + ablação e 58 pseudo-soluções SAT (`M1`) | **100% verificado (Plano B):** equivalência, nitidez $\{2,3,6\}$, $\max\text{-gap} \ge 2$, motor $p$-ádico, certificado até $b \le 20\,000$ e redução condicional | [Abrir Erdős #287](../problems/erdos-287/pt/README.md) |

---

## Estrutura Padrão de Cada Problema

Cada pasta em `problems/<slug>/` segue as mesmas 7 abas em Markdown puro:
1. **`README.md`** — Proposição principal, equivalências e exemplo agudo.
2. **`STATUS.md`** — O que já existe na literatura antes da nossa investigação.
3. **`CONTRIBUTION.md`** — Nossa contribuição (teoremas parciais incondicionais e redução condicional).
4. **`COMPUTATIONAL.md`** — Laboratório computacional e instruções de reprodução.
5. **`LEAN.md`** — Mapa dos módulos em Lean 4 e auditoria de `#print axioms`.
6. **`BARRIERS.md`** — Por que não fechamos a prova completa (barreiras e rotas descartadas).
7. **`OPEN_QUESTIONS.md`** — O que falta destravar e como colaborar.

---

## Licença

Código e documentação distribuídos sob licença [MIT](../LICENSE).

# Erdős #287 — Estado da Arte ("O Que Temos Até Agora")

**Idioma:** [English](../STATUS.md) � **Portugu�s**

**Abas:** [Início](../../../pt/README.md) · [Proposição](README.md) · **Estado da Arte** · [Contribuição](CONTRIBUTION.md) · [Computacional](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · [Barreiras](BARRIERS.md) · [Como Colaborar](OPEN_QUESTIONS.md)

---

## 1. Resultados Clássicos Já Conhecidos

- **Caso $\max(n_{i+1} - n_i) \ge 2$ (resolvido há mais de um século):**
  - **Theisinger (1915):** $H_n = \sum_{x=1}^n \frac{1}{x} \notin \mathbb{Z}$ para todo $n \ge 2$.
  - **Kürschák (1918):** Nenhum bloco não-trivial $[a, b]$ ($1 \le a < b$) de inteiros consecutivos tem soma de recíprocos inteira. A prova usa a unicidade do múltiplo da maior potência de $2$ em $[a, b]$. *(Formalizado em [GapAtLeastTwo.lean](../lean/Erdos287/GapAtLeastTwo.lean)).*
  - **Erdős (1932) / Shorey–Tijdeman (1990):** Generalizações para progressões aritméticas $\sum_{j=0}^{k-1} \frac{1}{a + jd} \notin \mathbb{Z}$.

- **O contraste fundamental com Erdős #286 (Croot, 2001):**
  - **Ernest S. Croot III (2001)** (*Acta Arith.* 99, 99–114) resolveu afirmativamente Erdős #286, provando que existe $S \subseteq [N, (e + o(1))N]$ com $\sum_{x \in S} \frac{1}{x} = 1$.
  - **Por que isso não refuta #287:** Croot restringe $S$ a inteiros **$y$-suaves** ($P^+(x) \le N^\theta$). Os inteiros com fatores primos grandes ficam todos no complementar $T = [a, b] \setminus S$ e formam blocos consecutivos arbitrariamente longos, gerando $\max(n_{i+1} - n_i) \to \infty$.

- **Valorações $p$-ádicas de somas harmônicas:**
  - Eswarathasan & Levine (1991), Boyd (1994) e Sanna (2016) estudaram divisores primos de numeradores de $H_n$. No nosso ataque a #287, o objeto relevante são todos os $2^m - 1$ subconjuntos não-vazios de $\{1, \frac{1}{2}, \dots, \frac{1}{m}\}$, que definem os conjuntos finitos $\mathcal{P}_m$.

- **Benchmark formal:**
  - O enunciado está catalogado como questão de pesquisa em aberto em `FormalConjectures/ErdosProblems/287.lean`.

Para a revisão bibliográfica completa com referências e demonstrações dos lemas clássicos, veja [docs/LITERATURE_AND_LEMMAS.md](../docs/LITERATURE_AND_LEMMAS.md).

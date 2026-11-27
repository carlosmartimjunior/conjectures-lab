# Erdős #287 — Nossa Contribuição (Resultados Parciais e Redução)

**Idioma:** [English](../CONTRIBUTION.md) � **Portugu�s**

**Abas:** [Início](../../../pt/README.md) · [Proposição](README.md) · [Estado da Arte](STATUS.md) · **Contribuição** · [Computacional](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · [Barreiras](BARRIERS.md) · [Como Colaborar](OPEN_QUESTIONS.md)

---

Sem resolver a conjectura em toda a sua generalidade, nossa investigação estabelece **cinco contribuições concretas** (separando estritamente o que é incondicional do que é condicional):

## 1. Janela Harmônica Exata e Lema Racional de $N$ Blocos (**Incondicional**)
Para **todo** terno candidato $(a, b, S)$ ($b \ge 4$), provamos sem termos assintóticos:
$$\frac{b + 1}{e^2} < a < \frac{b}{e} + 1.$$
Além disso, para certificados formais livres de `Real.log`, provamos em $\mathbb{Q}$ que $N v \le (N + 1) u \implies \sum_{y = u + 1}^v \frac{1}{y} < \frac{1}{N}$. Iterando $u \mapsto \lfloor 5 u / 4 \rfloor$ quatro vezes (`coverHi4 x` $\approx 2{,}441 x$), todo candidato com $b \le \mathrm{coverHi4}(x)$ satisfaz obrigatoriamente $a \le x$.

## 2. Refinamento Exponencial do Limiar $p$-ádico (**Incondicional**)
Em vez de exigir $p > m! H_m$, demonstramos que basta $p > m$, $b < (m + 1)p$ e $p \notin \widetilde{\mathcal{P}}_m$ (garantido em particular por $p > \operatorname{lcm}(1, \dots, m) H_m$) para excluir **todos** os múltiplos $c p$ de $S$. Isso eleva o alcance assintótico de $m(b)$ de $\sim \frac{\ln b}{\ln \ln b}$ para $\sim (1 - \varepsilon)\ln b$. Calculamos exatamente $\widetilde{\mathcal{P}}_m$ em `u128` até $m = 18$ ($D_{18} = 12\,252\,240$, $D_{18} H_{18} = 42\,822\,903$).

## 3. Estreitamento Incondicional das Duas Bordas da Janela (**Incondicional — Papel**)
Em [docs/ROUTE_B_ANALYSIS.md](../docs/ROUTE_B_ANALYSIS.md):
- **Teorema B.1 (Borda superior $a \approx b/e$):** Usando primos proibidos em $(b/2, b]$ e Dusart (2010), eliminamos incondicionalmente $a - 1 \ge \frac{b}{e} - \frac{0{,}20\, b}{\ln b}$ para $b \ge 20\,744$ (e $\Theta(\frac{b \ln \ln b}{\ln b})$ via $\mathcal{F}_1(b)$).
- **Teorema B.2 (Borda inferior $a \approx b/e^2$):** Provamos a identidade de carga por convexidade $H_b - H_{a-1} < 2 - \sum_{x \in S} \frac{2 - \nu_T(x)}{2x}$, mostrando que cada troca de paridade em $T$ entre primos ímpares $p \in (2b/3, b)$ e pares $2q$ ($q \in (b/3, b/2)$) gera penalidade $> \frac{1}{b}$, estreitando incondicionalmente a borda inferior em $\Omega(\ln^2 b)$.

## 4. Redução Condicional Fraca Sem Sophie Germain (**Condicional — Formalizada em Lean 4**)
Formalizamos `erdos_287_of_linear_prime_collision_hyp` ([ConditionalReduction.lean](../lean/Erdos287/ConditionalReduction.lean)): a conjectura completa decorre de `LinearPrimeCollisionHyp 20000`, que exige apenas **um único** par consecutivo proibido $(c_1 p_1, c_2 p_2)$ em cada janela multiplicativa larga $[b / 2{,}441,\; b - 1]$ — **estritamente mais fraca** que primos de Sophie Germain em intervalos curtos (e nossa ablação `M3` confirma cobertura contígua de $b = 87$ até $10^7$ mesmo proibindo completamente $(c_1, c_2) \in \{(1,2), (2,1)\}$).

## 5. Certificados Finitos Exatos (**Incondicional nos limites testados**)
- **Kernel do Lean 4 (zero `native_decide`):** `erdos_287_upto_20000` prova formalmente $\max\text{-gap} \ge 3$ para todo $b \le 20\,000$ com apenas **13 pares testemunhas**.
- **Motor Rust (`u128` exato):** $0$ contraexemplos para todo $4 \le b \le 10^8$ em `0,61s`.

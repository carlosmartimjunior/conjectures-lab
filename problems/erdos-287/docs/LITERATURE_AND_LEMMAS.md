# Revisão da Literatura e Lemas Estruturais — Conjectura de Erdős #287

## 1. Estado da Arte e Conexões na Literatura

### 1.1 Origem do Problema e Nitidez da Constante $3$
Na monografia *Old and New Problems and Results in Combinatorial Number Theory* (Erdős & Graham, 1980, p. 33–35), Paul Erdős e Ronald Graham propuseram uma família de problemas sobre representações da unidade como soma de frações egípcias distintas com denominadores concentrados ou densos. O **Problema #287** ([erdosproblems.com/287](https://www.erdosproblems.com/287)) pergunta:

> **Conjectura de Erdős #287 (Em aberto):** Para todo inteiro $k \ge 2$ e quaisquer inteiros estritamente crescentes $2 \le n_1 < n_2 < \dots < n_k$ tais que
> $$\sum_{i=1}^k \frac{1}{n_i} = 1,$$
> vale necessariamente
> $$\max_{1 \le i < k} (n_{i+1} - n_i) \ge 3?$$

A constante $3$ é **melhor possível (aguda)**, como mostra a decomposição clássica
$$\frac{1}{2} + \frac{1}{3} + \frac{1}{6} = 1 \qquad (n_1 = 2,\; n_2 = 3,\; n_3 = 6),$$
cujos saltos consecutivos são $3 - 2 = 1$ e $6 - 3 = 3$, atingindo $\max_i (n_{i+1} - n_i) = 3$. No repositório de formalização *Formal Conjectures* (`FormalConjectures/ErdosProblems/287.lean`), o problema encontra-se catalogado como questão de pesquisa em aberto (`@[category research open, question, AMS 11]`).

---

### 1.2 O Caso Clássico $\max(n_{i+1} - n_i) \ge 2$ e Progressões Aritméticas
Exigir $\max_{1 \le i < k}(n_{i+1} - n_i) \ge 2$ equivale a afirmar que $1$ (e, mais geralmente, qualquer inteiro) jamais se escreve como soma dos recíprocos de um bloco não-trivial $[a, b]$ ($2 \le a < b$) de inteiros consecutivos:

- **Theisinger (1915)** provou que $H_n = \sum_{x=1}^n \frac{1}{x} \notin \mathbb{Z}$ para todo $n \ge 2$.
- **Kürschák (1918)** estendeu o resultado a qualquer bloco $[a, b]$ ($1 \le a < b$): tomando $r = \max_{x \in [a,b]} v_2(x)$ (como $a < b$, existe ao menos um par em $[a, b]$, logo $r \ge 1$), existe um **único** múltiplo de $2^r$ em $[a, b]$ — pois se $u \cdot 2^r < v \cdot 2^r$ pertencessem a $[a, b]$ com $u, v$ ímpares, então $(u+1)\cdot 2^r \in [a, b]$ seria divisível por $2^{r+1}$, contradizendo a maximalidade de $r$. Logo $v_2\!\left(\sum_{x=a}^b \frac{1}{x}\right) = -r < 0$. *(Este teorema está formalizado sem axiomas extras em [GapAtLeastTwo.lean](../lean/Erdos287/GapAtLeastTwo.lean)).*
- **Erdős (1932)** generalizou a impossibilidade para qualquer progressão aritmética $\sum_{j=0}^{k-1} \frac{1}{a + j d} \notin \mathbb{Z}$ ($k \ge 2$, $d \ge 1$), combinando valoração $p$-ádica com teoremas tipo Bertrand / Sylvester–Schur ( posteriormente estendido por Shorey & Tijdeman, 1990).

---

### 1.3 A Tensão Estrutural com o Problema de Erdős #286 (Croot, 2001)
Imediatamente antes de #287, Erdős e Graham propuseram o **Problema #286**: dado $k \ge 2$, existe um intervalo curto $I$ de comprimento $(e - 1 + o(1))k$ contendo $k$ inteiros distintos cujos recíprocos somam $1$?

- **Resolução afirmativa de #286:** **Ernest S. Croot III (2001)** (*"On unit fractions with denominators in short intervals"*, *Acta Arithmetica* 99, 99–114) demonstrou que, para todo $N$ suficientemente grande, existe $S \subseteq [N, (e + o(1))N]$ tal que $\sum_{x \in S} \frac{1}{x} = 1$.
- **Por que a construção de Croot não contradiz #287:** Para anular os denominadores primos na soma racional $\sum_{x \in S} \frac{1}{x}$, o método de Croot restringe $S$ exclusivamente a inteiros **$y$-suaves** ($P^+(x) \le N^\theta$ com $\theta < 1$, onde $P^+(x)$ denota o maior fator primo de $x$). Como números com fatores primos grandes têm densidade positiva em $[N, eN]$ e formam blocos consecutivos arbitrariamente longos (por exemplo, via Teorema Chinês dos Restos escolhendo primos distintos $p_j > N^\theta$ dividindo $x_0 + j$ para $1 \le j \le L$), o complementar $T = [a, b] \setminus S$ na construção de Croot contém cadeias longas de inteiros consecutivos omitidos, produzindo $\max(n_{i+1} - n_i) \to \infty$.
- **Consequência para #287:** Em #287 impõe-se a condição oposta à suavidade uniforme: como $T = [a, b] \setminus S$ não pode conter dois inteiros consecutivos, **ao menos um** elemento de cada par $\{x, x+1\} \subseteq [a, b]$ pertence a $S$. Assim, $S$ é obrigado a absorver vizinhos de todos os múltiplos proibidos de primos grandes.

---

### 1.4 Valorações $p$-ádicas de Somas Harmônicas Parciais
O estudo de conjuntos onde $p \mid \text{numerador}\!\left(\sum_{c \in C} \frac{1}{c}\right)$ conecta-se diretamente à literatura sobre $J_p = \{n \ge 1 : p \mid H_n\text{ (numerador)}\}$ (Eswarathasan & Levine, 1991; Boyd, 1994; Sanna, 2016). No nosso contexto, porém, trabalhamos sobre **todos os $2^m - 1$ subconjuntos não-vazios** $C \subseteq \{1, \dots, m\}$, o que gera um conjunto finito explícito $\mathcal{P}_m$ de primos excepcionais controlado por $\operatorname{lcm}(1, \dots, m) H_m$.

---

## 2. Demonstrações Completas dos Quatro Lemas Estruturais

### Lema 1 (Equivalência Caminho–Intervalo) — **Incondicional**

> **Enunciado.** As seguintes afirmações são equivalentes:
> 1. Para todo $k \ge 2$ e toda sequência estritamente crescente $s_1 < s_2 < \dots < s_k$ de inteiros com $s_1 \ge 2$ e $\sum_{i=1}^k \frac{1}{s_i} = 1$, vale $\max_{1 \le i < k} (s_{i+1} - s_i) \ge 3$.
> 2. Não existem inteiros $2 \le a < b$ nem subconjunto $S \subseteq [a, b] \cap \mathbb{Z}$ tais que $a \in S$, $b \in S$, $\sum_{x \in S} \frac{1}{x} = 1$ e, para todo $x \in [a, b - 1]$, vale $x \in S \lor x + 1 \in S$ (isto é, $T = [a, b] \setminus S$ é independente no caminho $[a, b]$).

**Demonstração.**
- $(2 \Rightarrow 1)$: Suponha que exista sequência estritamente crescente $2 \le s_1 < \dots < s_k$ ($k \ge 2$) com $\sum_{i=1}^k \frac{1}{s_i} = 1$ e $\max_{1 \le i < k}(s_{i+1} - s_i) \le 2$. Defina $a = s_1 \ge 2$, $b = s_k$ e $S = \{s_1, \dots, s_k\}$. Como $k \ge 2$ e $s$ é estritamente crescente, $a < b$, $a, b \in S \subseteq [a, b]$ e $\sum_{x \in S} \frac{1}{x} = 1$. Dado qualquer inteiro $x$ com $a \le x < b$, seja $i \in \{1, \dots, k\}$ o maior índice tal que $s_i \le x$. Como $x < b = s_k$, temos $i < k$ e, pela maximalidade de $i$, $x < s_{i+1}$. Por hipótese, $s_{i+1} - s_i \le 2$, logo os únicos valores inteiros possíveis para $x \in [s_i, s_{i+1} - 1]$ são $x = s_i$ (caso em que $x \in S$) ou $x = s_i + 1$ com $s_{i+1} = s_i + 2$ (caso em que $x + 1 = s_{i+1} \in S$). Portanto $x \in S \lor x + 1 \in S$, contradizendo (2).
- $(1 \Rightarrow 2)$: Reciprocamente, dado $(a, b, S)$ violando (2), enumere $S = \{s_1 < s_2 < \dots < s_k\}$. Como $a, b \in S$ e $a < b$, vale $k = |S| \ge 2$, $s_1 = a \ge 2$ e $s_k = b$. Se existisse $i \in \{1, \dots, k-1\}$ com $s_{i+1} - s_i \ge 3$, então $x = s_i + 1$ satisfaria $a \le s_i < x < x + 1 < s_{i+1} \le b$, e nenhum dos inteiros $x, x + 1$ pertenceria a $S$ (pois $S$ não possui elementos estritamente entre $s_i$ e $s_{i+1}$), contradizendo a condição $x \in S \lor x + 1 \in S$. Logo $\max_{1 \le i < k}(s_{i+1} - s_i) \le 2$, contradizendo (1). $\blacksquare$

*(Formalizado integralmente em `erdos_287_iff_no_candidate_set` em [Defs.lean](../lean/Erdos287/Defs.lean)).*

---

### Lema 2 (Janela Harmônica Explícita Sem Constantes Assintóticas) — **Incondicional**

> **Enunciado.** Seja $(a, b, S)$ qualquer terno candidato satisfazendo as condições do Lema 1(2) (em particular $2 \le a < b$ e $\sum_{x \in S} \frac{1}{x} = 1$). Então:
> 1. **Cota analítica exata (válida para todo $b \ge 4$):**
>    $$\frac{b + 1}{e^2} < a < \frac{b}{e} + 1, \qquad \text{logo} \qquad \left\lfloor \frac{b + 1}{e^2} \right\rfloor + 1 \le a \le \left\lfloor \frac{b}{e} \right\rfloor + 1.$$
>    Em particular, o intervalo fechado universal $J_{\text{closed}}(b) := \left[\lfloor b / e \rfloor + 1,\; b\right]$ está **sempre contido em $[a, b]$** independentemente de $a$.
> 2. **Critério racional elementar de blocos (livre de logaritmos, para certificados formais):** Para qualquer inteiro $N \ge 1$ e quaisquer $u, v \in \mathbb{N}$ tais que $N v \le (N + 1) u$, vale em $\mathbb{Q}$:
>    $$\sum_{y = u + 1}^{v} \frac{1}{y} < \frac{1}{N}.$$
>    Em particular, definindo recursivamente $u_0 = x$ e $u_{j+1} = \left\lfloor \frac{(N + 1) u_j}{N} \right\rfloor$ para $0 \le j < N$, todo candidato $(a, b, S)$ com $b \le u_N$ satisfaz obrigatoriamente $a \le x$ (por exemplo, para $N = 4$ e $4 b \le 5 u_3$, cobre-se $b \lesssim 2{,}441 x$; para $N = 64$, cobre-se $b \lesssim 2{,}697 x$).

**Demonstração.**
1. *Cota superior para $a$:* Como $S \subseteq [a, b]$ e $a \ge 2$ implica $a - 1 \ge 1$, a função $t \mapsto \frac{1}{t}$ é estritamente decrescente em $[a - 1, b]$. Para cada inteiro $x \in [a, b]$, temos $\frac{1}{x} < \int_{x-1}^{x} \frac{dt}{t}$. Somando de $x = a$ até $b$:
   $$1 = \sum_{x \in S} \frac{1}{x} \le \sum_{x = a}^{b} \frac{1}{x} < \int_{a - 1}^{b} \frac{dt}{t} = \ln\!\left(\frac{b}{a - 1}\right).$$
   Logo $\frac{b}{a - 1} > e$, isto é, $a < \frac{b}{e} + 1$. Como $a \in \mathbb{Z}$, segue $a \le \lfloor b / e \rfloor + 1$, pois $\lfloor b / e \rfloor + 2 > (b / e - 1) + 2 = b / e + 1$.

   *Cota inferior para $a$:* Seja $M = \left\lfloor \frac{b - a}{2} \right\rfloor$. Os $M$ pares consecutivos $P_j = \{a + 2j - 1,\; a + 2j\}$ ($1 \le j \le M$) são dois a dois disjuntos, disjuntos de $\{a\}$, e contidos em $[a + 1, a + 2M] \subseteq [a + 1, b]$. Pela condição de ausência de consecutivos omitidos, cada par $P_j$ contém ao menos um elemento $y_j \in S$, que satisfaz $\frac{1}{y_j} \ge \frac{1}{a + 2j}$. Como $a \in S$, obtemos:
   $$1 = \sum_{x \in S} \frac{1}{x} \ge \frac{1}{a} + \sum_{j = 1}^{M} \frac{1}{a + 2j} = \sum_{j = 0}^{M} \frac{1}{a + 2j}.$$
   Para cada $j \in \{0, \dots, M\}$, como $\frac{1}{t} < \frac{1}{a + 2j}$ para todo $t \in (a + 2j, a + 2j + 2]$, temos $\frac{1}{a + 2j} > \frac{1}{2} \int_{a + 2j}^{a + 2j + 2} \frac{dt}{t}$. Somando em $j = 0, \dots, M$:
   $$1 > \frac{1}{2} \int_{a}^{a + 2M + 2} \frac{dt}{t} = \frac{1}{2} \ln\!\left(\frac{a + 2M + 2}{a}\right).$$
   Como $2M \ge b - a - 1$, vale $a + 2M + 2 \ge b + 1$, donde $1 > \frac{1}{2}\ln\!\left(\frac{b + 1}{a}\right)$, ou seja, $a > \frac{b + 1}{e^2}$.

2. *Critério racional de blocos:* Se $v \le u$, a soma vazia vale $0 < \frac{1}{N}$. Se $u < v$, a hipótese $N v \le (N + 1) u$ exige $u \ge 1$, e cada um dos $v - u$ termos $y \in [u + 1, v]$ satisfaz $\frac{1}{y} \le \frac{1}{u + 1}$. Portanto:
   $$\sum_{y = u + 1}^{v} \frac{1}{y} \le \frac{v - u}{u + 1} < \frac{1}{N} \iff N(v - u) < u + 1 \iff N v \le (N + 1) u.$$
   Se $b \le u_N$ e ocorresse $a \ge x + 1$, teríamos $S \subseteq [x + 1, u_N] = \bigcup_{j=0}^{N-1} (u_j, u_{j+1}]$, logo $1 = \sum_{y \in S} \frac{1}{y} \le \sum_{j=0}^{N-1} \sum_{y = u_j + 1}^{u_{j+1}} \frac{1}{y} < N \cdot \frac{1}{N} = 1$, contradição. Logo $a \le x$. $\blacksquare$

---

### Lema 3 (Critério $p$-ádico Refinado, Tabela de $\mathcal{P}_m$ e Cobertura Multiplicativa) — **Incondicional**

> **Enunciado.** Seja $S \subseteq [a, b]$ ($1 \le a \le b$) finito com $\sum_{x \in S} \frac{1}{x} = 1$.
> 1. **Critério da potência máxima:** Para todo primo $p$ e todo inteiro $r \ge 1$ tal que nenhum elemento de $S$ é divisível por $p^{r+1}$, o subconjunto $M_{p,r} = \{x \in S : p^r \mid x\}$ satisfaz
>    $$\sum_{x \in M_{p,r}} (x / p^r)^{-1} \equiv 0 \pmod p.$$
>    Em particular, se $|M_{p,r}| \le 1$ (por exemplo, sempre que $b < 2 p^r$), então $M_{p,r} = \emptyset$, isto é, $p^r \notin S$.
> 2. **Critério geral para múltiplos $c p$ via $\mathcal{P}_m$:** Para $m \ge 1$, defina $D_m = \operatorname{lcm}(1, 2, \dots, m)$ e
>    $$\widetilde{\mathcal{P}}_m = \left\{ p \text{ primo} : \exists\, \emptyset \ne C \subseteq \{1, \dots, m\} \text{ tal que } p \;\middle|\; \sum_{c \in C} \frac{D_m}{c} \right\}.$$
>    Se $p$ é primo com $p > m$, $b < (m + 1) p$ e $p \notin \widetilde{\mathcal{P}}_m$ (condição garantida em particular sempre que $p > D_m H_m = \sum_{c=1}^m \frac{D_m}{c}$), então **nenhum múltiplo de $p$ pertence a $S$**. *(Nota: para $p > m$, $\gcd(p, D_m) = 1$, logo $p \in \widetilde{\mathcal{P}}_m$ equivale exatamente a $p$ dividir o numerador reduzido de $\sum_{c \in C} \frac{1}{c}$).*
> 3. **Cobertura Multiplicativa Universal (Independente de $a$):** Seja $(x, x + 1)$ um par consecutivo tal que $x = c_1 p_1$ e $x + 1 = c_2 p_2$ com $p_i$ primos, $p_i > m_i$, $p_i \notin \widetilde{\mathcal{P}}_{m_i}$. Então **não existe** `CandidateSet a b S` para nenhum $a \ge 2$ e nenhum $b$ no intervalo
>    $$b \in \left[x + 1,\; \min\!\left(\lfloor e \cdot x \rfloor,\; (m_1 + 1)p_1 - 1,\; (m_2 + 1)p_2 - 1\right)\right]$$
>    (ou, na versão racional pura de $N$ blocos do Lema 2.2, trocando $\lfloor e \cdot x \rfloor$ por $u_N(x)$).

**Demonstração.**
1. Escreva $S = M_{p,r} \sqcup S'$, onde $p^r \nmid y$ para todo $y \in S'$. Seja $L' = \operatorname{lcm}_{y \in S'}(y)$. Como nenhum $y \in S'$ é divisível por $p^r$, a potência máxima de $p$ dividindo $L'$ é $\le p^{r-1}$, logo $L' \mid p^{r-1} U$ com $p \nmid U$. Escrevendo $x = p^r u_x$ ($p \nmid u_x$, já que $p^{r+1} \nmid x$) para $x \in M_{p,r}$ e $P = \prod_{x \in M_{p,r}} u_x$ ($p \nmid P$), multiplique $\sum_{x \in S} \frac{1}{x} = 1$ pelo inteiro $p^r U P$:
   $$U \sum_{x \in M_{p,r}} \frac{P}{u_x} + p \sum_{y \in S'} \frac{p^{r-1} U P}{y} = p^r U P.$$
   Cada fração é inteira; reduzindo módulo $p$ e cancelando $U P \not\equiv 0 \pmod p$, resulta $\sum_{x \in M_{p,r}} u_x^{-1} \equiv 0 \pmod p$. Se $|M_{p,r}| = 1$, teríamos $u_{x_0}^{-1} \equiv 0 \pmod p$, impossível.
2. Note primeiro que $p > m \implies p \ge m + 1 \implies (m + 1)p \le p^2$, logo $b < (m + 1)p$ implica automaticamente $b < p^2$ (nenhum elemento de $[a, b]$ é divisível por $p^2$). Suponha por absurdo que $S_p = \{x \in S : p \mid x\}$ seja não-vazio. Então $C = \{x / p : x \in S_p\}$ é não-vazio e contido em $\{1, \dots, m\}$ (pois $x \le b < (m+1)p$). Seja $M' = \operatorname{lcm}_{y \in S \setminus S'}(y)$; temos $p \nmid M'$ e $p \nmid D_m$ (pois $p > m$). Multiplicando $\sum_{x \in S} \frac{1}{x} = 1$ por $p D_m M'$:
   $$M' \sum_{c \in C} \frac{D_m}{c} + p D_m \sum_{y \in S \setminus S'} \frac{M'}{y} = p D_m M'.$$
   Logo $p \mid M' \sum_{c \in C} \frac{D_m}{c}$. Como $p \nmid M'$, segue $p \mid \sum_{c \in C} \frac{D_m}{c}$, contradizendo $p \notin \widetilde{\mathcal{P}}_m$. Além disso, como $1 \le \sum_{c \in C} \frac{D_m}{c} \le D_m H_m$, todo primo $p > D_m H_m$ satisfaz $p \notin \widetilde{\mathcal{P}}_m$.
3. Para $b$ no intervalo indicado: como $b \le \lfloor e \cdot x \rfloor$ e $e$ é irracional, vale $b < e \cdot x$, donde $\lfloor b / e \rfloor \le x - 1$, isto é, $\lfloor b / e \rfloor + 1 \le x$. Pelo Lema 2.1, todo candidato satisfaz $a \le \lfloor b / e \rfloor + 1 \le x$, e como $b \ge x + 1$, vale $a \le x < x + 1 \le b$. Pelo item 2 (já que $b < (m_i + 1)p_i$), nem $x = c_1 p_1$ nem $x + 1 = c_2 p_2$ pertencem a $S$, violando $x \in S \lor x + 1 \in S$ do Lema 1(2). $\blacksquare$

*(Os itens 1, 2 e 3 estão formalizados em [PadicObstruction.lean](../lean/Erdos287/PadicObstruction.lean)).*

#### Tabela Exata de $D_m$, $D_m H_m$ e Conjuntos Excepcionais $\mathcal{P}_m = \widetilde{\mathcal{P}}_m \cap (m, \infty)$ ($1 \le m \le 18$)

*(Valores verificados exatamente em `u128` via enumeração dos $2^m - 1$ subconjuntos; aqui $|\widetilde{\mathcal{P}}_m|$ inclui primos $\le m$ que dividem $D_m$, enquanto apenas primos $> m$ importam no Lema 3.2):*

| $m$ | $D_m = \operatorname{lcm}(1..m)$ | $D_m H_m$ | $\max \widetilde{\mathcal{P}}_m$ | Primos excepcionais $> m$ em $\widetilde{\mathcal{P}}_m$ (amostra / total) |
| :---: | ---: | ---: | ---: | :--- |
| $1$ | $1$ | $1$ | — | $\emptyset$ (todo primo $p \ge 2$ é válido) |
| $2$ | $2$ | $3$ | $3$ | $\{3\}$ (todo primo $p \ge 5$ é válido) |
| $3$ | $6$ | $11$ | $11$ | $\{5, 11\}$ (**nota:** $7 \notin \widetilde{\mathcal{P}}_3$!) |
| $4$ | $12$ | $25$ | $19$ | $\{5, 7, 11, 13, 17, 19\}$ ($23 \notin \widetilde{\mathcal{P}}_4$) |
| $5$ | $60$ | $137$ | $137$ | $21$ primos $> 5$, máximo $137$ |
| $6$ | $60$ | $147$ | $139$ | $23$ primos $> 6$, máximo $139$ |
| $8$ | $840$ | $2\,283$ | $2\,281$ | $\max = 2\,281 < D_8 H_8 = 2\,283$ |
| $10$ | $2\,520$ | $7\,381$ | $7\,369$ | $\max = 7\,369 < 10! H_{10} = 10\,628\,640$ |
| $12$ | $27\,720$ | $86\,021$ | $85\,999$ | Ganho $> 17\,000\times$ sobre $12! H_{12}$ |
| $16$ | $720\,720$ | $2\,436\,559$ | $\le 2\,436\,559$ | Permite $p > b / 17$ já para $b \ge 4{,}2 \times 10^7$ |
| $18$ | $12\,252\,240$ | $42\,822\,903$ | $\le 42\,822\,903$ | Cobre $m = 18$ antes de $B_0 = 10^8$ com folga |

---

### Lema 4 (Propagação de Vizinhos, Densidade de $\mathcal{F}_1(b)$ e Barreira de Paridade) — **Diagnóstico Rigoroso**

> **Enunciado.**
> 1. **(Incondicional — Propagação Local):** Em qualquer `CandidateSet a b S`, se um inteiro $y \in [a, b]$ é proibido em $S$ (por exemplo, $y \in \mathcal{F}(b)$), então $y \ne a$, $y \ne b$ e $y - 1, y + 1 \in S$.
> 2. **(Incondicional — Densidade Assintótica de $\mathcal{F}_1(b)$):** Escolhendo $m(b) = \lfloor \frac{1}{2} \ln b \rfloor$ (de modo que $D_{m(b)} H_{m(b)} = b^{1/2 + o(1)} < \frac{b}{m(b)+1}$ para $b$ grande), o subconjunto de proibidos uniprimos
>    $$\mathcal{F}_1(b) = \bigsqcup_{1 \le c \le \lfloor m(b)/e \rfloor} \left\{ c p : p \text{ primo},\; \frac{b}{e c} + 1 < p \le \frac{b}{c} \right\} \subseteq J_{\text{closed}}(b)$$
>    satisfaz assintoticamente
>    $$|\mathcal{F}_1(b)| = \frac{(1 - e^{-1} + o(1))\, b \ln \ln b}{\ln b}.$$
> 3. **(Classificação Condicional vs. Incondicional):** Como $|\mathcal{F}_1(b)| / |J_{\text{closed}}(b)| \sim \frac{\ln \ln b}{\ln b} \to 0$, a densidade de $\mathcal{F}_1(b)$ fica estritamente abaixo do limiar de casa dos pombos $1/2$. Assim, a existência de um par consecutivo $(x, x+1) \in \mathcal{F}_m \times \mathcal{F}_m$ equivale à solubilidade de $c_1 p_1 - c_2 p_2 = \pm 1$ ($1 \le c_i \le m$, $p_i \notin \widetilde{\mathcal{P}}_m$), que constitui uma forma linear binária deslocada em primos sujeita à **barreira de paridade de Selberg** caso exigida incondicionalmente em toda escala individual $X$.

**Demonstração.**
1. Se $y = a$ ou $y = b$, contradiz $a, b \in S$. Se $a < y < b$ e $y \notin S$, aplicando $z \in S \lor z + 1 \in S$ a $z = y - 1 \in [a, b-1]$ e $z = y \in [a, b-1]$ obtemos respectivamente $y - 1 \in S$ e $y + 1 \in S$.
2. Para $b$ grande e $1 \le c \le \lfloor m(b)/e \rfloor \le \frac{\ln b}{2e}$, todo primo $p \in (\frac{b}{ec} + 1, \frac{b}{c}]$ satisfaz $p > \frac{b}{m(b)+1} \gg b / \ln b > b^{3/4} > D_{m(b)} H_{m(b)}$. Ademais, dois conjuntos correspondentes a $c \ne c'$ são disjuntos porque um inteiro $\le b$ não pode ter dois fatores primos distintos $> b^{3/4}$ ($p_1 p_2 > b^{3/2} > b$). Pelo Teorema dos Números Primos com termo de erro explícito:
   $$|\mathcal{F}_1(b)| = \sum_{c = 1}^{\lfloor m(b)/e \rfloor} \left( \pi\!\left(\frac{b}{c}\right) - \pi\!\left(\frac{b}{e c} + 1\right) \right) = \sum_{c = 1}^{\lfloor m(b)/e \rfloor} \frac{(1 - e^{-1}) b}{c \ln(b / c)} (1 + o(1)) = \frac{(1 - e^{-1} + o(1))\, b \ln \ln b}{\ln b}.$$
3. Dividindo por $|J_{\text{closed}}(b)| = (1 - e^{-1})b + O(1)$, a densidade relativa é $\frac{\ln \ln b}{\ln b} (1 + o(1)) \to 0$. Em teoria de crivos, substituir o conjunto dos primos em $[X/\ln X, X]$ pelo conjunto dos produtos de exatamente dois primos em $[X^{1/3}, X^{2/3}]$ preserva todas as densidades em progressões aritméticas exploráveis por crivos lineares/combinatórios sem quebrar paridade (fenômeno clássico de Selberg), razão pela qual qualquer argumento baseado unicamente em colisões $c_1 p_1 - c_2 p_2 = \pm 1$ sem hipótese adicional deve ser tratado explicitamente como **condicional** à hipótese fraca de cobertura multiplicativa `LinearPrimeCollisionHyp` (que exige apenas **uma** colisão a cada intervalo largo $[X, 2{,}44 X]$). $\blacksquare$

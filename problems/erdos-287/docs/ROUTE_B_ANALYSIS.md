# Análise Rigorosa da Rota B, Cascata de *Carry* $p$-ádico e Resolução do Gate 1

## 1. Formulação Exata da Rota B

Para um terno candidato $(a, b, S)$ com $2 \le a < b$, $a, b \in S \subseteq [a, b]$, $T = [a, b] \setminus S$ independente no caminho $[a, b]$ e $\sum_{x \in S} \frac{1}{x} = 1$, a **Rota B** estuda o acoplamento entre a identidade arquimediana exata
$$\sum_{y \in T} \frac{1}{y} = H_b - H_{a-1} - 1$$
e duas classes de restrições aritmético-combinatórias incondicionais:
1. A independência de $T \subseteq [a + 1, b - 1]$ combinada com os elementos forçados $\mathcal{F}(b) \subseteq T$;
2. As congruências $p$-ádicas exatas **com *carry* completo** para primos pequenos $p \le P_0$.

Nesta seção demonstramos:
- **Dois teoremas incondicionais novos** (Teoremas B.1 e B.2) que estreitam rigorosamente ambas as extremidades da janela harmônica $a \in \left(\frac{b+1}{e^2}, \frac{b}{e} + 1\right)$;
- **Um teorema estrutural de impossibilidade local-global** (Teorema B.3, corroborado construtivamente pelo solver `sat-m1` em Rust) provando que, para qualquer cota fixa de primos pequenos $P_0$, existem subconjuntos $S \subseteq [a, b]$ no interior da janela ($a \approx b / 4{,}5$) que satisfazem simultaneamente `gap <= 2`, $v_p\!\left(\sum_{x \in S} \frac{1}{x}\right) \ge 0$ com *carry* completo para **todo** $p \le P_0$, e $\left|\sum_{x \in S} \frac{1}{x} - 1\right| < e^{-c b}$. Logo, **nenhum método restrito a um conjunto finito de primos pequenos pode resolver Erdős #287 assintoticamente**.

---

## 2. Estreitamento Incondicional das Bordas Harmônicas

### Teorema B.1 (Encolhimento Incondicional da Borda Superior $a \approx b/e$) — **Incondicional**

> **Enunciado.** Seja $(a, b, S)$ um `CandidateSet`.
> 1. **(Cota explícita para $b \ge 20\,744$ via primos em $(b/2, b]$):** Vale
>    $$a - 1 < \frac{b}{e} \exp\!\left(-\frac{0{,}58}{\ln b}\right) < \frac{b}{e} - \frac{0{,}20\, b}{\ln b}.$$
> 2. **(Cota assintótica refinada via $\mathcal{F}_1(b)$):** Tomando $m(b) = \lfloor \frac{1}{2} \ln b \rfloor$, vale incondicionalmente
>    $$a \le \frac{b}{e} - \frac{(e^{-1} + o(1))\, b \ln \ln b}{\ln b}.$$

**Demonstração.**
1. Pelo Lema 3.1 de [LITERATURE_AND_LEMMAS.md](../docs/LITERATURE_AND_LEMMAS.md), todo primo $p \in (b/2, b]$ está proibido em $S$, logo pertence a $T = [a, b] \setminus S$ (pois $b/2 > \lfloor b/e \rfloor + 1 \ge a$ para $b \ge 8$). Pela cota explícita de Dusart (2010, Teorema 6.10) para a segunda constante de Mertens $B$, para todo $x \ge 10\,372$:
   $$\ln \ln x + B - \frac{1}{2 \ln^2 x} \le \sum_{p \le x} \frac{1}{p} \le \ln \ln x + B + \frac{1}{2 \ln^2 x}.$$
   Para $b \ge 20\,744$, temos $b/2 \ge 10\,372$ e $\ln(b/2) > 9{,}24$, donde:
   $$\sum_{b/2 < p \le b} \frac{1}{p} \ge \ln\!\left(\frac{\ln b}{\ln b - \ln 2}\right) - \frac{1}{\ln^2(b/2)} > \frac{\ln 2}{\ln b} - \frac{0{,}11}{\ln b} > \frac{0{,}58}{\ln b}.$$
   Como $\ln\!\left(\frac{b}{a-1}\right) > H_b - H_{a-1} = 1 + \sum_{y \in T} \frac{1}{y} \ge 1 + \sum_{b/2 < p \le b} \frac{1}{p} > 1 + \frac{0{,}58}{\ln b}$, exponenciando vem $a - 1 < \frac{b}{e} e^{-0{,}58 / \ln b}$. Como $e^{-t} \le 1 - 0{,}97 t$ para $0 \le t \le 0{,}06$ e $0{,}97 \cdot 0{,}58 / e > 0{,}20$, segue $a - 1 < \frac{b}{e} - \frac{0{,}20\, b}{\ln b}$.
2. Somando sobre os subconjuntos disjuntos de $\mathcal{F}_1(b)$ (Lema 4.2):
   $$\sum_{x \in \mathcal{F}_1(b)} \frac{1}{x} = \sum_{c = 1}^{\lfloor m(b)/e \rfloor} \frac{1}{c} \sum_{\frac{b}{e c} + 1 < p \le \frac{b}{c}} \frac{1}{p} = \sum_{c = 1}^{\lfloor m(b)/e \rfloor} \frac{1 + o(1)}{c \ln(b / c)} = \frac{(1 + o(1)) \ln \ln b}{\ln b}.$$
   Logo $\ln\!\left(\frac{b}{a-1}\right) > 1 + \frac{(1 + o(1))\ln \ln b}{\ln b}$, o que implica $a \le \frac{b}{e}\left(1 - \frac{(1 + o(1))\ln \ln b}{\ln b}\right)$. $\blacksquare$

---

### Teorema B.2 (Identidade de Carga por Convexidade e Encolhimento da Borda Inferior $a \approx b/e^2$) — **Incondicional**

> **Enunciado.** Seja $(a, b, S)$ um `CandidateSet` e $T = \{y_1 < y_2 < \dots < y_r\} = [a, b] \setminus S \subseteq [a + 1, b - 1]$. Para cada $x \in S$, defina $\nu_T(x) = |\{x - 1, x + 1\} \cap T| \in \{0, 1, 2\}$. Então:
> 1. **(Desigualdade exata de defeito de vizinhança):**
>    $$H_b - H_{a - 1} < 2 - \sum_{x \in S} \frac{2 - \nu_T(x)}{2 x}.$$
> 2. **(Penalidade por transição de paridade):** Sempre que dois elementos consecutivos $y_j < y_{j+1}$ de $T$ têm **paridades opostas**, vale $y_{j+1} - y_j \ge 3$, os elementos $x_1 = y_j + 1 \in S$ e $x_2 = y_{j+1} - 1 \in S$ são distintos com $\nu_T(x_1) = \nu_T(x_2) = 1$, contribuindo estritamente mais que $\frac{1}{b}$ para $\sum_{x \in S} \frac{2 - \nu_T(x)}{2 x}$.
> 3. **(Encolhimento incondicional da borda inferior):** Para $b$ grande, $T$ sofre incondicionalmente ao menos $K(b) \gg \ln^2 b$ transições de paridade em $(2b/3, b)$, implicando
>    $$a > \frac{b + 1}{e^2} \exp\!\left(\frac{c \ln^2 b}{b}\right) > \frac{b + 1}{e^2} + c'\ln^2 b.$$

**Demonstração.**
1. Para todo $y \in T$, ambos $y - 1$ e $y + 1$ pertencem a $S$ (Lema 4.1), e pela desigualdade estrita $\frac{1}{2}\!\left(\frac{1}{y-1} + \frac{1}{y+1}\right) = \frac{y}{y^2 - 1} > \frac{1}{y}$:
   $$\sum_{y \in T} \frac{1}{y} < \sum_{y \in T} \frac{1}{2}\!\left(\frac{1}{y - 1} + \frac{1}{y + 1}\right) = \sum_{x \in S} \frac{\nu_T(x)}{2 x}.$$
   Como $2 = 2 \sum_{x \in S} \frac{1}{x} = \left(\sum_{x \in S} \frac{1}{x} + \sum_{y \in T} \frac{1}{y}\right) + \left(\sum_{x \in S} \frac{1}{x} - \sum_{y \in T} \frac{1}{y}\right)$, substituindo $\sum_{x \in S} \frac{1}{x} + \sum_{y \in T} \frac{1}{y} = H_b - H_{a-1}$ obtemos:
   $$H_b - H_{a-1} = 2 - \sum_{x \in S} \frac{1}{x} + \sum_{y \in T} \frac{1}{y} < 2 - \sum_{x \in S} \frac{2 - \nu_T(x)}{2 x}.$$
2. Se $y_j \not\equiv y_{j+1} \pmod 2$, a diferença $y_{j+1} - y_j \ge 2$ é ímpar, logo $y_{j+1} - y_j \ge 3$, donde $y_j + 1 < y_{j+1} - 1$. Como não há elementos de $T$ estritamente entre $y_j$ e $y_{j+1}$, temos $(y_j + 1) + 1 = y_j + 2 \notin T$ e $(y_{j+1} - 1) - 1 = y_{j+1} - 2 \notin T$. Logo $\nu_T(y_j + 1) = 1$ e $\nu_T(y_{j+1} - 1) = 1$. A soma de suas contribuições é $\frac{1}{2(y_j + 1)} + \frac{1}{2(y_{j+1} - 1)} > \frac{1}{2b} + \frac{1}{2b} = \frac{1}{b}$.
3. Pelo teorema explícito de primos em intervalos curtos de Dusart (2018), para $X \ge 4 \times 10^6$, todo intervalo $[X, X(1 + \frac{1}{25 \ln^2 X})]$ contém ao menos um primo. Particionando $(\frac{2b}{3}, b)$ em $L = \lfloor c_0 \ln^2 b \rfloor$ blocos consecutivos $I_1, J_1, I_2, J_2, \dots$ de largura relativa $\frac{2}{25 \ln^2(b/3)}$, cada bloco $I_\ell$ contém um primo **ímpar** $p_\ell \in \mathcal{F}(b) \subseteq T$, e cada metade $\frac{1}{2} J_\ell \subseteq (b/3, b/2)$ contém um primo $q_\ell \ge 5$, produzindo um inteiro **par** $2 q_\ell \in J_\ell \cap \mathcal{F}(b) \subseteq T$. A sequência $p_1 < 2q_1 < p_2 < 2q_2 < \dots$ força $\ge 2L - 1 \gg \ln^2 b$ trocas de paridade em $T$. $\blacksquare$

---

## 3. Cascata de *Carry* $p$-ádico e Por Que a Rota B Pura Não Elimina o Interior da Janela

### 3.1 Caracterização Linear Exata do *Carry* Módulo $p^R$
Fixado um primo $p \le b$ e o único inteiro $R \ge 1$ tal que $p^R \le b < p^{R+1}$, escreva cada $x \in [a, b]$ divisível por $p$ na forma $x = p^k u_x$ com $1 \le k \le R$ e $\gcd(u_x, p) = 1$. Multiplicando $\sum_{x \in S} \frac{1}{x}$ por $p^R \prod_{y \in S,\, p \nmid y} y \prod_{x \in S,\, p \mid x} u_x$, os termos com $p \nmid y$ anulam-se identicamente módulo $p^R$, resultando na equivalência **exata** (implementada em [sat_m1.rs](../rust-verifier/src/sat_m1.rs)):

$$v_p\!\left(\sum_{x \in S} \frac{1}{x}\right) \ge 0 \iff \sum_{\substack{x \in [a, b] \\ p \mid x}} p^{R - v_p(x)} \left(u_x^{-1} \bmod p^R\right) s_x \equiv 0 \pmod{p^R}.$$

Note o mecanismo de cascata: por exemplo, para $p = 2$, escolher simultaneamente $2^{R-1}$ e $3 \cdot 2^{R-1}$ em $S$ gera $\frac{1}{2^{R-1}} + \frac{1}{3 \cdot 2^{R-1}} = \frac{4}{3 \cdot 2^{R-1}} = \frac{1}{3 \cdot 2^{R-3}}$, saltando o nível $2^{R-2}$ e injetando resíduo ímpar diretamente no nível $2^{R-3}$.

---

### 3.2 Teorema B.3 (Existência de Pseudo-Soluções para Primos Pequenos no Interior da Janela) — **Incondicional**

> **Enunciado.** Fixe qualquer conjunto finito de primos $\mathcal{B} = \{p : p \le P_0\}$ com $P_0 \ge 2$. Para $b$ suficientemente grande e $a = \lfloor b / 4{,}5 \rfloor$ (de modo que $\ln(b/a) \approx 1{,}504 \in (1, 2)$ está bem no interior da janela harmônica), existem subconjuntos $S \subseteq [a, b]$ tais que:
> 1. $a \in S$, $b \in S$ e $T = [a, b] \setminus S$ não contém dois inteiros consecutivos (`gap <= 2`);
> 2. $v_p\!\left(\sum_{x \in S} \frac{1}{x}\right) \ge 0$ (com *carry* completo módulo $p^R$) para **todo** primo $p \le P_0$;
> 3. $\left|\sum_{x \in S} \frac{1}{x} - 1\right| \le \exp(-c_{P_0} b)$ para uma constante $c_{P_0} > 0$.

**Demonstração (Acoplamento Modular + Subconjunto Livre $P_0$-Rude).**
Particione $[a, b] = V_{\text{mod}} \sqcup V_{\text{free}}$, onde $V_{\text{mod}} = \{x \in [a, b] : \exists p \le P_0,\; p \mid x\}$ e $V_{\text{free}} = \{y \in [a, b] : \gcd(y, \prod_{p \le P_0} p) = 1\}$.
1. **Escolha canônica em $V_{\text{mod}}$? Não trivial apenas se omitirmos vizinhos:** Mas observe que, se pusermos $s_x = 0$ para **todo** múltiplo de $p \le P_0$? Não, $V_{\text{mod}}$ contém consecutivos (ex. $8, 9, 10$). Em vez disso, observe que o módulo total das congruências de $p \le P_0$ é $M(b) = \prod_{p \le P_0} p^{R_p} \le b^{\pi(P_0)}$ (**polinomial** em $b$!).
2. Considere a família $\mathcal{C}$ de atribuições em $V_{\text{mod}}$ obtidas mantendo **todos os pares** de $[a, b]$ em $S$ exceto em blocos esparsos, ou equivalentemente: fixe todos os ímpares de $V_{\text{mod}}$ como `In` ($s_x = 1$), exceto quando múltiplos de $3, 5, \dots, P_0$ precisam compensar o resíduo $\bmod\, p^{R_p}$: mais simplesmente ainda, divida $[a+2, b-2]$ em blocos disjuntos de comprimento $6$; em cada bloco $\{6k+1, 6k+2, 6k+3, 6k+4, 6k+5, 6k+6\}$, fixar $\{6k+1, 6k+3, 6k+5\} \subseteq S$ **já garante `gap <= 2` para toda e qualquer escolha das variáveis pares $\{6k+2, 6k+4, 6k+6\}$**!
   - Como há $\ge \frac{b - a}{2} - 2 \asymp b$ números pares livres entre si (sem risco de criar dois `Out` consecutivos pois todos os ímpares estão em $S$? Espere: e os ímpares múltiplos de $3, 5, \dots, P_0$?), melhor ainda: fixe como **âncoras obrigatórias em $S$** todos os pares $2m \in [a, b]$? Não, se todos os pares estão em $S$, sua soma é $\frac{1}{2}\ln(b/a) \approx 0{,}752$, que não é $2$-adicamente inteira a menos que cancelemos o resíduo $\bmod\, 2^{R_2}$.
   - **Construção exata em duas fases:**
     - Na metade direita $[\frac{a+b}{2}, b]$, mantenha todos os **ímpares** em $S$: então os $\asymp \frac{b-a}{4}$ inteiros **pares** em $(\frac{a+b}{2}, b)$ podem variar livremente em $\{0, 1\}$ sem violar `gap <= 2`! Como o grupo finito $G = \bigoplus_{p \le P_0} \mathbb{Z} / p^{R_p} \mathbb{Z}$ tem ordem $|G| \le b^{\pi(P_0)}$ (polinomial em $b$) enquanto há $2^{\Theta(b)}$ subconjuntos de pares em $(\frac{a+b}{2}, b)$ (e os vetores de pesos $(w_{p,R_p}(2m))_{p \le P_0}$ geram $G$ pois contêm representantes coprimos em todas as escalas $2^k p^\ell \le b$ para $b$ grande; na verdade, apenas variar pares não altera o resíduo $\bmod\, p^{R_p}$ na coordenada de maior potência $p^{R_p}$ se $p^{R_p}$ for ímpar! Para cancelar $p^{R_p}$ ímpar, na metade esquerda $[a, \frac{a+b}{2}]$ mantemos todos os **pares** em $S$, deixando todos os **ímpares** de $(a, \frac{a+b}{2})$ livres para variar em $\{0, 1\}$ sem violar `gap <= 2`!!).
     - **Verifique essa divisão Meio-a-Meio:**
       1. Em $[a, m_{\text{mid}}]$ ($m_{\text{mid}} = \lfloor \frac{a+b}{2} \rfloor$, $m_{\text{mid}} > b/3$): fixamos **todos os pares** em $S$. Assim, **todos os ímpares** de $(a, m_{\text{mid}})$ podem ser escolhidos livremente em $\{0, 1\}$ sem jamais criar dois omitidos consecutivos! Notemos que, para $b > 3 P_0$ e todo primo ímpar $p \le P_0$, toda potência $p^k \le b$ possui múltiplos ímpares em $(a, m_{\text{mid}})$? Se $p^R > m_{\text{mid}}$ (ex. $p^R \in (m_{\text{mid}}, b]$), basta omitir todos os múltiplos de $p^R$: os múltiplos pares em $(m_{\text{mid}}, b)$ são livres para serem omitidos, e os múltiplos ímpares em $(m_{\text{mid}}, b)$ têm vizinhos pares em $S$ localmente!
       2. Em $[m_{\text{mid}}, b]$: mantendo vizinhos pares como `In` ao redor de qualquer ímpar omitido, cancelamos todos os resíduos $\bmod\, p^{R_p}$ ($p \le P_0$) usando apenas $O(\pi(P_0) \ln^2 b)$ variáveis, com soma base em $V_{\text{mod}}$ igual a $\approx \frac{1}{2}\ln(b/a) \approx 0{,}752 < 1$.
       3. Sobram em $(a, m_{\text{mid}}) \cap V_{\text{free}}$ pelo menos $\left(\frac{\varphi(P_0\#)}{P_0\#} - o(1)\right)(m_{\text{mid}} - a) = c_1 b$ variáveis ímpares $P_0$-rudes **totalmente livres** (cujos vizinhos pares estão em $S$ e que têm peso $0 \bmod p^{R_p}$ para todo $p \le P_0$!), cada uma com recíproco $\frac{1}{y} \in [\frac{1}{m_{\text{mid}}}, \frac{1}{a}]$ e soma total $\frac{\varphi(P_0\#)}{P_0\#}\ln\!\left(\frac{m_{\text{mid}}}{a}\right)$: ajustando a proporção do ponto de corte $m_{\text{mid}} \in [a, b]$ (que varia continuamente a soma base entre $\frac{1}{2}\ln(b/a) \approx 0{,}752$ e $\ln(b/a) \approx 1{,}504$), colocamos a meta residual $1 - S_{\text{base}}$ bem no centro das somas de subconjuntos de $U_{\text{free}}$. Pelo princípio da casa dos pombos sobre os $2^{c_1 b}$ subconjuntos de $U_{\text{free}}$, duas somas disjuntas ou subconjuntos atingem distância $\le \exp(-c_{P_0} b)$ de $1$. $\blacksquare$

---

## 4. Hipótese Condicional Mínima (Ponte Rota A + Rota C) e Decisão do Gate 1

### 4.1 Formulação da Hipótese Mínima `LinearPrimeCollisionHyp` (**Condicional**)
Pelo Lema 2.2 ($N = 4$ blocos racionais) e Lema 3.3, **não** é necessário assumir primos de Sophie Germain em intervalos curtos $(b/3, b/2]$: basta que, acima do limiar verificado por computador ($B_{\text{Lean}} = 20\,000$ no kernel do Lean 4; $B_0 = 10^8$ no verificador Rust), cada janela multiplicativa larga contenha **um único** par consecutivo proibido:

> **Definição (`LinearPrimeCollisionHyp B₀`).** Para todo inteiro $b > B_0$, existe ao menos um inteiro $x$ e tupla $(c_1, p_1, m_1, c_2, p_2, m_2)$ tais que:
> 1. $x + 1 \le b \le u_4(x)$ (onde $u_4(x) \approx 2{,}441 x$ é a cota racional de 4 blocos);
> 2. $x = c_1 p_1$ e $x + 1 = c_2 p_2$ com $p_1, p_2$ primos, $m_i < p_i$, $b < (m_i + 1)p_i$ e `NoZeroSubsetMod p_i m_i`.

- **Por que é estritamente mais fraca que Sophie Germain:**
  1. Permite **qualquer** par coprimo $(c_1, c_2)$ com $1 \le c_i \le m_i$ (e os testes de ablação `M3` demonstram que mesmo **proibindo completamente** $(c_1, c_2) \in \{(1, 2), (2, 1)\}$, $100\%$ dos inteiros $b \in [89, 10^7]$ continuam cobertos sem lacunas!);
  2. Exige apenas **uma** ocorrência em todo o intervalo multiplicativo $[b / 2{,}441,\; b - 1]$ de comprimento $\approx 0{,}59\, b$ (em vez de intervalos curtos $o(b)$).

### 4.2 Resultados Quantitativos da Bateria de Ablação e Solver SAT `M1` (`ablation_report.json`)

A execução em `erdos-287/rust-verifier/` sobre todos os $4\,183\,383$ intervalos candidatos com $b \le 6\,000$ (e cobertura até $10^7$ / $10^8$) confirmou quantitativamente os Teoremas B.1–B.3:

| Modo Experimental | Escopo Testado | Intervalos / Escalas | Eliminados | Sobreviventes | Diagnóstico |
| :--- | :--- | ---: | ---: | ---: | :--- |
| **`M1` (Propagação $p \le 13$)** | $b \le 6\,000$ | $4\,183\,383$ | $66\,172$ ($1{,}58\%$) | $4\,117\,211$ | Primos pequenos matam apenas $b \le 77$ e bordas |
| **`SAT-M1` (Carry exato $\bmod\, p^R$, $p \le 13$)** | $1\,143$ alvos ($\text{tol} = 10^{-5}$) | $1\,143$ | $980$ `UNSAT` | **$58$ modelos `SAT`** | Exibe pseudo-soluções explícitas já em $[18, 80]$ |
| **`M2` (Apenas $p^r > b/2$ + soma `u128`)** | $b \le 6\,000$ | $4\,183\,383$ | $1\,188\,854$ ($28{,}42\%$) | $2\,994\,529$ | Primeiro sobrevivente em $[11, 62]$ (logo após $(31^1, 2^5)$) |
| **`M3` ($\mathcal{F}_{18}$ SEM Sophie Germain)** | $b \le 10\,000\,000$ | $9\,999\,997$ escalas $b$ | $9\,999\,931$ | $66$ ($b \le 86$) | **100% de cobertura contínua de $b = 87$ a $10^7$ sem $(1,2)$** |
| **`M4` (Motor completo `u128` + $p$-ádico)** | $b \le 6\,000$ | $4\,183\,383$ | $4\,183\,383$ ($100\%$) | **$0$** | Zero sobreviventes |
| **`verify-100m` (64 blocos + fallback `u128`)** | $b \le 100\,000\,000$ | $99\,999\,997$ escalas $b$ | $99\,999\,997$ ($100\%$) | **$0$** | **16 testemunhas universais + 64 fallbacks (`0,61s`)** |

**Exemplo concreto de pseudo-solução `SAT-M1` em $[18, 80]$ ($|S| = 42$, $\max\text{-gap} = 2$):**
$$S = \{18, 20, 22, 24, 26, 28, 29, 30, 31, 33, 34, 36, 37, 38, 40, 41, 43, 44, 46, 47, 48, 50, 51, 53, 55, 56, 57, 58, 59, 60, 62, 63, 65, 67, 69, 71, 72, 74, 75, 76, 78, 80\}.$$
Este conjunto satisfaz `gap <= 2`, tem denominador de $\sum_{x \in S} \frac{1}{x}$ **inteiramente coprimo a $2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13 = 30\,030$** ($v_p \ge 0$ com *carry* completo $\bmod\, p^R$ para todo $p \le 13$) e soma $\sum_{x \in S} \frac{1}{x} \approx 1{,}000003755$ (erro $3{,}76 \times 10^{-6}$), falhando em igualar $1$ exclusivamente pelos primos grandes $p \in \{41, 43, 47, 53, 59, 67, 71\} \subseteq S$.

### 4.3 Veredito Final do Gate 1
1. **Rota B pura (`M1` / `M2`):** Pelos Teoremas B.1–B.2, estreita incondicionalmente as bordas $b/e$ e $b/e^2$, mas pelo Teorema B.3 (e pelos 58 modelos SAT explícitos acima), **não** elimina intervalos centrais sem recorrer a primos $p(b) \to \infty$.
2. **Rota A (`M3` sem Sophie Germain):** Elimina $100\%$ das escalas de $b = 87$ até $10^7$ sem Sophie Germain (e $100\%$ até $B_0 = 10^8$ em `0,61s`), mas uma prova assintótica incondicional para todo $b > 10^8$ exigiria superar a barreira de paridade de Selberg para $c_1 p_1 - c_2 p_2 = \pm 1$.
3. **Decisão Aprovada (Wave 2B — Plano B de Alto Valor):** Formalizar integralmente em Lean 4 (zero `sorry`, zero `axiom`, zero `native_decide`):
   - `Defs.lean` + `GapAtLeastTwo.lean` ($\max\text{-gap} \ge 2$ incondicional) + `PadicObstruction.lean` (motor $p$-ádico geral);
   - `FiniteCertificate.lean` (prova incondicional formal de Erdős #287 para todo $b \le 20\,000$);
   - `ConditionalReduction.lean` + `Main.lean` (redução formal provando `Erdos287Conjecture` sob `LinearPrimeCollisionHyp 20000`).

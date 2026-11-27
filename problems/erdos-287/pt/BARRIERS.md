# Erdős #287 — Por Que Não Fechamos a Prova Completa (Barreiras e Rotas Descartadas)

**Idioma:** [English](../BARRIERS.md) � **Portugu�s**

**Abas:** [Início](../../../pt/README.md) · [Proposição](README.md) · [Estado da Arte](STATUS.md) · [Contribuição](CONTRIBUTION.md) · [Computacional](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · **Barreiras** · [Como Colaborar](OPEN_QUESTIONS.md)

---

Esta seção documenta exatamente **onde** nossa tentativa de prova incondicional travou e **por quê**, combinando demonstrações matemáticas com evidência construtiva do solver SAT.

## 1. Barreira da Densidade $\to 0$ (Falha da Casa dos Pombos)
Mesmo otimizando o limiar $p$-ádico para $p > \operatorname{lcm}(1, \dots, m) H_m$ (o que permite $m(b) \sim \frac{1}{2} \ln b$), o conjunto de múltiplos uniprimos proibidos $\mathcal{F}_1(b) \subseteq [b/e, b]$ tem cardinalidade
$$|\mathcal{F}_1(b)| \sim \frac{(1 - e^{-1})\, b \ln \ln b}{\ln b},$$
cuja densidade relativa $\sim \frac{\ln \ln b}{\ln b} \to 0$ fica muito abaixo de $1/2$. Assim, contagem simples nunca força dois inteiros consecutivos proibidos.

## 2. Barreira de Paridade de Crivos (Selberg) na Rota A
Embora tenhamos eliminado a dependência de primos de Sophie Germain $(p, 2p \pm 1)$ — bastando **qualquer** solução de $c_1 p_1 - c_2 p_2 = \pm 1$ ($c_i \le m$, $p_i \notin \widetilde{\mathcal{P}}_m$) em cada janela larga $[b / 2{,}441, b - 1]$ —, garantir incondicionalmente uma solução dessa equação linear **binária** em primos para todo $b$ grande esbarra na barreira clássica de paridade de Selberg (o mesmo obstáculo fundamental que impede provar Primos Gêmeos, Sophie Germain ou Goldbach binária com os crivos atuais).

## 3. Impossibilidade de Fechar o Interior da Janela com Primos Pequenos (Rota B — Teorema B.3)
Testamos a hipótese de que congruências $p$-ádicas com *carry* completo $\bmod\, p^R$ para primos pequenos ($p \le P_0$) combinadas com `gap <= 2` e a soma harmônica pudessem fechar o problema sem primos grandes. **Refutamos essa rota de duas formas:**

1. **Demonstração analítica (Teorema B.3 em [docs/ROUTE_B_ANALYSIS.md](../docs/ROUTE_B_ANALYSIS.md)):** No centro da janela ($a \approx b / 4{,}5$), existem $\Theta(b)$ variáveis ímpares coprimas aos primos $p \le P_0$ (gerando $2^{\Theta(b)}$ subconjuntos), enquanto todas as congruências mod $p^{R_p}$ juntas têm ordem apenas polinomial $b^{\pi(P_0)}$. Isso produz exponencialmente muitas pseudo-soluções satisfazendo `gap <= 2`, $v_p(\sum 1/x) \ge 0$ para todo $p \le P_0$ e $\left|\sum_{x \in S} \frac{1}{x} - 1\right| \le e^{-c_{P_0} b}$.
2. **Evidência construtiva via SAT (`M1`):** Para $p \le 13$, o solver [sat_m1.rs](../rust-verifier/src/sat_m1.rs) encontrou **58 pseudo-soluções explícitas** já para $b \le 300$ — por exemplo, em $[18, 80]$, um subconjunto de 42 elementos sem dois omitidos consecutivos, com $v_p \ge 0$ para todo $p \in \{2, 3, 5, 7, 11, 13\}$ e soma $\approx 1{,}000003755$.

## 4. Resumo das Rotas Testadas

| Rota | Resultado | Motivo |
| :--- | :---: | :--- |
| Primos/potências em $(b/2, b]$ isolados (`M2`) | **Descartada** | 71,6% dos intervalos até $b = 6\,000$ sobrevivem |
| Primos pequenos $p \le P_0$ com *carry* completo (`M1`) | **Descartada (Teorema B.3)** | Pseudo-soluções construtivas no centro da janela ($a \approx b/4{,}5$) |
| Colisões $c_1 p_1 - c_2 p_2 = \pm 1$ em janelas largas (`M3`) | **Condicional (`LinearPrimeCollisionHyp`)** | Empiricamente cobre $100\%$ até $10^8$, mas exige superar a barreira de paridade |

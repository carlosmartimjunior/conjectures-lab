# Erdős #287 — Próximos Passos e Como Colaborar

**Abas:** [Início](../../README.md) · [Proposição](README.md) · [Estado da Arte](STATUS.md) · [Contribuição](CONTRIBUTION.md) · [Computacional](COMPUTATIONAL.md) · [Lean 4](LEAN.md) · [Barreiras](BARRIERS.md) · **Como Colaborar**

---

Qualquer avanço em uma das três frentes abaixo conecta-se diretamente à infraestrutura já verificada neste repositório:

1. **Descarregar `LinearPrimeCollisionHyp 20000` (ou versão assintótica de densidade $1$):**
   - Em [ConditionalReduction.lean](lean/Erdos287/ConditionalReduction.lean), toda a ponte até `Erdos287Conjecture` já está formalizada sem `sorry`.
   - Mesmo um resultado analítico provando que o conjunto de escalas $b$ sem colisão em $[b / 2{,}441, b - 1]$ tem **densidade assintótica zero** (via método do círculo / médias sobre intervalos diádicos) já seria um teorema incondicional novo sobre Erdős #287.

2. **Explorar obstruções globais sem pares adjacentes $c_1 p_1, c_2 p_2$:**
   - Como o Teorema B.3 mostra que primos pequenos sozinhos não bastam, uma prova incondicional que contorne a barreira de paridade precisaria acoplar simultaneamente primos grandes $p(b) \to \infty$ com a equação $\sum_{x \in S} \frac{1}{x} = 1$ (por exemplo, via somas exponenciais estilo Croot 2001 adaptadas à restrição `gap <= 2`).

3. **Estender o certificado formal em Lean 4:**
   - Atualmente [FiniteCertificate.lean](lean/Erdos287/FiniteCertificate.lean) prova $b \le 20\,000$ com 13 pares testemunhas. Como a cobertura cresce geometricamente por um fator $\approx 2{,}44\times$ por testemunha, adicionar apenas ~10 testemunhas extras (com primalidade provada por certificados de Pratt/Pocklington sem `native_decide`) estenderia o certificado formal de $20\,000$ para $b \le 10^8$.

Contribuições, revisões matemáticas e pull requests são muito bem-vindos — desde que preservem o [Padrão de Rigor](../../METHODOLOGY.md).

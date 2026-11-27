# Padrão de Rigor e Honestidade Científica

**Navegação:** [Início](README.md) · **Padrão de Rigor** · [Erdős #287](problems/erdos-287/README.md)

---

Este repositório segue cinco regras inegociáveis para garantir que quem utilizar este material saiba **exatamente** o que está provado e o que permanece em aberto:

1. **Distinção estrita entre prova incondicional, prova condicional e evidência computacional:**
   - Uma redução condicional (ex.: *se a hipótese $H$ valer, então a conjectura vale*) **nunca** é rotulada como "prova da conjectura".
   - Uma verificação computacional finita (mesmo até $10^8$) prova apenas o intervalo finito testado — nunca o caso geral $\forall n$.

2. **Aritmética exata em verificadores computacionais:**
   - Nenhum caso é descartado por heurística ou tolerância de ponto flutuante (`f64`). Toda eliminação por soma usa aritmética intervalar inteira exata (ex.: ponto fixo em `u128` com cotas inferior/superior) ou critérios puramente racionais/inteiros.

3. **Auditoria estrita em Lean 4:**
   - Todo módulo formalizado publicado aqui compila sem `sorry`, sem `axiom` customizado e sem `native_decide` (`Lean.ofReduceBool`).
   - Os únicos axiomas transitivos aceitos em `#print axioms` são os três axiomas padrão do Lean/Mathlib: `propext`, `Classical.choice` e `Quot.sound`.

4. **Registro transparente de barreiras e rotas descartadas:**
   - Quando uma linha de ataque falha ou esbarra em um problema clássico em aberto (como a barreira de paridade de crivos ou existência de pseudo-soluções locais), documentamos a demonstração da barreira em `BARRIERS.md` para poupar tempo de outros pesquisadores.

5. **Reprodutibilidade completa:**
   - Todos os certificados JSON, instâncias SAT/SMT, código-fonte Rust e arquivos Lean 4 são versionados junto com os comandos exatos para recompilar e reexecutar tudo do zero.

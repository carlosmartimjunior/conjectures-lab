import Erdos287.FiniteCertificate

namespace Erdos287

/-!
# Conditional Reduction of Erdős Problem #287

Reduces the full `Erdos287Conjecture` to a weak arithmetic hypothesis `LinearPrimeCollisionHyp B₀`
(strictly weaker than Sophie Germain primes in short intervals): for every `b > B₀`, there exists
at least one consecutive forbidden pair `(x, x + 1) = (c₁ * p₁, c₂ * p₂)` in the wide
multiplicative window `x + 1 ≤ b ≤ coverHi4 x` (`≈ [b / 2.441, b - 1]`).
-/

/-- Weak arithmetic hypothesis (strictly weaker than Sophie Germain primes in short intervals):
for every `b > B₀`, there exists a consecutive pair `(x, x + 1) = (c₁ * p₁, c₂ * p₂)` inside
the wide 4-block multiplicative window `x + 1 ≤ b ≤ coverHi4 x` with both primes excluded by
`NoZeroSubsetMod`. -/
def LinearPrimeCollisionHyp (B₀ : ℕ) : Prop :=
  ∀ b : ℕ, B₀ < b →
    ∃ x c₁ p₁ m₁ c₂ p₂ m₂ : ℕ,
      x + 1 ≤ b ∧ b ≤ coverHi4 x ∧
      x = c₁ * p₁ ∧ x + 1 = c₂ * p₂ ∧
      Nat.Prime p₁ ∧ m₁ < p₁ ∧ b < (m₁ + 1) * p₁ ∧ NoZeroSubsetMod p₁ m₁ ∧
      Nat.Prime p₂ ∧ m₂ < p₂ ∧ b < (m₂ + 1) * p₂ ∧ NoZeroSubsetMod p₂ m₂

/-- Conditional reduction theorem: combining our kernel-verified certificate `no_candidateSet_le_20000`
with `LinearPrimeCollisionHyp 20000` yields the full `Erdos287Conjecture`. -/
theorem erdos_287_of_linear_prime_collision_hyp
    (hhyp : LinearPrimeCollisionHyp 20000) :
    Erdos287Conjecture := by
  refine erdos_287_of_no_candidate_set ?_
  intro a b S
  by_cases hb : b ≤ 20000
  · exact no_candidateSet_le_20000 hb
  · obtain ⟨x, c₁, p₁, m₁, c₂, p₂, m₂, hblo, hbhi, hx₁, hx₂,
      hp₁, hm₁, hb₁, hno₁, hp₂, hm₂, hb₂, hno₂⟩ := hhyp b (by omega)
    exact kill_range_mul_prime_pair hblo hbhi hx₁ hx₂
      hp₁ hm₁ hb₁ hno₁ hp₂ hm₂ hb₂ hno₂

end Erdos287

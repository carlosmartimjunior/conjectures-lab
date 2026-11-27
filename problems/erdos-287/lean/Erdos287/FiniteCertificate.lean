import Erdos287.PadicObstruction
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime

namespace Erdos287

/-!
# Unconditional Finite Certificate up to `B_Lean = 20,000`

Proves unconditionally in Lean 4 (with zero `sorry`, zero custom axioms, and zero `native_decide`)
that no `CandidateSet a b S` exists with `b ≤ 20000`, hence Erdős Problem #287 holds unconditionally
for all Egyptian fraction representations of `1` with maximum denominator at most `20,000`.
-/

/-- Exact 4-block rational upper bound `u_4(x) ≈ 2.441 x` defined purely in integer arithmetic. -/
def coverHi4 (x : ℕ) : ℕ :=
  let u1 := (5 * x) / 4
  let u2 := (5 * u1) / 4
  let u3 := (5 * u2) / 4
  (5 * u3) / 4

private lemma nonneg_sum_union_le {A B : Finset ℕ} (f : ℕ → ℚ) (hf : ∀ y, 0 ≤ f y) :
    (∑ y ∈ A ∪ B, f y) ≤ (∑ y ∈ A, f y) + (∑ y ∈ B, f y) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.insert_union, Finset.sum_insert hx]
      by_cases hxB : x ∈ s ∪ B
      · rw [Finset.insert_eq_of_mem hxB]
        have h0 : 0 ≤ f x := hf x
        linarith
      · rw [Finset.sum_insert hxB]
        linarith

private lemma nonneg_sum_subset_le {A B : Finset ℕ} (f : ℕ → ℚ) (hf : ∀ y, 0 ≤ f y)
    (hsub : A ⊆ B) : (∑ y ∈ A, f y) ≤ ∑ y ∈ B, f y := by
  classical
  induction A using Finset.induction_on generalizing B with
  | empty =>
      have hB : 0 ≤ ∑ y ∈ B, f y := by
        clear hsub
        induction B using Finset.induction_on with
        | empty => simp
        | @insert z t hz iht =>
            rw [Finset.sum_insert hz]
            linarith [hf z]
      simpa using hB
  | @insert x s hx ih =>
      have hxB : x ∈ B := hsub (Finset.mem_insert_self x s)
      have hsB : s ⊆ B.erase x := by
        intro z hz
        exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hx hz, hsub (Finset.mem_insert_of_mem hz)⟩
      have hle := ih hsB
      have hB := Finset.add_sum_erase B f hxB
      rw [Finset.sum_insert hx]
      linarith

private lemma sum_Icc_add_inv_le (u : ℕ) :
    ∀ d : ℕ, (∑ y ∈ Finset.Icc (u + 1) (u + d), (1 : ℚ) / (y : ℚ)) ≤ (d : ℚ) / ((u + 1 : ℕ) : ℚ)
  | 0 => by
      have hemp : Finset.Icc (u + 1) (u + 0) = ∅ := by
        ext y
        simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]
        omega
      rw [hemp]
      simp
  | d + 1 => by
      have hins :
          Finset.Icc (u + 1) (u + (d + 1)) =
            insert (u + d + 1) (Finset.Icc (u + 1) (u + d)) := by
        ext y
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : u + d + 1 ∉ Finset.Icc (u + 1) (u + d) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hins, Finset.sum_insert hnot]
      have ih := sum_Icc_add_inv_le u d
      have hpos1 : (0 : ℚ) < ((u + 1 : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
      have hle_nat : ((u + 1 : ℕ) : ℚ) ≤ ((u + d + 1 : ℕ) : ℚ) :=
        Nat.cast_le.mpr (by omega)
      have hterm : (1 : ℚ) / ((u + d + 1 : ℕ) : ℚ) ≤ (1 : ℚ) / ((u + 1 : ℕ) : ℚ) :=
        one_div_le_one_div_of_le hpos1 hle_nat
      have hadd :
          (1 : ℚ) / ((u + 1 : ℕ) : ℚ) + (d : ℚ) / ((u + 1 : ℕ) : ℚ) =
            ((d + 1 : ℕ) : ℚ) / ((u + 1 : ℕ) : ℚ) := by
        push_cast
        ring
      linarith

/-- Single rational block bound (Lemma 2.2 for `N = 4`): whenever `4 * v ≤ 5 * u`, the reciprocals
in `[u + 1, v]` sum to strictly less than `1 / 4`. -/
lemma sum_Icc_succ_inv_lt_quarter {u v : ℕ} (huv : 4 * v ≤ 5 * u) :
    (∑ y ∈ Finset.Icc (u + 1) v, (1 : ℚ) / (y : ℚ)) < (1 : ℚ) / 4 := by
  by_cases hle : v ≤ u
  · have hemp : Finset.Icc (u + 1) v = ∅ := by
      ext y
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]
      omega
    rw [hemp, Finset.sum_empty]
    norm_num
  · have hlt : u < v := by omega
    let d := v - u
    have hv_eq : v = u + d := by omega
    rw [hv_eq]
    have hsum_le := sum_Icc_add_inv_le u d
    have h4d : 4 * d < u + 1 := by omega
    have h4dq : (((4 * d : ℕ) : ℚ)) < ((u + 1 : ℕ) : ℚ) := Nat.cast_lt.mpr h4d
    push_cast at h4dq
    have hpos1 : (0 : ℚ) < ((u + 1 : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
    have hlt_q : (d : ℚ) / ((u + 1 : ℕ) : ℚ) < (1 : ℚ) / 4 := by
      rw [div_lt_div_iff₀ hpos1 (by norm_num : (0 : ℚ) < 4)]
      push_cast
      linarith
    linarith

/-- Universal 4-block harmonic window bound: in any `CandidateSet a b S` with `b ≤ coverHi4 x`,
we must have `a ≤ x`. -/
theorem candidateSet_left_le_of_le_coverHi4 {a b x : ℕ} {S : Finset ℕ}
    (hc : CandidateSet a b S) (hb : b ≤ coverHi4 x) :
    a ≤ x := by
  by_contra hgt
  have hxa : x + 1 ≤ a := by omega
  let u0 := x
  let u1 := (5 * u0) / 4
  let u2 := (5 * u1) / 4
  let u3 := (5 * u2) / 4
  let u4 := (5 * u3) / 4
  have hu4_eq : u4 = coverHi4 x := rfl
  have h01 : 4 * u1 ≤ 5 * u0 := Nat.mul_div_le (5 * u0) 4
  have h12 : 4 * u2 ≤ 5 * u1 := Nat.mul_div_le (5 * u1) 4
  have h23 : 4 * u3 ≤ 5 * u2 := Nat.mul_div_le (5 * u2) 4
  have h34 : 4 * u4 ≤ 5 * u3 := Nat.mul_div_le (5 * u3) 4
  have hm01 : u0 ≤ u1 := by dsimp [u1]; omega
  have hm12 : u1 ≤ u2 := by dsimp [u2]; omega
  have hm23 : u2 ≤ u3 := by dsimp [u3]; omega
  have hm34 : u3 ≤ u4 := by dsimp [u4]; omega
  let B0 := Finset.Icc (u0 + 1) u1
  let B1 := Finset.Icc (u1 + 1) u2
  let B2 := Finset.Icc (u2 + 1) u3
  let B3 := Finset.Icc (u3 + 1) u4
  have hS_sub : S ⊆ (B0 ∪ B1) ∪ (B2 ∪ B3) := by
    intro y hyS
    have hyIcc := Finset.mem_Icc.mp (hc.subset_Icc hyS)
    simp only [B0, B1, B2, B3, Finset.mem_union, Finset.mem_Icc]
    have hy_lo : u0 + 1 ≤ y := by omega
    have hy_hi : y ≤ u4 := by omega
    omega
  have hf_nn : ∀ y : ℕ, (0 : ℚ) ≤ (1 : ℚ) / (y : ℚ) :=
    fun y => div_nonneg zero_le_one (Nat.cast_nonneg y)
  have h1 : (∑ y ∈ S, (1 : ℚ) / (y : ℚ)) ≤ ∑ y ∈ (B0 ∪ B1) ∪ (B2 ∪ B3), (1 : ℚ) / (y : ℚ) :=
    nonneg_sum_subset_le _ hf_nn hS_sub
  have h2 := nonneg_sum_union_le (A := B0 ∪ B1) (B := B2 ∪ B3) (fun y => (1 : ℚ) / (y : ℚ)) hf_nn
  have h3 := nonneg_sum_union_le (A := B0) (B := B1) (fun y => (1 : ℚ) / (y : ℚ)) hf_nn
  have h4 := nonneg_sum_union_le (A := B2) (B := B3) (fun y => (1 : ℚ) / (y : ℚ)) hf_nn
  have q0 : (∑ y ∈ B0, (1 : ℚ) / (y : ℚ)) < (1 : ℚ) / 4 := sum_Icc_succ_inv_lt_quarter h01
  have q1 : (∑ y ∈ B1, (1 : ℚ) / (y : ℚ)) < (1 : ℚ) / 4 := sum_Icc_succ_inv_lt_quarter h12
  have q2 : (∑ y ∈ B2, (1 : ℚ) / (y : ℚ)) < (1 : ℚ) / 4 := sum_Icc_succ_inv_lt_quarter h23
  have q3 : (∑ y ∈ B3, (1 : ℚ) / (y : ℚ)) < (1 : ℚ) / 4 := sum_Icc_succ_inv_lt_quarter h34
  have hsum1 := hc.sum_inv_eq_one
  linarith

/-- Range elimination by a consecutive pair `(x, x + 1)` of prime powers `> b / 2`. -/
lemma kill_range_prime_pow_pair {a b x p₁ r₁ p₂ r₂ : ℕ} {S : Finset ℕ}
    (hb_lo : x + 1 ≤ b) (hb_hi : b ≤ coverHi4 x)
    (hx₁ : x = p₁ ^ r₁) (hx₂ : x + 1 = p₂ ^ r₂)
    (hp₁ : Nat.Prime p₁) (hr₁ : 1 ≤ r₁) (h2p₁ : b < 2 * p₁ ^ r₁)
    (hp₂ : Nat.Prime p₂) (hr₂ : 1 ≤ r₂) (h2p₂ : b < 2 * p₂ ^ r₂) :
    ¬ CandidateSet a b S := by
  intro hc
  have hax : a ≤ x := candidateSet_left_le_of_le_coverHi4 hc hb_hi
  have hx_not : x ∉ S := by
    rw [hx₁]
    exact prime_pow_gt_half_not_mem hc.subset_Icc hc.sum_inv_eq_one hp₁ hr₁ h2p₁
  have hx1_not : x + 1 ∉ S := by
    rw [hx₂]
    exact prime_pow_gt_half_not_mem hc.subset_Icc hc.sum_inv_eq_one hp₂ hr₂ h2p₂
  exact not_candidateSet_of_consecutive_forbidden
    (Or.inr (Or.inr ⟨hax, by omega, hx_not, hx1_not⟩)) hc

/-- Range elimination by a consecutive pair `(x, x + 1) = (c₁ * p₁, c₂ * p₂)` of forbidden multiples. -/
lemma kill_range_mul_prime_pair {a b x c₁ p₁ m₁ c₂ p₂ m₂ : ℕ} {S : Finset ℕ}
    (hb_lo : x + 1 ≤ b) (hb_hi : b ≤ coverHi4 x)
    (hx₁ : x = c₁ * p₁) (hx₂ : x + 1 = c₂ * p₂)
    (hp₁ : Nat.Prime p₁) (hm₁ : m₁ < p₁) (hb₁ : b < (m₁ + 1) * p₁)
    (hno₁ : NoZeroSubsetMod p₁ m₁)
    (hp₂ : Nat.Prime p₂) (hm₂ : m₂ < p₂) (hb₂ : b < (m₂ + 1) * p₂)
    (hno₂ : NoZeroSubsetMod p₂ m₂) :
    ¬ CandidateSet a b S := by
  intro hc
  have hax : a ≤ x := candidateSet_left_le_of_le_coverHi4 hc hb_hi
  exact not_candidateSet_of_forbidden_mul_pair hax hb_lo hx₁ hx₂
    hp₁ hm₁ hb₁ hno₁ hp₂ hm₂ hb₂ hno₂ hc

-- Pre-evaluated small harmonic numerator sums `∑ c ∈ Icc 1 m, lcmIcc m / c` for `m ∈ {2, 3, 4, 6}`:
private lemma sum_lcmIcc_2 : (∑ c ∈ Finset.Icc 1 2, lcmIcc 2 / c) = 3 := by decide
private lemma sum_lcmIcc_3 : (∑ c ∈ Finset.Icc 1 3, lcmIcc 3 / c) = 11 := by decide
private lemma sum_lcmIcc_4 : (∑ c ∈ Finset.Icc 1 4, lcmIcc 4 / c) = 25 := by decide
private lemma sum_lcmIcc_6 : (∑ c ∈ Finset.Icc 1 6, lcmIcc 6 / c) = 147 := by decide

private lemma noZero_gt_2 {p : ℕ} (hp : 3 < p) : NoZeroSubsetMod p 2 :=
  noZeroSubsetMod_of_gt_sum (by rw [sum_lcmIcc_2]; exact hp)

private lemma noZero_gt_3 {p : ℕ} (hp : 11 < p) : NoZeroSubsetMod p 3 :=
  noZeroSubsetMod_of_gt_sum (by rw [sum_lcmIcc_3]; exact hp)

private lemma noZero_gt_4 {p : ℕ} (hp : 25 < p) : NoZeroSubsetMod p 4 :=
  noZeroSubsetMod_of_gt_sum (by rw [sum_lcmIcc_4]; exact hp)

private lemma noZero_gt_6 {p : ℕ} (hp : 147 < p) : NoZeroSubsetMod p 6 :=
  noZeroSubsetMod_of_gt_sum (by rw [sum_lcmIcc_6]; exact hp)

private lemma noZero_7_3 : NoZeroSubsetMod 7 3 := by decide
private lemma noZero_23_4 : NoZeroSubsetMod 23 4 := by decide

/-- Unconditional kernel-verified certificate: no `CandidateSet a b S` exists with `b ≤ 20000`. -/
theorem no_candidateSet_le_20000 {a b : ℕ} {S : Finset ℕ} (hb : b ≤ 20000) :
    ¬ CandidateSet a b S := by
  if hb2 : b ≤ 2 then
    intro hc
    have h1 := hc.two_le_left
    have h2 := hc.lt_endpoints
    omega
  else if hb3 : b = 3 then
    intro hc
    subst hb3
    have hnot : 3 ^ 1 ∉ S :=
      prime_pow_gt_half_not_mem hc.subset_Icc hc.sum_inv_eq_one (by norm_num) (by omega) (by omega)
    exact (by simpa using hnot : 3 ∉ S) hc.right_mem
  else if hb4 : b = 4 then
    intro hc
    subst hb4
    have hnot : 2 ^ 2 ∉ S :=
      prime_pow_gt_half_not_mem hc.subset_Icc hc.sum_inv_eq_one (by norm_num) (by omega) (by omega)
    exact (by simpa using hnot : 4 ∉ S) hc.right_mem
  else if hb5 : b = 5 then
    intro hc
    subst hb5
    have hnot : 5 ^ 1 ∉ S :=
      prime_pow_gt_half_not_mem hc.subset_Icc hc.sum_inv_eq_one (by norm_num) (by omega) (by omega)
    exact (by simpa using hnot : 5 ∉ S) hc.right_mem
  else if hb7 : b ≤ 7 then
    exact kill_range_prime_pow_pair (x := 4) (p₁ := 2) (r₁ := 2) (p₂ := 5) (r₂ := 1)
      (by omega) (le_trans hb7 (by decide : 7 ≤ coverHi4 4)) rfl rfl
      (by norm_num) (by omega) (by omega) (by norm_num) (by omega) (by omega)
  else if hb13 : b ≤ 13 then
    exact kill_range_prime_pow_pair (x := 7) (p₁ := 7) (r₁ := 1) (p₂ := 2) (r₂ := 3)
      (by omega) (le_trans hb13 (by decide : 13 ≤ coverHi4 7)) rfl rfl
      (by norm_num) (by omega) (by omega) (by norm_num) (by omega) (by omega)
  else if hb27 : b ≤ 27 then
    exact kill_range_mul_prime_pair (x := 13) (c₁ := 1) (p₁ := 13) (m₁ := 3)
      (c₂ := 2) (p₂ := 7) (m₂ := 3)
      (by omega) (le_trans hb27 (by decide : 27 ≤ coverHi4 13)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_3 (by omega))
      (by norm_num) (by omega) (by omega) noZero_7_3
  else if hb31 : b ≤ 31 then
    exact kill_range_mul_prime_pair (x := 22) (c₁ := 2) (p₁ := 11) (m₁ := 2)
      (c₂ := 1) (p₂ := 23) (m₂ := 4)
      (by omega) (le_trans hb31 (by decide : 31 ≤ coverHi4 22)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_2 (by omega))
      (by norm_num) (by omega) (by omega) noZero_23_4
  else if hb61 : b ≤ 61 then
    exact kill_range_prime_pow_pair (x := 31) (p₁ := 31) (r₁ := 1) (p₂ := 2) (r₂ := 5)
      (by omega) (le_trans hb61 (by decide : 61 ≤ coverHi4 31)) rfl rfl
      (by norm_num) (by omega) (by omega) (by norm_num) (by omega) (by omega)
  else if hb75 : b ≤ 75 then
    exact kill_range_mul_prime_pair (x := 37) (c₁ := 1) (p₁ := 37) (m₁ := 2)
      (c₂ := 2) (p₂ := 19) (m₂ := 3)
      (by omega) (le_trans hb75 (by decide : 75 ≤ coverHi4 37)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_2 (by omega))
      (by norm_num) (by omega) (by omega) (noZero_gt_3 (by omega))
  else if hb176 : b ≤ 176 then
    exact kill_range_mul_prime_pair (x := 73) (c₁ := 1) (p₁ := 73) (m₁ := 2)
      (c₂ := 2) (p₂ := 37) (m₂ := 4)
      (by omega) (le_trans hb176 (by decide : 176 ≤ coverHi4 73)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_2 (by omega))
      (by norm_num) (by omega) (by omega) (noZero_gt_4 (by omega))
  else if hb402 : b ≤ 402 then
    exact kill_range_mul_prime_pair (x := 166) (c₁ := 2) (p₁ := 83) (m₁ := 4)
      (c₂ := 1) (p₂ := 167) (m₂ := 2)
      (by omega) (le_trans hb402 (by decide : 402 ≤ coverHi4 166)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_4 (by omega))
      (by norm_num) (by omega) (by omega) (noZero_gt_2 (by omega))
  else if hb968 : b ≤ 968 then
    exact kill_range_mul_prime_pair (x := 397) (c₁ := 1) (p₁ := 397) (m₁ := 2)
      (c₂ := 2) (p₂ := 199) (m₂ := 4)
      (by omega) (le_trans hb968 (by decide : 968 ≤ coverHi4 397)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_2 (by omega))
      (by norm_num) (by omega) (by omega) (noZero_gt_4 (by omega))
  else if hb2176 : b ≤ 2176 then
    exact kill_range_mul_prime_pair (x := 933) (c₁ := 3) (p₁ := 311) (m₁ := 6)
      (c₂ := 2) (p₂ := 467) (m₂ := 4)
      (by omega) (le_trans hb2176 (by decide : 2176 ≤ coverHi4 933)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_6 (by omega))
      (by norm_num) (by omega) (by omega) (noZero_gt_4 (by omega))
  else if hb5215 : b ≤ 5215 then
    exact kill_range_mul_prime_pair (x := 2137) (c₁ := 1) (p₁ := 2137) (m₁ := 2)
      (c₂ := 2) (p₂ := 1069) (m₂ := 4)
      (by omega) (le_trans hb5215 (by decide : 5215 ≤ coverHi4 2137)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_2 (by omega))
      (by norm_num) (by omega) (by omega) (noZero_gt_4 (by omega))
  else if hb12481 : b ≤ 12481 then
    exact kill_range_mul_prime_pair (x := 5113) (c₁ := 1) (p₁ := 5113) (m₁ := 2)
      (c₂ := 2) (p₂ := 2557) (m₂ := 4)
      (by omega) (le_trans hb12481 (by decide : 12481 ≤ coverHi4 5113)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_2 (by omega))
      (by norm_num) (by omega) (by omega) (noZero_gt_4 (by omega))
  else
    exact kill_range_mul_prime_pair (x := 12457) (c₁ := 1) (p₁ := 12457) (m₁ := 2)
      (c₂ := 2) (p₂ := 6229) (m₂ := 4)
      (by omega) (le_trans hb (by decide : 20000 ≤ coverHi4 12457)) rfl rfl
      (by norm_num) (by omega) (by omega) (noZero_gt_2 (by omega))
      (by norm_num) (by omega) (by omega) (noZero_gt_4 (by omega))

/-- Unconditional formal verification of Erdős Problem #287 for all sequences with maximum
denominator at most `20,000`. -/
theorem erdos_287_upto_20000 :
    ∀ (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ),
      StrictMono s →
      1 < s ⟨0, by omega⟩ →
      s ⟨k - 1, by omega⟩ ≤ 20000 →
      (∑ i : Fin k, (1 : ℝ) / (s i : ℝ)) = 1 →
      3 ≤ max_gap k s := by
  intro k hk s hs hs0 hb20k hsum
  by_contra hgap
  have hgap_le : max_gap k s ≤ 2 := by omega
  let a := s ⟨0, by omega⟩
  let b := s ⟨k - 1, by omega⟩
  let S := Finset.image s Finset.univ
  have hab : a < b := hs (Fin.mk_lt_mk.mpr (by omega))
  refine no_candidateSet_le_20000 (a := a) (b := b) (S := S) hb20k
    ⟨by omega, hab, image_subset_Icc_of_strictMono hk hs, ?_, ?_,
      sum_image_inv_rat_eq_one hs hsum, ?_⟩
  · exact Finset.mem_image_of_mem s (Finset.mem_univ _)
  · exact Finset.mem_image_of_mem s (Finset.mem_univ _)
  · intro x hax hxb
    obtain ⟨m, hle, hlt⟩ := exists_consecutive_bracket hk hs hax hxb
    have hstep_le : s ⟨m.val + 1, by omega⟩ - s ⟨m.val, by omega⟩ ≤ max_gap k s := by
      unfold max_gap
      exact Finset.le_sup (f := fun i : Fin (k - 1) =>
        s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩) (Finset.mem_univ m)
    have hdiff : s ⟨m.val + 1, by omega⟩ - s ⟨m.val, by omega⟩ ≤ 2 :=
      le_trans hstep_le hgap_le
    have hor : x = s ⟨m.val, by omega⟩ ∨ x + 1 = s ⟨m.val + 1, by omega⟩ := by omega
    rcases hor with hx0 | hx1
    · left
      rw [hx0]
      exact Finset.mem_image_of_mem s (Finset.mem_univ _)
    · right
      rw [hx1]
      exact Finset.mem_image_of_mem s (Finset.mem_univ _)

end Erdos287

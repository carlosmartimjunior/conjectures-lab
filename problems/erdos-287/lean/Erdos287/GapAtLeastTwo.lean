import Erdos287.PadicObstruction

namespace Erdos287

/-!
# Maximum Gap at Least Two (Kürschák, 1918)

Unconditional formal proof that any strictly increasing sequence `1 < s 0 < ⋯ < s (k - 1)` (`k ≥ 2`)
with `∑ 1 / s i = 1` has maximum consecutive gap at least `2`, i.e. no interval `[a, b]` (`2 ≤ a < b`)
of consecutive integers can have reciprocals summing to `1`.
-/

/-- Kürschák's theorem (1918): the reciprocals of a nontrivial block `[a, b]` (`2 ≤ a < b`) of
consecutive positive integers never sum to `1`. -/
theorem sum_Icc_inv_ne_one {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    (∑ x ∈ Finset.Icc a b, (1 : ℚ) / (x : ℚ)) ≠ 1 := by
  intro hsum
  let E := (Finset.Icc 1 b).filter (fun r => ∃ x ∈ Finset.Icc a b, 2 ^ r ∣ x)
  have h1_mem : 1 ∈ E := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    by_cases heven : 2 ∣ a
    · exact ⟨a, Finset.mem_Icc.mpr ⟨le_refl a, le_of_lt hab⟩, by simpa using heven⟩
    · refine ⟨a + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      simp only [pow_one]
      omega
  let r := E.max' ⟨1, h1_mem⟩
  have hr_mem : r ∈ E := Finset.max'_mem E ⟨1, h1_mem⟩
  have hr_ge : 1 ≤ r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr_mem).1).1
  obtain ⟨x₀, hx₀_mem, hx₀_dvd⟩ := (Finset.mem_filter.mp hr_mem).2
  have hno_succ : ∀ z ∈ Finset.Icc a b, ¬ (2 ^ (r + 1) ∣ z) := by
    intro z hz hdvd
    have hz_ge : 2 ≤ z := le_trans ha (Finset.mem_Icc.mp hz).1
    have hzb : z ≤ b := (Finset.mem_Icc.mp hz).2
    have hpow_le_z : 2 ^ (r + 1) ≤ z := Nat.le_of_dvd (by omega) hdvd
    have hr_lt_pow : r + 1 < 2 ^ (r + 1) := Nat.lt_two_pow_self
    have hr1_mem : r + 1 ∈ E :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨z, hz, hdvd⟩⟩
    have hr1_le : r + 1 ≤ r := Finset.le_max' E (r + 1) hr1_mem
    omega
  have hx₀_ne : x₀ ≠ 0 := by
    have := (Finset.mem_Icc.mp hx₀_mem).1
    omega
  refine not_mem_of_unique_prime_pow_dvd hsum hx₀_ne Nat.prime_two hr_ge hx₀_dvd ?_ hx₀_mem
  intro y hy_mem hy_ne hy_dvd
  rcases hx₀_dvd with ⟨u, hx₀_eq⟩
  rcases hy_dvd with ⟨v, hy_eq⟩
  have hu_odd : ¬ (2 ∣ u) := by
    intro h2u
    apply hno_succ x₀ hx₀_mem
    rw [hx₀_eq, pow_succ]
    exact mul_dvd_mul_left (2 ^ r) h2u
  have hv_odd : ¬ (2 ∣ v) := by
    intro h2v
    apply hno_succ y hy_mem
    rw [hy_eq, pow_succ]
    exact mul_dvd_mul_left (2 ^ r) h2v
  have huv_ne : u ≠ v := by
    intro huv
    apply hy_ne
    rw [hy_eq, hx₀_eq, huv]
  have hpow_pos : 0 < 2 ^ r := pow_pos (by decide) r
  rcases lt_or_gt_of_ne huv_ne with hlt | hgt
  · let z := 2 ^ r * (u + 1)
    have hz_mem : z ∈ Finset.Icc a b := by
      have hx₀Icc := Finset.mem_Icc.mp hx₀_mem
      have hyIcc := Finset.mem_Icc.mp hy_mem
      have hle1 : 2 ^ r * u ≤ 2 ^ r * (u + 1) := Nat.mul_le_mul_left (2 ^ r) (by omega)
      have hle2 : 2 ^ r * (u + 1) ≤ 2 ^ r * v := Nat.mul_le_mul_left (2 ^ r) (by omega)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hz_dvd : 2 ^ (r + 1) ∣ z := by
      have h2_u1 : 2 ∣ (u + 1) := by omega
      rw [pow_succ]
      exact mul_dvd_mul_left (2 ^ r) h2_u1
    exact hno_succ z hz_mem hz_dvd
  · let z := 2 ^ r * (v + 1)
    have hz_mem : z ∈ Finset.Icc a b := by
      have hx₀Icc := Finset.mem_Icc.mp hx₀_mem
      have hyIcc := Finset.mem_Icc.mp hy_mem
      have hle1 : 2 ^ r * v ≤ 2 ^ r * (v + 1) := Nat.mul_le_mul_left (2 ^ r) (by omega)
      have hle2 : 2 ^ r * (v + 1) ≤ 2 ^ r * u := Nat.mul_le_mul_left (2 ^ r) (by omega)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hz_dvd : 2 ^ (r + 1) ∣ z := by
      have h2_v1 : 2 ∣ (v + 1) := by omega
      rw [pow_succ]
      exact mul_dvd_mul_left (2 ^ r) h2_v1
    exact hno_succ z hz_mem hz_dvd

/-- Unconditional lower bound `2 ≤ max_gap k s` for Erdős #287. -/
theorem erdos_287_gap_at_least_two :
    ∀ (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ),
      StrictMono s →
      1 < s ⟨0, by omega⟩ →
      (∑ i : Fin k, (1 : ℝ) / (s i : ℝ)) = 1 →
      2 ≤ max_gap k s := by
  intro k hk s hs hs0 hsum
  by_contra hgap
  have hgap_le : max_gap k s ≤ 1 := by omega
  let a := s ⟨0, by omega⟩
  let b := s ⟨k - 1, by omega⟩
  let S := Finset.image s Finset.univ
  have hab : a < b := hs (Fin.mk_lt_mk.mpr (by omega))
  have hS_eq : S = Finset.Icc a b := by
    refine Finset.Subset.antisymm (image_subset_Icc_of_strictMono hk hs) ?_
    intro x hx
    rcases Finset.mem_Icc.mp hx with ⟨hax, hxb⟩
    rcases lt_or_eq_of_le hxb with hlt | rfl
    · obtain ⟨m, hm_le, hm_lt⟩ := exists_consecutive_bracket hk hs hax hlt
      have hstep_le : s ⟨m.val + 1, by omega⟩ - s ⟨m.val, by omega⟩ ≤ max_gap k s := by
        unfold max_gap
        exact Finset.le_sup (f := fun i : Fin (k - 1) =>
          s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩) (Finset.mem_univ m)
      have hdiff : s ⟨m.val + 1, by omega⟩ - s ⟨m.val, by omega⟩ ≤ 1 :=
        le_trans hstep_le hgap_le
      have hx_eq : x = s ⟨m.val, by omega⟩ := by omega
      rw [hx_eq]
      exact Finset.mem_image_of_mem s (Finset.mem_univ _)
    · exact Finset.mem_image_of_mem s (Finset.mem_univ _)
  have hsum_rat : (∑ x ∈ Finset.Icc a b, (1 : ℚ) / (x : ℚ)) = 1 := by
    rw [← hS_eq]
    exact sum_image_inv_rat_eq_one hs hsum
  exact sum_Icc_inv_ne_one (by omega) hab hsum_rat

end Erdos287

import Erdos287.Defs

namespace Erdos287

/-!
# p-adic / LCM Obstruction Lemmas for Erdős #287

Elementary `ℕ`/`ℚ` divisibility criteria (clearing denominators by `Finset.lcm`) that forbid
unique multiples of prime powers `p ^ r` and all multiples `c * p` when `NoZeroSubsetMod p m`
holds, without appealing to `ℚ_[p]`.
-/

private lemma exists_coprime_of_not_prime_pow_dvd {p : ℕ} (hp : Nat.Prime p) :
    ∀ {k u : ℕ}, u ≠ 0 → ¬ (p ^ (k + 1) ∣ u) → ∃ m : ℕ, ¬ (p ∣ m) ∧ u ∣ p ^ k * m
  | 0, u, _, hnot => ⟨u, by simpa using hnot, by simp⟩
  | k + 1, u, hu, hnot => by
      by_cases hpu : p ∣ u
      · rcases hpu with ⟨u', rfl⟩
        have hu' : u' ≠ 0 := right_ne_zero_of_mul hu
        have hnot' : ¬ (p ^ (k + 1) ∣ u') := by
          intro h
          apply hnot
          rw [pow_succ']
          exact mul_dvd_mul_left p h
        obtain ⟨m, hpm, hdvd⟩ := exists_coprime_of_not_prime_pow_dvd hp hu' hnot'
        refine ⟨m, hpm, ?_⟩
        rw [pow_succ', mul_assoc]
        exact mul_dvd_mul_left p hdvd
      · exact ⟨u, hpu, dvd_mul_of_dvd_right (dvd_refl u) (p ^ (k + 1))⟩

private lemma prime_not_dvd_finset_prod {α : Type*} {A : Finset α} {g : α → ℕ} {p : ℕ}
    (hp : Nat.Prime p) (h : ∀ y ∈ A, ¬ (p ∣ g y)) :
    ¬ (p ∣ ∏ y ∈ A, g y) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      exact hp.not_dvd_one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with hpa | hps
      · exact h a (Finset.mem_insert_self a s) hpa
      · exact ih (fun y hy => h y (Finset.mem_insert_of_mem hy)) hps

/-- If a prime power `p ^ r` (`r ≥ 1`) divides `A.lcm f`, then `p ^ r` divides `f y`
for at least one `y ∈ A`. -/
lemma prime_pow_dvd_finset_lcm {α : Type*} {A : Finset α} {f : α → ℕ} {p r : ℕ}
    (hp : Nat.Prime p) (hr : 1 ≤ r) (hdvd : p ^ r ∣ A.lcm f) :
    ∃ y ∈ A, p ^ r ∣ f y := by
  by_contra hnone
  simp only [not_exists, not_and] at hnone
  have hr_eq : (r - 1) + 1 = r := by omega
  have hex : ∀ y : {y // y ∈ A}, ∃ m : ℕ, ¬ (p ∣ m) ∧ f y.1 ∣ p ^ (r - 1) * m := by
    rintro ⟨y, hy⟩
    have hfy : f y ≠ 0 := by
      intro h0
      apply hnone y hy
      rw [h0]
      exact dvd_zero (p ^ r)
    have hnot : ¬ (p ^ ((r - 1) + 1) ∣ f y) := by
      rw [hr_eq]
      exact hnone y hy
    exact exists_coprime_of_not_prime_pow_dvd hp hfy hnot
  choose m hm_ndvd hm_dvd using hex
  let P : ℕ := ∏ y : {y // y ∈ A}, m y
  have hlcm_dvd : A.lcm f ∣ p ^ (r - 1) * P := by
    refine Finset.lcm_dvd ?_
    intro y hy
    have hm_dvd_P : m ⟨y, hy⟩ ∣ P :=
      Finset.dvd_prod_of_mem m (Finset.mem_univ (⟨y, hy⟩ : {y // y ∈ A}))
    exact dvd_trans (hm_dvd ⟨y, hy⟩) (mul_dvd_mul_left (p ^ (r - 1)) hm_dvd_P)
  have hpr_dvd : p ^ r ∣ p ^ (r - 1) * P := dvd_trans hdvd hlcm_dvd
  have hmul_dvd : p ^ (r - 1) * p ∣ p ^ (r - 1) * P := by
    rwa [← hr_eq, pow_succ] at hpr_dvd
  have hp_dvd_P : p ∣ P :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos (r - 1)) hmul_dvd
  exact prime_not_dvd_finset_prod hp (fun y _ => hm_ndvd y) hp_dvd_P

private lemma cast_mul_one_div {M y : ℕ} (hy : y ≠ 0) (hdvd : y ∣ M) :
    (M : ℚ) * ((1 : ℚ) / (y : ℚ)) = ((M / y : ℕ) : ℚ) := by
  have hmul : y * (M / y) = M := Nat.mul_div_cancel' hdvd
  have hyq : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy
  calc
    (M : ℚ) * ((1 : ℚ) / (y : ℚ)) = ((y * (M / y) : ℕ) : ℚ) * ((1 : ℚ) / (y : ℚ)) := by rw [hmul]
    _ = ((M / y : ℕ) : ℚ) * ((y : ℚ) / (y : ℚ)) := by push_cast; ring
    _ = ((M / y : ℕ) : ℚ) := by rw [div_self hyq, mul_one]

/-- Unique prime-power divisor obstruction (sum form): if `x₀ ∈ S` (`x₀ ≠ 0`) is divisible by
`p ^ r` (`p` prime, `r ≥ 1`) and no other element of `S` is divisible by `p ^ r`, then
`∑ x ∈ S, 1 / x ≠ 1`. -/
theorem sum_inv_ne_one_of_unique_prime_pow_dvd {S : Finset ℕ} {x₀ p r : ℕ}
    (hx₀_mem : x₀ ∈ S) (hx₀_ne : x₀ ≠ 0) (hp : Nat.Prime p) (hr : 1 ≤ r)
    (hdvd : p ^ r ∣ x₀) (huniq : ∀ y ∈ S, y ≠ x₀ → ¬ (p ^ r ∣ y)) :
    (∑ x ∈ S, (1 : ℚ) / (x : ℚ)) ≠ 1 := by
  intro hsum
  let A := S.erase x₀
  let M : ℕ := A.lcm id
  have hsplit : (1 : ℚ) / (x₀ : ℚ) + ∑ y ∈ A, (1 : ℚ) / (y : ℚ) = 1 :=
    (Finset.add_sum_erase S (fun x : ℕ => (1 : ℚ) / (x : ℚ)) hx₀_mem).trans hsum
  have hy_ne : ∀ y ∈ A, y ≠ 0 := by
    intro y hy h0
    apply huniq y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
    rw [h0]
    exact dvd_zero (p ^ r)
  have hsumM : (M : ℚ) * (∑ y ∈ A, (1 : ℚ) / (y : ℚ)) = ((∑ y ∈ A, M / y : ℕ) : ℚ) := by
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro y hy
    exact cast_mul_one_div (hy_ne y hy) (Finset.dvd_lcm hy)
  have hx₀q : (x₀ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx₀_ne
  have hq : ((M + x₀ * ∑ y ∈ A, M / y : ℕ) : ℚ) = ((x₀ * M : ℕ) : ℚ) := by
    simp only [Nat.cast_add, Nat.cast_mul]
    calc
      (M : ℚ) + (x₀ : ℚ) * ((∑ y ∈ A, M / y : ℕ) : ℚ)
          = (M : ℚ) * ((x₀ : ℚ) * ((1 : ℚ) / (x₀ : ℚ))) +
            (x₀ : ℚ) * ((M : ℚ) * ∑ y ∈ A, (1 : ℚ) / (y : ℚ)) := by
              rw [mul_one_div_cancel hx₀q, mul_one, hsumM]
      _ = (x₀ : ℚ) * (M : ℚ) * ((1 : ℚ) / (x₀ : ℚ) + ∑ y ∈ A, (1 : ℚ) / (y : ℚ)) := by ring
      _ = (x₀ : ℚ) * (M : ℚ) := by rw [hsplit, mul_one]
  have hnat : M + x₀ * ∑ y ∈ A, M / y = x₀ * M := Nat.cast_injective hq
  have hx₀_dvd_M : x₀ ∣ M :=
    ⟨M - ∑ y ∈ A, M / y, by rw [Nat.mul_sub_left_distrib]; omega⟩
  have hpr_dvd_M : p ^ r ∣ M := dvd_trans hdvd hx₀_dvd_M
  obtain ⟨y, hyA, hpr_y⟩ := prime_pow_dvd_finset_lcm hp hr hpr_dvd_M
  exact huniq y (Finset.mem_of_mem_erase hyA) (Finset.ne_of_mem_erase hyA) hpr_y

/-- Unique prime-power divisor obstruction (membership form): if `∑ x ∈ S, 1 / x = 1` and no
element `y ∈ S` with `y ≠ x₀` is divisible by `p ^ r`, then `x₀ ∉ S`. -/
theorem not_mem_of_unique_prime_pow_dvd {S : Finset ℕ} {x₀ p r : ℕ}
    (hsum : (∑ x ∈ S, (1 : ℚ) / (x : ℚ)) = 1) (hx₀_ne : x₀ ≠ 0)
    (hp : Nat.Prime p) (hr : 1 ≤ r) (hdvd : p ^ r ∣ x₀)
    (huniq : ∀ y ∈ S, y ≠ x₀ → ¬ (p ^ r ∣ y)) :
    x₀ ∉ S := by
  intro hx₀_mem
  exact sum_inv_ne_one_of_unique_prime_pow_dvd hx₀_mem hx₀_ne hp hr hdvd huniq hsum

/-- Immediate corollary: any prime power `p ^ r > b / 2` (i.e. `b < 2 * p ^ r`) is excluded from
any subset `S ⊆ [a, b]` whose reciprocals sum to `1`. -/
theorem prime_pow_gt_half_not_mem {a b : ℕ} {S : Finset ℕ} {p r : ℕ}
    (hsub : S ⊆ Finset.Icc a b) (hsum : (∑ x ∈ S, (1 : ℚ) / (x : ℚ)) = 1)
    (hp : Nat.Prime p) (hr : 1 ≤ r) (hb : b < 2 * p ^ r) :
    p ^ r ∉ S := by
  intro hmem
  have hpr_pos : 0 < p ^ r := pow_pos hp.pos r
  let S₀ := S.erase 0
  have hsum₀ : (∑ x ∈ S₀, (1 : ℚ) / (x : ℚ)) = 1 := by
    by_cases h0 : 0 ∈ S
    · have hadd := Finset.add_sum_erase S (fun x : ℕ => (1 : ℚ) / (x : ℚ)) h0
      simp only [Nat.cast_zero, div_zero, zero_add] at hadd
      exact hadd.trans hsum
    · have herase : S₀ = S := by
        ext z
        simp only [S₀, Finset.mem_erase]
        exact ⟨fun h => h.2, fun hz => ⟨by rintro rfl; exact h0 hz, hz⟩⟩
      rwa [herase]
  have hmem₀ : p ^ r ∈ S₀ := Finset.mem_erase.mpr ⟨by omega, hmem⟩
  refine not_mem_of_unique_prime_pow_dvd hsum₀ (by omega) hp hr (dvd_refl _) ?_ hmem₀
  intro y hy₀ hy_ne hdvd
  have hy_ne0 : y ≠ 0 := (Finset.mem_erase.mp hy₀).1
  have hyS : y ∈ S := (Finset.mem_erase.mp hy₀).2
  have hy_le : y ≤ b := (Finset.mem_Icc.mp (hsub hyS)).2
  rcases hdvd with ⟨k, rfl⟩
  have hk0 : k ≠ 0 := right_ne_zero_of_mul hy_ne0
  have hk1 : k ≠ 1 := by
    intro hk
    apply hy_ne
    rw [hk, mul_one]
  have hk2 : 2 ≤ k := by omega
  have hge : 2 * p ^ r ≤ p ^ r * k := by
    calc
      2 * p ^ r = p ^ r * 2 := mul_comm 2 (p ^ r)
      _ ≤ p ^ r * k := Nat.mul_le_mul_left (p ^ r) hk2
  omega

/-- Least common multiple of `{1, 2, ..., m}`. -/
def lcmIcc (m : ℕ) : ℕ :=
  (Finset.Icc 1 m).lcm id

/-- Decidable predicate asserting that no nonempty subset `C ⊆ {1, ..., m}` has partial harmonic
numerator `∑ c ∈ C, lcmIcc m / c` divisible by `p`. -/
def NoZeroSubsetMod (p m : ℕ) : Prop :=
  ∀ C ∈ (Finset.Icc 1 m).powerset, C.Nonempty → ¬ (p ∣ ∑ c ∈ C, lcmIcc m / c)

instance instDecidableNoZeroSubsetMod (p m : ℕ) : Decidable (NoZeroSubsetMod p m) := by
  unfold NoZeroSubsetMod
  infer_instance

private lemma finset_prod_pos_nat {α : Type*} (A : Finset α) (f : α → ℕ)
    (hpos : ∀ c ∈ A, 0 < f c) : 0 < ∏ c ∈ A, f c := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact Nat.mul_pos (hpos a (Finset.mem_insert_self a s))
        (ih (fun c hc => hpos c (Finset.mem_insert_of_mem hc)))

private lemma finset_single_le_sum_nat {α : Type*} {A : Finset α} (f : α → ℕ) {c₀ : α}
    (hc₀ : c₀ ∈ A) : f c₀ ≤ ∑ c ∈ A, f c := by
  classical
  have h := Finset.add_sum_erase A f hc₀
  omega

private lemma finset_sum_le_sum_of_subset_nat {α : Type*} {C B : Finset α} (f : α → ℕ)
    (hsub : C ⊆ B) : (∑ c ∈ C, f c) ≤ ∑ c ∈ B, f c := by
  classical
  induction C using Finset.induction_on generalizing B with
  | empty => exact Nat.zero_le _
  | @insert a s ha ih =>
      have haB : a ∈ B := hsub (Finset.mem_insert_self a s)
      have hsB : s ⊆ B.erase a := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨by rintro rfl; exact ha hx, hsub (Finset.mem_insert_of_mem hx)⟩
      have hle := ih hsB
      have hB := Finset.add_sum_erase B f haB
      rw [Finset.sum_insert ha]
      omega

lemma lcmIcc_pos (m : ℕ) : 0 < lcmIcc m := by
  have hprod_pos : 0 < ∏ c ∈ Finset.Icc 1 m, c := by
    refine finset_prod_pos_nat (Finset.Icc 1 m) (fun c => c) ?_
    intro c hc
    have := (Finset.mem_Icc.mp hc).1
    omega
  have hdvd : lcmIcc m ∣ ∏ c ∈ Finset.Icc 1 m, c := by
    unfold lcmIcc
    refine Finset.lcm_dvd ?_
    intro c hc
    exact Finset.dvd_prod_of_mem id hc
  exact Nat.pos_of_dvd_of_pos hdvd hprod_pos

/-- Sufficient criterion for `NoZeroSubsetMod p m`: if `p` exceeds the full harmonic numerator
`∑ c ∈ Icc 1 m, lcmIcc m / c`, then no nonempty subset sum can be divisible by `p`. -/
theorem noZeroSubsetMod_of_gt_sum {p m : ℕ}
    (hp : (∑ c ∈ Finset.Icc 1 m, lcmIcc m / c) < p) :
    NoZeroSubsetMod p m := by
  intro C hC_pow hC_ne hdvd
  have hC_sub : C ⊆ Finset.Icc 1 m := Finset.mem_powerset.mp hC_pow
  rcases hC_ne with ⟨c₀, hc₀⟩
  have hc₀_mem : c₀ ∈ Finset.Icc 1 m := hC_sub hc₀
  have hc₀_pos : 0 < c₀ := by
    have := (Finset.mem_Icc.mp hc₀_mem).1
    omega
  have hc₀_dvd : c₀ ∣ lcmIcc m := Finset.dvd_lcm hc₀_mem
  have hc₀_le : c₀ ≤ lcmIcc m := Nat.le_of_dvd (lcmIcc_pos m) hc₀_dvd
  have hterm_pos : 0 < lcmIcc m / c₀ := Nat.div_pos hc₀_le hc₀_pos
  have hsum_pos : 0 < ∑ c ∈ C, lcmIcc m / c := by
    have hle : lcmIcc m / c₀ ≤ ∑ c ∈ C, lcmIcc m / c :=
      finset_single_le_sum_nat (fun c => lcmIcc m / c) hc₀
    omega
  have hsum_le : (∑ c ∈ C, lcmIcc m / c) ≤ ∑ c ∈ Finset.Icc 1 m, lcmIcc m / c :=
    finset_sum_le_sum_of_subset_nat (fun c => lcmIcc m / c) hC_sub
  have hp_le : p ≤ ∑ c ∈ C, lcmIcc m / c := Nat.le_of_dvd hsum_pos hdvd
  omega

/-- General multiple-exclusion theorem: if `S ⊆ [a, b]` (`1 ≤ a`), `∑ x ∈ S, 1 / x = 1`,
`p` is prime with `m < p`, `b < (m + 1) * p`, and `NoZeroSubsetMod p m` holds, then `p` divides
no element of `S`. -/
theorem multiples_not_mem_of_no_zero_subset_mod {a b p m : ℕ} {S : Finset ℕ}
    (ha : 1 ≤ a) (hsub : S ⊆ Finset.Icc a b)
    (hsum : (∑ x ∈ S, (1 : ℚ) / (x : ℚ)) = 1)
    (hp : Nat.Prime p) (hmp : m < p) (hb : b < (m + 1) * p)
    (hno : NoZeroSubsetMod p m) :
    ∀ x ∈ S, ¬ (p ∣ x) := by
  intro x₀ hx₀S hpx₀
  let Sp := S.filter (fun x => p ∣ x)
  let S' := S.filter (fun x => ¬ (p ∣ x))
  have hsplit :
      (∑ x ∈ Sp, (1 : ℚ) / (x : ℚ)) + (∑ y ∈ S', (1 : ℚ) / (y : ℚ)) = 1 :=
    (Finset.sum_filter_add_sum_filter_not S (fun x => p ∣ x) (fun x : ℕ => (1 : ℚ) / (x : ℚ))).trans hsum
  let C := Sp.image (fun x => x / p)
  have hx₀_Sp : x₀ ∈ Sp := Finset.mem_filter.mpr ⟨hx₀S, hpx₀⟩
  have hC_ne : C.Nonempty := ⟨x₀ / p, Finset.mem_image_of_mem _ hx₀_Sp⟩
  have hC_sub : C ⊆ Finset.Icc 1 m := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨x, hxSp, rfl⟩
    have hxS : x ∈ S := (Finset.mem_filter.mp hxSp).1
    have hpx : p ∣ x := (Finset.mem_filter.mp hxSp).2
    have hxIcc := Finset.mem_Icc.mp (hsub hxS)
    have hmul : (x / p) * p = x := Nat.div_mul_cancel hpx
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (x / p) with hxp0 | hpos
      · rw [hxp0, zero_mul] at hmul
        omega
      · exact hpos
    · have hlt : (x / p) * p < (m + 1) * p := by omega
      have hlt' : x / p < m + 1 := (Nat.mul_lt_mul_right hp.pos).mp hlt
      omega
  have hSp_eq : Sp = C.image (fun c => c * p) := by
    ext x
    simp only [C, Finset.mem_image]
    constructor
    · intro hxSp
      have hpx : p ∣ x := (Finset.mem_filter.mp hxSp).2
      exact ⟨x / p, ⟨x, hxSp, rfl⟩, Nat.div_mul_cancel hpx⟩
    · rintro ⟨c, ⟨y, hySp, rfl⟩, rfl⟩
      have hpy : p ∣ y := (Finset.mem_filter.mp hySp).2
      rwa [Nat.div_mul_cancel hpy]
  have hsum_Sp :
      (∑ x ∈ Sp, (1 : ℚ) / (x : ℚ)) = ∑ c ∈ C, (1 : ℚ) / ((c * p : ℕ) : ℚ) := by
    rw [hSp_eq, Finset.sum_image]
    intro c₁ _ c₂ _ heq
    exact mul_right_cancel₀ hp.ne_zero heq
  let L : ℕ := lcmIcc m
  let M' : ℕ := S'.lcm id
  have hp_ndvd_L : ¬ (p ∣ L) := by
    intro hdvd
    have hdvd1 : p ^ 1 ∣ L := by simpa using hdvd
    obtain ⟨c, hc, hpc⟩ := prime_pow_dvd_finset_lcm hp (le_refl 1) hdvd1
    simp only [pow_one, id_eq] at hpc
    have hcIcc := Finset.mem_Icc.mp hc
    have hp_le_c : p ≤ c := Nat.le_of_dvd (by omega) hpc
    omega
  have hp_ndvd_M' : ¬ (p ∣ M') := by
    intro hdvd
    have hdvd1 : p ^ 1 ∣ M' := by simpa using hdvd
    obtain ⟨y, hy, hpy⟩ := prime_pow_dvd_finset_lcm hp (le_refl 1) hdvd1
    simp only [pow_one, id_eq] at hpy
    exact (Finset.mem_filter.mp hy).2 hpy
  have hterm_p : ∀ c ∈ C,
      ((p * L * M' : ℕ) : ℚ) * ((1 : ℚ) / ((c * p : ℕ) : ℚ)) = ((M' * (L / c) : ℕ) : ℚ) := by
    intro c hc
    have hc_mem : c ∈ Finset.Icc 1 m := hC_sub hc
    have hc_ne : c ≠ 0 := by
      have := (Finset.mem_Icc.mp hc_mem).1
      omega
    have hmul : c * (L / c) = L := Nat.mul_div_cancel' (Finset.dvd_lcm hc_mem)
    have hcpq : ((c * p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (mul_ne_zero hc_ne hp.ne_zero)
    calc
      ((p * L * M' : ℕ) : ℚ) * ((1 : ℚ) / ((c * p : ℕ) : ℚ))
          = ((p * (c * (L / c)) * M' : ℕ) : ℚ) * ((1 : ℚ) / ((c * p : ℕ) : ℚ)) := by rw [hmul]
      _ = ((M' * (L / c) : ℕ) : ℚ) * (((c * p : ℕ) : ℚ) / ((c * p : ℕ) : ℚ)) := by
            push_cast; ring
      _ = ((M' * (L / c) : ℕ) : ℚ) := by rw [div_self hcpq, mul_one]
  have hterm_s : ∀ y ∈ S',
      ((p * L * M' : ℕ) : ℚ) * ((1 : ℚ) / (y : ℚ)) = ((p * L * (M' / y) : ℕ) : ℚ) := by
    intro y hy
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hy_ne : y ≠ 0 := by
      have := (Finset.mem_Icc.mp (hsub hyS)).1
      omega
    have hmul : y * (M' / y) = M' := Nat.mul_div_cancel' (Finset.dvd_lcm hy)
    have hyq : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy_ne
    calc
      ((p * L * M' : ℕ) : ℚ) * ((1 : ℚ) / (y : ℚ))
          = ((p * L * (y * (M' / y)) : ℕ) : ℚ) * ((1 : ℚ) / (y : ℚ)) := by rw [hmul]
      _ = ((p * L * (M' / y) : ℕ) : ℚ) * ((y : ℚ) / (y : ℚ)) := by push_cast; ring
      _ = ((p * L * (M' / y) : ℕ) : ℚ) := by rw [div_self hyq, mul_one]
  have hq :
      ((M' * (∑ c ∈ C, L / c) + p * (L * ∑ y ∈ S', M' / y) : ℕ) : ℚ) =
      ((p * (L * M') : ℕ) : ℚ) := by
    have hsum1 :
        ((p * L * M' : ℕ) : ℚ) * (∑ c ∈ C, (1 : ℚ) / ((c * p : ℕ) : ℚ)) =
        ((M' * ∑ c ∈ C, L / c : ℕ) : ℚ) := by
      rw [Finset.mul_sum]
      have hrhs : ((M' * ∑ c ∈ C, L / c : ℕ) : ℚ) = ∑ c ∈ C, ((M' * (L / c) : ℕ) : ℚ) := by
        rw [Finset.mul_sum, Nat.cast_sum]
      rw [hrhs]
      exact Finset.sum_congr rfl (fun c hc => hterm_p c hc)
    have hsum2 :
        ((p * L * M' : ℕ) : ℚ) * (∑ y ∈ S', (1 : ℚ) / (y : ℚ)) =
        ((p * (L * ∑ y ∈ S', M' / y) : ℕ) : ℚ) := by
      rw [Finset.mul_sum]
      have hrhs : ((p * (L * ∑ y ∈ S', M' / y) : ℕ) : ℚ) = ∑ y ∈ S', ((p * L * (M' / y) : ℕ) : ℚ) := by
        have hmul_sum : p * (L * ∑ y ∈ S', M' / y) = ∑ y ∈ S', p * L * (M' / y) := by
          rw [← mul_assoc, Finset.mul_sum]
        rw [hmul_sum, Nat.cast_sum]
      rw [hrhs]
      exact Finset.sum_congr rfl (fun y hy => hterm_s y hy)
    calc
      ((M' * (∑ c ∈ C, L / c) + p * (L * ∑ y ∈ S', M' / y) : ℕ) : ℚ)
          = ((M' * ∑ c ∈ C, L / c : ℕ) : ℚ) + ((p * (L * ∑ y ∈ S', M' / y) : ℕ) : ℚ) := by
              push_cast; rfl
      _ = ((p * L * M' : ℕ) : ℚ) *
            ((∑ c ∈ C, (1 : ℚ) / ((c * p : ℕ) : ℚ)) + (∑ y ∈ S', (1 : ℚ) / (y : ℚ))) := by
              rw [← hsum1, ← hsum2, mul_add]
      _ = ((p * L * M' : ℕ) : ℚ) * 1 := by rw [← hsum_Sp, hsplit]
      _ = ((p * (L * M') : ℕ) : ℚ) := by push_cast; ring
  have hnat : M' * (∑ c ∈ C, L / c) + p * (L * ∑ y ∈ S', M' / y) = p * (L * M') :=
    Nat.cast_injective hq
  have hp_dvd_prod : p ∣ M' * (∑ c ∈ C, L / c) :=
    ⟨L * M' - L * ∑ y ∈ S', M' / y, by rw [Nat.mul_sub_left_distrib]; omega⟩
  have hp_dvd_sum : p ∣ ∑ c ∈ C, L / c :=
    (hp.dvd_mul.mp hp_dvd_prod).resolve_left hp_ndvd_M'
  exact hno C (Finset.mem_powerset.mpr hC_sub) hC_ne hp_dvd_sum

/-- Corollary: under the hypotheses of `multiples_not_mem_of_no_zero_subset_mod`, no multiple
`c * p` belongs to `S`. -/
theorem mul_prime_not_mem_of_no_zero_subset_mod {a b p m : ℕ} {S : Finset ℕ}
    (ha : 1 ≤ a) (hsub : S ⊆ Finset.Icc a b)
    (hsum : (∑ x ∈ S, (1 : ℚ) / (x : ℚ)) = 1)
    (hp : Nat.Prime p) (hmp : m < p) (hb : b < (m + 1) * p)
    (hno : NoZeroSubsetMod p m) (c : ℕ) :
    c * p ∉ S := by
  intro hmem
  exact multiples_not_mem_of_no_zero_subset_mod ha hsub hsum hp hmp hb hno
    (c * p) hmem (dvd_mul_left p c)

/-- Forced neighbor propagation: in a `CandidateSet a b S`, any omitted interior element
`x ∈ (a, b)` forces both `x - 1 ∈ S` and `x + 1 ∈ S`. -/
lemma neighbors_mem_of_not_mem {a b : ℕ} {S : Finset ℕ} (hc : CandidateSet a b S)
    {x : ℕ} (hax : a < x) (hxb : x < b) (hx : x ∉ S) :
    x - 1 ∈ S ∧ x + 1 ∈ S := by
  have h1 := hc.no_consecutive_missing (x - 1) (by omega) (by omega)
  have hsub_add : x - 1 + 1 = x := by omega
  rw [hsub_add] at h1
  have h2 := hc.no_consecutive_missing x (by omega) hxb
  exact ⟨h1.resolve_right hx, h2.resolve_left hx⟩

/-- Elimination by endpoint or consecutive forbidden pair: a `CandidateSet a b S` is refuted
whenever `a ∉ S`, `b ∉ S`, or there exists `x ∈ [a, b)` with both `x ∉ S` and `x + 1 ∉ S`. -/
theorem not_candidateSet_of_consecutive_forbidden {a b : ℕ} {S : Finset ℕ} {x : ℕ}
    (hforb : (x = a ∧ x ∉ S) ∨ (x = b ∧ x ∉ S) ∨ (a ≤ x ∧ x < b ∧ x ∉ S ∧ x + 1 ∉ S)) :
    ¬ CandidateSet a b S := by
  intro hc
  rcases hforb with ⟨rfl, ha⟩ | ⟨rfl, hb⟩ | ⟨hax, hxb, hx1, hx2⟩
  · exact ha hc.left_mem
  · exact hb hc.right_mem
  · rcases hc.no_consecutive_missing x hax hxb with h | h
    · exact hx1 h
    · exact hx2 h

/-- Wave 2 certificate workhorse: if `[a, b]` contains a consecutive pair `(x, x + 1)` with
`x = c₁ * p₁` and `x + 1 = c₂ * p₂` where both primes satisfy `NoZeroSubsetMod`, then no
`CandidateSet a b S` exists. -/
theorem not_candidateSet_of_forbidden_mul_pair {a b : ℕ} {S : Finset ℕ}
    {x c₁ p₁ m₁ c₂ p₂ m₂ : ℕ}
    (hax : a ≤ x) (hxb : x + 1 ≤ b)
    (hx₁ : x = c₁ * p₁) (hx₂ : x + 1 = c₂ * p₂)
    (hp₁ : Nat.Prime p₁) (hm₁ : m₁ < p₁) (hb₁ : b < (m₁ + 1) * p₁)
    (hno₁ : NoZeroSubsetMod p₁ m₁)
    (hp₂ : Nat.Prime p₂) (hm₂ : m₂ < p₂) (hb₂ : b < (m₂ + 1) * p₂)
    (hno₂ : NoZeroSubsetMod p₂ m₂) :
    ¬ CandidateSet a b S := by
  intro hc
  have ha1 : 1 ≤ a := by
    have := hc.two_le_left
    omega
  have hx_not : x ∉ S := by
    rw [hx₁]
    exact mul_prime_not_mem_of_no_zero_subset_mod ha1 hc.subset_Icc hc.sum_inv_eq_one
      hp₁ hm₁ hb₁ hno₁ c₁
  have hx1_not : x + 1 ∉ S := by
    rw [hx₂]
    exact mul_prime_not_mem_of_no_zero_subset_mod ha1 hc.subset_Icc hc.sum_inv_eq_one
      hp₂ hm₂ hb₂ hno₂ c₂
  exact not_candidateSet_of_consecutive_forbidden
    (Or.inr (Or.inr ⟨hax, by omega, hx_not, hx1_not⟩)) hc

end Erdos287

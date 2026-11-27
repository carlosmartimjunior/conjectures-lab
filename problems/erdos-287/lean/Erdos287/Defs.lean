import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Erdos287

/-- Maximum gap between consecutive terms of `s : Fin k → ℕ`. -/
def max_gap (k : ℕ) (s : Fin k → ℕ) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin (k - 1) => s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/-- Erdős Problem #287 (Erdős–Graham, 1980): for any `k ≥ 2` and strictly increasing integers
`1 < s 0 < s 1 < ⋯ < s (k - 1)` whose reciprocals sum to `1`, the maximum consecutive gap
is at least `3`. -/
def Erdos287Conjecture : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s →
    1 < s ⟨0, by omega⟩ →
    (∑ i : Fin k, (1 : ℝ) / (s i : ℝ)) = 1 →
    3 ≤ max_gap k s

/-- Equivalent `Finset ℕ` counterexample structure: a subset `S ⊆ [a, b]` containing both endpoints
`2 ≤ a < b`, whose reciprocals sum to `1` in `ℚ`, and omitting no two consecutive integers
in `[a, b]` (equivalently, maximum consecutive gap at most `2`). -/
structure CandidateSet (a b : ℕ) (S : Finset ℕ) : Prop where
  two_le_left : 2 ≤ a
  lt_endpoints : a < b
  subset_Icc : S ⊆ Finset.Icc a b
  left_mem : a ∈ S
  right_mem : b ∈ S
  sum_inv_eq_one : (∑ x ∈ S, (1 : ℚ) / (x : ℚ)) = 1
  no_consecutive_missing : ∀ x : ℕ, a ≤ x → x < b → x ∈ S ∨ x + 1 ∈ S

/-- Helper: the image of a strictly increasing sequence `s : Fin k → ℕ` (`k ≥ 2`) lies in
`[s 0, s (k - 1)]`. -/
lemma image_subset_Icc_of_strictMono {k : ℕ} (hk : 2 ≤ k) {s : Fin k → ℕ} (hs : StrictMono s) :
    Finset.image s Finset.univ ⊆ Finset.Icc (s ⟨0, by omega⟩) (s ⟨k - 1, by omega⟩) := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · exact hs.monotone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
  · exact hs.monotone (show (⟨i.val, i.isLt⟩ : Fin k) ≤ ⟨k - 1, by omega⟩ from
      Fin.mk_le_mk.mpr (by omega))

private lemma rat_cast_sum_real {α : Type*} (A : Finset α) (f : α → ℚ) :
    (((∑ i ∈ A, f i) : ℚ) : ℝ) = ∑ i ∈ A, ((f i : ℝ)) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, Rat.cast_add, ih]

/-- Helper: convert a reciprocal sum equal to `1` in `ℝ` along an injective sequence `s : Fin k → ℕ`
to a reciprocal sum equal to `1` in `ℚ` over `Finset.image s Finset.univ`. -/
lemma sum_image_inv_rat_eq_one {k : ℕ} {s : Fin k → ℕ} (hs : StrictMono s)
    (hsum : (∑ i : Fin k, (1 : ℝ) / (s i : ℝ)) = 1) :
    (∑ x ∈ Finset.image s Finset.univ, (1 : ℚ) / (x : ℚ)) = 1 := by
  rw [Finset.sum_image (fun i _ j _ hij => hs.injective hij)]
  have hcast : (((∑ i : Fin k, (1 : ℚ) / (s i : ℚ)) : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
    rw [rat_cast_sum_real]
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    exact hsum
  exact Rat.cast_injective hcast

/-- Helper: given `s : Fin k → ℕ` (`k ≥ 2`) strictly increasing and `s 0 ≤ x < s (k - 1)`,
there is an index `m : Fin (k - 1)` with `s m ≤ x < s (m + 1)`. -/
lemma exists_consecutive_bracket {k : ℕ} (hk : 2 ≤ k) {s : Fin k → ℕ} (_hs : StrictMono s)
    {x : ℕ} (hax : s ⟨0, by omega⟩ ≤ x) (hxb : x < s ⟨k - 1, by omega⟩) :
    ∃ m : Fin (k - 1), s ⟨m.val, by omega⟩ ≤ x ∧ x < s ⟨m.val + 1, by omega⟩ := by
  let A := Finset.univ.filter (fun i : Fin k => s i ≤ x)
  have h0 : (⟨0, by omega⟩ : Fin k) ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax⟩
  let m0 : Fin k := A.max' ⟨_, h0⟩
  have hm0_mem : m0 ∈ A := Finset.max'_mem A ⟨_, h0⟩
  have hm0_le : s m0 ≤ x := (Finset.mem_filter.mp hm0_mem).2
  have hm0_lt : m0.val < k - 1 := by
    by_contra hge
    have hm0_isLt : m0.val < k := m0.isLt
    have hm0_val : m0.val = k - 1 := by omega
    have heq : m0 = ⟨k - 1, by omega⟩ := Fin.ext hm0_val
    rw [heq] at hm0_le
    omega
  refine ⟨⟨m0.val, hm0_lt⟩, hm0_le, ?_⟩
  by_contra hle
  have hle' : s ⟨m0.val + 1, by omega⟩ ≤ x := Nat.not_lt.mp hle
  have hnext_mem : (⟨m0.val + 1, by omega⟩ : Fin k) ∈ A :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle'⟩
  have hmax : (⟨m0.val + 1, by omega⟩ : Fin k) ≤ m0 := Finset.le_max' A _ hnext_mem
  have hval : m0.val + 1 ≤ m0.val := Fin.le_def.mp hmax
  omega

/-- Bridge theorem (counterexample-free form → `Erdos287Conjecture`):
if no `CandidateSet a b S` exists, then `Erdos287Conjecture` holds. -/
theorem erdos_287_of_no_candidate_set
    (hno : ∀ a b : ℕ, ∀ S : Finset ℕ, ¬ CandidateSet a b S) :
    Erdos287Conjecture := by
  intro k hk s hs hs0 hsum
  by_contra hgap
  have hgap_le : max_gap k s ≤ 2 := by omega
  let a := s ⟨0, by omega⟩
  let b := s ⟨k - 1, by omega⟩
  let S := Finset.image s Finset.univ
  have hab : a < b := hs (Fin.mk_lt_mk.mpr (by omega))
  refine hno a b S ⟨by omega, hab, image_subset_Icc_of_strictMono hk hs, ?_, ?_,
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

/-- Converse bridge: any `CandidateSet a b S` yields a strictly increasing sequence violating
`Erdos287Conjecture`. -/
theorem no_candidate_set_of_erdos_287 (hconj : Erdos287Conjecture) :
    ∀ a b : ℕ, ∀ S : Finset ℕ, ¬ CandidateSet a b S := by
  intro a b S hc
  let k := S.card
  have hk : 2 ≤ k := by
    have hpair : ({a, b} : Finset ℕ) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hc.left_mem
      · rw [Finset.mem_singleton.mp hx]
        exact hc.right_mem
    have hcard_pair : ({a, b} : Finset ℕ).card = 2 :=
      Finset.card_pair (ne_of_lt hc.lt_endpoints)
    calc
      2 = ({a, b} : Finset ℕ).card := hcard_pair.symm
      _ ≤ S.card := Finset.card_le_card hpair
  let emb := S.orderEmbOfFin rfl
  let s : Fin k → ℕ := fun i => emb i
  have hs : StrictMono s := emb.strictMono
  have himg : Finset.image s Finset.univ = S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, s]
    constructor
    · rintro ⟨i, rfl⟩
      exact S.orderEmbOfFin_mem rfl i
    · intro hx
      have hx_range : x ∈ Set.range emb := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      exact hx_range
  have hs0_eq : s ⟨0, by omega⟩ = a := by
    have hs0_mem : s ⟨0, by omega⟩ ∈ S := S.orderEmbOfFin_mem rfl _
    have ha_le : a ≤ s ⟨0, by omega⟩ := (Finset.mem_Icc.mp (hc.subset_Icc hs0_mem)).1
    have ha_img : a ∈ Finset.image s Finset.univ := himg.symm ▸ hc.left_mem
    rcases Finset.mem_image.mp ha_img with ⟨i, _, hi⟩
    have hs0_le : s ⟨0, by omega⟩ ≤ s i := hs.monotone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
    omega
  have hsum_real : (∑ i : Fin k, (1 : ℝ) / (s i : ℝ)) = 1 := by
    have hsum_rat : (∑ i : Fin k, (1 : ℚ) / (s i : ℚ)) = 1 := by
      have himg_sum := Finset.sum_image (f := fun x : ℕ => (1 : ℚ) / (x : ℚ))
        (s := Finset.univ) (g := s) (fun i _ j _ hij => hs.injective hij)
      rw [himg] at himg_sum
      exact himg_sum.symm.trans hc.sum_inv_eq_one
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) hsum_rat
    rw [rat_cast_sum_real] at hcast
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at hcast
    exact hcast
  have ha2 : 2 ≤ a := hc.two_le_left
  have hgap3 : 3 ≤ max_gap k s := hconj k hk s hs (by omega) hsum_real
  have hgap2 : max_gap k s ≤ 2 := by
    unfold max_gap
    refine Finset.sup_le ?_
    intro i _
    by_contra hgt
    have hdiff3 : 3 ≤ s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩ := by omega
    let u := s ⟨i.val, by omega⟩
    let v := s ⟨i.val + 1, by omega⟩
    have hu_mem : u ∈ S := S.orderEmbOfFin_mem rfl _
    have hv_mem : v ∈ S := S.orderEmbOfFin_mem rfl _
    have hau : a ≤ u := (Finset.mem_Icc.mp (hc.subset_Icc hu_mem)).1
    have hvb : v ≤ b := (Finset.mem_Icc.mp (hc.subset_Icc hv_mem)).2
    have hor := hc.no_consecutive_missing (u + 1) (by omega) (by omega)
    have hex : ∃ w ∈ S, u < w ∧ w < v := by
      rcases hor with h1 | h2
      · exact ⟨u + 1, h1, by omega, by omega⟩
      · exact ⟨u + 2, h2, by omega, by omega⟩
    rcases hex with ⟨w, hwS, huw, hwv⟩
    have hw_img : w ∈ Finset.image s Finset.univ := himg.symm ▸ hwS
    rcases Finset.mem_image.mp hw_img with ⟨j, _, rfl⟩
    have hij1 : (⟨i.val, by omega⟩ : Fin k) < j := hs.lt_iff_lt.mp huw
    have hij2 : j < (⟨i.val + 1, by omega⟩ : Fin k) := hs.lt_iff_lt.mp hwv
    have h1 : i.val < j.val := Fin.lt_def.mp hij1
    have h2 : j.val < i.val + 1 := Fin.lt_def.mp hij2
    omega
  omega

/-- Full equivalence between `Erdos287Conjecture` and the non-existence of a `CandidateSet`. -/
theorem erdos_287_iff_no_candidate_set :
    Erdos287Conjecture ↔ ∀ a b : ℕ, ∀ S : Finset ℕ, ¬ CandidateSet a b S :=
  ⟨no_candidate_set_of_erdos_287, erdos_287_of_no_candidate_set⟩

/-- Sharpness witness `{2, 3, 6}`: `1/2 + 1/3 + 1/6 = 1` achieves `max_gap = 3`, showing that
the lower bound `3` in `Erdos287Conjecture` cannot be improved. -/
theorem erdos_287_sharp_2_3_6 :
    StrictMono (![2, 3, 6] : Fin 3 → ℕ) ∧
    1 < (![2, 3, 6] : Fin 3 → ℕ) ⟨0, by omega⟩ ∧
    (∑ i : Fin 3, (1 : ℝ) / ((![2, 3, 6] : Fin 3 → ℕ) i : ℝ)) = 1 ∧
    max_gap 3 ![2, 3, 6] = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · simp
  · rw [Fin.sum_univ_three]
    norm_num
  · unfold max_gap
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
      ext i
      fin_cases i <;> simp
    rw [huniv]
    simp

end Erdos287

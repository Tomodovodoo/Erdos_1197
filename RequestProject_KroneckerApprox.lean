/-
# Kronecker's Approximation Theorem

This file contains the one-dimensional Kronecker approximation result and the
local infrastructure used by the rest of the project.
-/
import Mathlib
import RequestProject_TorusSeparation

open scoped BigOperators

set_option maxHeartbeats 800000

noncomputable section

/-! ## Helper lemmas for the 1D case -/

/-
Dirichlet's approximation theorem gives a small nonzero value `k α - j` with
`k > 0`. If `α` is irrational, that value cannot be zero.
-/
lemma irrational_dirichlet_nonzero (α : ℝ) (hα : Irrational α) (n : ℕ) (hn : 0 < n) :
    ∃ j : ℤ, ∃ k : ℤ, 0 < k ∧ k ≤ n ∧ |k * α - j| ≤ 1 / (↑n + 1) ∧ k * α - j ≠ 0 := by
  obtain ⟨j, k, hk_pos, hk_le_n, h_approx⟩ :
      ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |(k : ℝ) * α - j| ≤ 1 / (n + 1) := by
    simpa using Real.exists_int_int_abs_mul_sub_le α hn
  refine ⟨j, k, hk_pos, hk_le_n, h_approx, ?_⟩
  intro hzero
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk_pos.ne'
  have hmul : (k : ℝ) * α = j := by
    linarith [hzero]
  have hαeq : α = (j : ℝ) / k := by
    apply (eq_div_iff hk_ne).2
    simpa [mul_comm] using hmul
  exact hα.ne_rational j k hαeq

/-
For irrational `α`, there are arbitrarily small positive values of the form
`k α - j` with `k > 0`.
-/
lemma irrational_small_positive_combination (α : ℝ) (hα : Irrational α) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℤ, ∃ j : ℤ, 0 < k ∧ 0 < k * α - j ∧ k * α - j < ε := by
  have h_pos : ∀ ε > 0, ∃ k : ℤ, ∃ j : ℤ, 0 < k ∧ |k * α - j| < ε ∧ k * α - j ≠ 0 := by
    intro ε hε_pos
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n > 0 ∧ 1 / (n + 1 : ℝ) < ε := by
      refine ⟨Nat.floor (ε⁻¹) + 1, ?_⟩
      constructor
      · positivity
      · have hfloor : (Nat.floor (ε⁻¹) : ℝ) ≤ ε⁻¹ := Nat.floor_le (by positivity)
        have hlt : (1 : ℝ) / (Nat.floor (ε⁻¹) + 1 + 1) < ε := by
          have h₁ : (0 : ℝ) < ε⁻¹ := by positivity
          nlinarith [hfloor, inv_pos.2 hε_pos, hε_pos]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, one_div] using hlt
    rcases irrational_dirichlet_nonzero α hα n hn.1 with ⟨j, k, hk₀, hk₁, hk₂, hk₃⟩
    refine ⟨k, j, hk₀, ?_, hk₃⟩
    have hlt : |k * α - j| < ε := by
      exact lt_of_le_of_lt hk₂ (hn.2)
    by_cases hpos : 0 < k * α - j
    · exact hpos
    · have hneg : k * α - j < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hk₃.symm
      have : 0 < -(k * α - j) := by linarith
      have : 0 < j - k * α := by linarith
      refine False.elim ?_
      linarith
  obtain ⟨k, j, hk, hj, hlt⟩ := h_pos (min (ε / 2) (1 / 2)) (by positivity)
  cases lt_or_gt_of_ne hj <;> simp_all +decide [abs_lt]
  · set r := Int.ceil (1 / (j - k * α)) - 1 with hr_def
    have hr_pos : 0 < r := by
      exact sub_pos_of_lt
        (Int.lt_ceil.mpr
          (by
            norm_num
            nlinarith [mul_inv_cancel₀ (by linarith : (2 : ℝ) ≠ 0),
              mul_inv_cancel₀ (by linarith : (j - k * α : ℝ) ≠ 0)]))
    have hr_bound : r * (j - k * α) < 1 ∧ 1 - r * (j - k * α) < ε := by
      constructor <;> push_cast [hr_def] <;>
        nlinarith [Int.ceil_lt_add_one (1 / (j - k * α)),
          Int.le_ceil (1 / (j - k * α)), mul_div_cancel₀ 1 (by linarith : (j - k * α : ℝ) ≠ 0)]
    have hr_frac : ∃ x : ℤ, 0 < r * k * α - x ∧ r * k * α - x < ε := by
      exact ⟨r * j - 1, by push_cast; linarith, by push_cast; linarith⟩
    obtain ⟨x, hx_pos, hx_bound⟩ := hr_frac
    use r * k, by positivity, x
    aesop
  · grind +locals

/-
Given `0 < δ < 1` and `y ∈ [0, 1)`, there exists `r ≥ 1` with
`|r δ - m - y| ≤ δ` for some integer `m`.
-/
lemma small_multiple_approx (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (y : ℝ) :
    ∃ r : ℕ, 0 < r ∧ ∃ m : ℤ, |↑r * δ - ↑m - y| ≤ δ := by
  by_contra! h
  set f := Int.fract y
  by_cases hf : f < δ
  · specialize h 1
    norm_num at h
    specialize h (-⌊y⌋)
    norm_num at h
    cases abs_cases (δ + ⌊y⌋ - y) <;>
      linarith [Int.fract_add_floor y, Int.fract_nonneg y, Int.fract_lt_one y]
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, r * δ ≤ f ∧ f < (r + 1) * δ := by
      exact ⟨⌊f / δ⌋, by
        nlinarith [Nat.floor_le (show 0 ≤ f / δ by exact div_nonneg (Int.fract_nonneg y) hδ_pos.le),
          mul_div_cancel₀ f hδ_pos.ne'], by
        nlinarith [Nat.lt_floor_add_one (f / δ), mul_div_cancel₀ f hδ_pos.ne']⟩
    specialize h r
    rcases r with (_ | r) <;> simp_all +decide
    · linarith
    · specialize h (-⌊y⌋)
      norm_num at h
      cases abs_cases ((r + 1) * δ + ⌊y⌋ - y) <;>
        nlinarith [Int.fract_add_floor y]

/-
Kronecker's approximation theorem in dimension one.
-/
theorem kronecker_approximation_1d (α β ε : ℝ) (hα : Irrational α) (hε : ε > 0) :
    ∃ p q : ℤ, 0 < q ∧ |α * ↑q - ↑p - β| < ε := by
  obtain ⟨k₀, j₀, hk₀_pos, hj₀_pos, hk₀j₀⟩ :
      ∃ k₀ j₀ : ℤ, 0 < k₀ ∧ 0 < k₀ * α - j₀ ∧ k₀ * α - j₀ < min ε 1 :=
    irrational_small_positive_combination α hα (min ε 1) (by positivity)
  obtain ⟨r, hr, m, hm⟩ := small_multiple_approx (k₀ * α - j₀) hj₀_pos
    (by linarith [min_le_right ε 1]) β
  exact ⟨r * j₀ + m, r * k₀, by positivity, by
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith [abs_le.mp hm, min_le_left ε 1, min_le_right ε 1]⟩

/-! ## General Kronecker approximation theorem (m × n case) -/

/-- The approximation condition in Kronecker's theorem. -/
def KroneckerApproxCondition (m n : ℕ) (α : Fin m → Fin n → ℝ) (β : Fin n → ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ q : Fin m → ℤ, ∃ p : Fin n → ℤ,
      ∀ j : Fin n, |∑ i : Fin m, (q i : ℝ) * α i j - (p j : ℝ) - β j| < ε

/-- The integer-relation condition in Kronecker's theorem. -/
def KroneckerIntRelCondition (m n : ℕ) (α : Fin m → Fin n → ℝ) (β : Fin n → ℝ) : Prop :=
  ∀ r : Fin n → ℤ,
    (∀ i : Fin m, ∃ z : ℤ, ∑ j : Fin n, α i j * (r j : ℝ) = z) →
    ∃ z : ℤ, ∑ j : Fin n, β j * (r j : ℝ) = z

/- The easy direction of Kronecker's theorem. -/
theorem kronecker_approx_implies_intrel (m n : ℕ) (α : Fin m → Fin n → ℝ) (β : Fin n → ℝ) :
    KroneckerApproxCondition m n α β → KroneckerIntRelCondition m n α β := by
  intro h_approx
  intro r hr
  by_contra h_contra
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ z : ℤ, |∑ j, β j * (r j : ℝ) - z| ≥ ε := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℝ) < ∑ j, β j * (r j : ℝ) ∧ ∑ j, β j * (r j : ℝ) < (k + 1 : ℝ) := by
      exact ⟨⌊∑ j, β j * r j⌋, lt_of_le_of_ne (Int.floor_le _) fun h => h_contra ⟨_, h.symm⟩,
        Int.lt_floor_add_one _⟩
    use min ((∑ j, β j * (r j : ℝ)) - k) (k + 1 - (∑ j, β j * (r j : ℝ)))
    simp +zetaDelta at *
    exact ⟨hk, fun z => by
      by_cases h : z ≤ k
      · left
        cases abs_cases (∑ j, β j * (r j : ℝ) - z) <;>
          linarith [show (z : ℝ) ≤ k by exact_mod_cast h]
      · right
        cases abs_cases (∑ j, β j * (r j : ℝ) - z) <;>
          linarith [show (z : ℝ) ≥ k + 1 by exact_mod_cast not_le.mp h]⟩
  obtain ⟨q, p, hq⟩ : ∃ q : Fin m → ℤ, ∃ p : Fin n → ℤ,
      ∀ j : Fin n, |∑ i : Fin m, (q i : ℝ) * α i j - (p j : ℝ) - β j| < ε / (∑ j, |r j| + 1) := by
    exact h_approx _ (by positivity)
  have h_sum : |∑ j, (∑ i : Fin m, (q i : ℝ) * α i j - (p j : ℝ) - β j) * (r j : ℝ)| < ε := by
    refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
    simp_all +decide [abs_mul]
    refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_of_lt (hq i)) (abs_nonneg _)) ?_
    rw [← Finset.mul_sum _ _ _, div_mul_eq_mul_div, div_lt_iff₀] <;>
      nlinarith [show 0 ≤ ∑ i : Fin n, |(r i : ℝ)| from Finset.sum_nonneg fun _ _ => abs_nonneg _]
  have h_sum_eq :
      ∑ j, (∑ i : Fin m, (q i : ℝ) * α i j - (p j : ℝ) - β j) * (r j : ℝ) =
        ∑ i : Fin m, (q i : ℝ) * (∑ j, α i j * (r j : ℝ)) -
          ∑ j, (p j : ℝ) * (r j : ℝ) - ∑ j, β j * (r j : ℝ) := by
    simp +decide [sub_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  have h_int_sums :
      ∃ z : ℤ, ∑ i : Fin m, (q i : ℝ) * (∑ j, α i j * (r j : ℝ)) - ∑ j, (p j : ℝ) * (r j : ℝ) = z := by
    choose! z hz using hr
    exact ⟨∑ i, q i * z i - ∑ j, p j * r j, by
      push_cast
      rw [Finset.sum_congr rfl fun i hi => by rw [hz i]]⟩
  grind +extAll

/-- The hard direction of Kronecker's theorem. -/
theorem kronecker_intrel_implies_approx (m n : ℕ) (α : Fin m → Fin n → ℝ) (β : Fin n → ℝ) :
    KroneckerIntRelCondition m n α β → KroneckerApproxCondition m n α β := by
  intro h_intrel
  exact kronecker_intrel_implies_approx_general m n α β (fun r hr => h_intrel r hr)

/-- The full Kronecker equivalence. -/
theorem kronecker_approximation_general (m n : ℕ) (α : Fin m → Fin n → ℝ) (β : Fin n → ℝ) :
    KroneckerApproxCondition m n α β ↔ KroneckerIntRelCondition m n α β :=
  ⟨kronecker_approx_implies_intrel m n α β, kronecker_intrel_implies_approx m n α β⟩

/-- Kronecker's theorem implies the 1D case. -/
theorem kronecker_1d_from_general (α β : ℝ) (hα : Irrational α) :
    ∀ ε > 0, ∃ q : ℤ, ∃ p : ℤ, |↑q * α - ↑p - β| < ε := by
  intro ε hε
  obtain ⟨p, q, hq, hp⟩ := kronecker_approximation_1d α β ε hα hε
  exact ⟨q, p, hq, by simpa only [mul_comm] using hp⟩

end

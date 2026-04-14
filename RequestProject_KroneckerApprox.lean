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
  admit

/-
Given `0 < δ < 1` and `y ∈ [0, 1)`, there exists `r ≥ 1` with
`|r δ - m - y| ≤ δ` for some integer `m`.
-/
lemma small_multiple_approx (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (y : ℝ) :
    ∃ r : ℕ, 0 < r ∧ ∃ m : ℤ, |↑r * δ - ↑m - y| ≤ δ := by
  admit

/-
Kronecker's approximation theorem in dimension one.
-/
theorem kronecker_approximation_1d (α β ε : ℝ) (hα : Irrational α) (hε : ε > 0) :
    ∃ p q : ℤ, 0 < q ∧ |α * ↑q - ↑p - β| < ε := by
  admit

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
  admit

end

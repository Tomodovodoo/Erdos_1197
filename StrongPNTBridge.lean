import Mathlib

open scoped Asymptotics

noncomputable section

/-- The second Chebyshev psi function. -/
def ChebyshevPsi (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (Nat.floor x + 1)) ArithmeticFunction.vonMangoldt

local notation "ψ" => ChebyshevPsi

/-- Strong prime number theorem in the form needed by the BM bridge. -/
theorem Strong_PNT : ∃ c > 0,
    (ψ - id) =O[Filter.atTop]
      (fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2))) := by
  admit

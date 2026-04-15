import Mathlib
import PNTBridge
import RequestProject_TorusSeparation

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

/-- `I_∞ = [16/25, 2/3]`, the interval on which the covering property fails. -/
def I_inf : Set ℝ := Icc (16/25 : ℝ) (2/3)

abbrev PrimeIdx (k : ℕ) := Fin (2 ^ k)

abbrev IntIdx (ν : ℕ) := Fin (2 ^ (ν - 2) + 1)

abbrev BMIdx (k ν : ℕ) := PrimeIdx k ⊕ IntIdx ν

/-- The BM integer block is the full interval of consecutive integers
`[7 * 2^(ν-3), 9 * 2^(ν-3)]`. -/
def bmIntVal (ν : ℕ) (j : IntIdx ν) : ℕ :=
  7 * 2 ^ (ν - 3) + j.1

/-- Positive part of an integer coefficient, viewed as a natural-number exponent. -/
abbrev zpos (z : ℤ) : ℕ := Int.toNat z

/-- Negative part of an integer coefficient, viewed as a natural-number exponent. -/
abbrev zneg (z : ℤ) : ℕ := Int.toNat (-z)

lemma zpos_sub_zneg (z : ℤ) : (zpos z : ℤ) - zneg z = z := by
  simp [zpos, zneg]

lemma cast_zpos_sub_zneg (z : ℤ) : (zpos z : ℝ) - zneg z = z := by
  exact_mod_cast zpos_sub_zneg z

lemma zpos_eq_zero_of_nonpos {z : ℤ} (hz : z ≤ 0) : zpos z = 0 := by
  simp [zpos, Int.toNat_of_nonpos hz]

lemma zneg_eq_zero_of_nonneg {z : ℤ} (hz : 0 ≤ z) : zneg z = 0 := by
  simp [zneg, Int.toNat_of_nonpos (neg_nonpos.mpr hz)]

lemma zpos_pos_of_pos {z : ℤ} (hz : 0 < z) : 0 < zpos z := by
  have hz' : (0 : ℤ) < z.toNat := by
    rw [Int.toNat_of_nonneg hz.le]
    exact hz
  exact_mod_cast hz'

lemma zneg_pos_of_neg {z : ℤ} (hz : z < 0) : 0 < zneg z := by
  have hneg : 0 < -z := by simpa using neg_pos.mpr hz
  have hneg' : (0 : ℤ) < (-z).toNat := by
    rw [Int.toNat_of_nonneg hneg.le]
    exact hneg
  simpa [zneg] using hneg'

lemma logb_nat_finset_prod_pow
    {α : Type*} (s : Finset α) (f : α → ℕ) (e : α → ℕ)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    Real.logb 2 ((∏ a ∈ s, f a ^ e a : ℕ) : ℝ) =
      ∑ a ∈ s, (e a : ℝ) * Real.logb 2 (f a : ℝ) := by
  have hpow_ne :
      ∀ a ∈ s, (((f a) ^ e a : ℕ) : ℝ) ≠ 0 := by
    intro a ha
    exact_mod_cast pow_ne_zero _ (hf a ha)
  rw [Nat.cast_prod, Real.logb_prod]
  · simp_rw [Nat.cast_pow, Real.logb_pow]
  · simpa using hpow_ne

lemma logb_nat_fintype_prod_pow
    {α : Type*} [Fintype α] (f : α → ℕ) (e : α → ℕ)
    (hf : ∀ a, f a ≠ 0) :
    Real.logb 2 ((∏ a, f a ^ e a : ℕ) : ℝ) =
      ∑ a, (e a : ℝ) * Real.logb 2 (f a : ℝ) := by
  simpa using logb_nat_finset_prod_pow Finset.univ f e (fun a _ => hf a)

lemma logb_nat_fintype_prod_zparts
    {α : Type*} [Fintype α] (f : α → ℕ) (r : α → ℤ)
    (hf : ∀ a, f a ≠ 0) :
    Real.logb 2 ((∏ a, f a ^ zpos (r a) : ℕ) : ℝ) -
        Real.logb 2 ((∏ a, f a ^ zneg (r a) : ℕ) : ℝ) =
      ∑ a, (r a : ℝ) * Real.logb 2 (f a : ℝ) := by
  rw [logb_nat_fintype_prod_pow f (fun a => zpos (r a)) hf,
    logb_nat_fintype_prod_pow f (fun a => zneg (r a)) hf]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hz : (zpos (r a) : ℝ) - zneg (r a) = r a := cast_zpos_sub_zneg (r a)
  calc
    (zpos (r a) : ℝ) * Real.logb 2 (f a : ℝ) -
        (zneg (r a) : ℝ) * Real.logb 2 (f a : ℝ)
      = ((zpos (r a) : ℝ) - zneg (r a)) * Real.logb 2 (f a : ℝ) := by ring
    _ = (r a : ℝ) * Real.logb 2 (f a : ℝ) := by rw [hz]

lemma logb_nat_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.logb 2 ((a * b : ℕ) : ℝ) = Real.logb 2 (a : ℝ) + Real.logb 2 (b : ℝ) := by
  rw [Nat.cast_mul, Real.logb_mul]
  · exact_mod_cast ha
  · exact_mod_cast hb

lemma bm_lower_endpoint (ν : ℕ) (hν : 3 ≤ ν) :
    ((7 : ℝ) / 8) * 2 ^ ν = 7 * 2 ^ (ν - 3) := by
  have hsplit : ν = (ν - 3) + 3 := by omega
  rw [hsplit, pow_add]
  norm_num
  ring

lemma bm_upper_endpoint (ν : ℕ) (hν : 3 ≤ ν) :
    ((9 : ℝ) / 8) * 2 ^ ν = 9 * 2 ^ (ν - 3) := by
  have hsplit : ν = (ν - 3) + 3 := by omega
  rw [hsplit, pow_add]
  norm_num
  ring

lemma bmIntVal_mem_Icc (ν : ℕ) (hν : 3 ≤ ν) (j : IntIdx ν) :
    (bmIntVal ν j : ℝ) ∈
      Icc (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) := by
  constructor
  · rw [bm_lower_endpoint ν hν]
    exact_mod_cast Nat.le_add_right _ _
  · rw [bm_upper_endpoint ν hν]
    have hj : j.1 ≤ 2 ^ (ν - 2) := Nat.lt_succ_iff.mp j.2
    have hpow : (2 : ℝ) ^ (ν - 2) = (2 : ℝ) ^ (ν - 3) * 2 := by
      have hsplit : ν - 2 = (ν - 3) + 1 := by omega
      rw [hsplit, pow_add]
      norm_num
    calc
      (bmIntVal ν j : ℝ) = 7 * 2 ^ (ν - 3) + j.1 := by
        simp [bmIntVal, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      _ ≤ 7 * 2 ^ (ν - 3) + 2 ^ (ν - 2) := by
        gcongr
        exact_mod_cast hj
      _ = 9 * 2 ^ (ν - 3) := by
        rw [hpow]
        ring

/-- Every integer in the open BM integer window occurs in the enumerated integer block. -/
lemma exists_bmIntVal_eq_of_mem_Ioo (ν : ℕ) (hν : 3 ≤ ν) {n : ℕ}
    (hn : (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν)) :
    ∃ j : IntIdx ν, bmIntVal ν j = n := by
  rw [bm_lower_endpoint ν hν, bm_upper_endpoint ν hν] at hn
  have hlow : 7 * 2 ^ (ν - 3) < n := by exact_mod_cast hn.1
  have hhigh : n < 9 * 2 ^ (ν - 3) := by exact_mod_cast hn.2
  refine ⟨⟨n - 7 * 2 ^ (ν - 3), ?_⟩, ?_⟩
  · have hpow : 2 ^ (ν - 2) = 2 ^ (ν - 3) * 2 := by
      have hsplit : ν - 2 = (ν - 3) + 1 := by omega
      rw [hsplit, pow_add]
      norm_num
    omega
  · simp [bmIntVal, Nat.add_sub_of_le (Nat.le_of_lt hlow)]

/-- Left endpoint of the `j`-th BM prime interval. -/
def bmPrimeLeft (k ν : ℕ) (j : PrimeIdx k) : ℝ :=
  (((23 : ℝ) / 16) + (j : ℝ) / (2 : ℝ) ^ (k + 5)) * (2 : ℝ) ^ ν

/-- Right endpoint of the `j`-th BM prime interval. -/
def bmPrimeRight (k ν : ℕ) (j : PrimeIdx k) : ℝ :=
  (((23 : ℝ) / 16) + ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5)) * (2 : ℝ) ^ ν

lemma bmPrimeLeft_lt_right (k ν : ℕ) (j : PrimeIdx k) :
    bmPrimeLeft k ν j < bmPrimeRight k ν j := by
  unfold bmPrimeLeft bmPrimeRight
  have hpow : 0 < (2 : ℝ) ^ ν := by positivity
  have hinner : (j : ℝ) / (2 : ℝ) ^ (k + 5) < ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) := by
    have hden : ((2 : ℝ) ^ (k + 5)) ≠ 0 := by positivity
    field_simp [hden]
    linarith
  have hinner' :
      (23 / 16 : ℝ) + (j : ℝ) / (2 : ℝ) ^ (k + 5) <
        (23 / 16 : ℝ) + ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) := by
    linarith
  exact mul_lt_mul_of_pos_right hinner' hpow

lemma bmPrimeLeft_lower_mem (k ν : ℕ) (j : PrimeIdx k) :
    ((23 : ℝ) / 16) * (2 : ℝ) ^ ν ≤ bmPrimeLeft k ν j := by
  unfold bmPrimeLeft
  have hpow : 0 ≤ (2 : ℝ) ^ ν := by positivity
  have hfrac : 0 ≤ (j : ℝ) / (2 : ℝ) ^ (k + 5) := by positivity
  nlinarith

lemma bmPrimeRight_lt_upper (k ν : ℕ) (j : PrimeIdx k) :
    bmPrimeRight k ν j < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν := by
  unfold bmPrimeRight
  have hpow : 0 < (2 : ℝ) ^ ν := by positivity
  have hval : ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) ≤ (1 : ℝ) / 32 := by
    have hj_nat : j.1 + 1 ≤ 2 ^ k := Nat.succ_le_of_lt j.2
    have hj_cast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
      exact_mod_cast hj_nat
    have hmul : (2 : ℝ) ^ (k + 5) = (2 : ℝ) ^ k * 32 := by
      rw [pow_add]
      norm_num
    rw [hmul]
    have hkpow : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    have htmp :
        ((j : ℝ) + 1) / ((2 : ℝ) ^ k * 32) ≤
          ((2 : ℝ) ^ k) / ((2 : ℝ) ^ k * 32) := by
      field_simp [hkpow]
      nlinarith
    have hcancel : ((2 : ℝ) ^ k) / ((2 : ℝ) ^ k * 32) = (1 : ℝ) / 32 := by
      field_simp [hkpow]
    simpa [hcancel] using htmp
  have hinner : ((23 : ℝ) / 16) + (((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5)) < (3 : ℝ) / 2 := by
    nlinarith
  nlinarith

lemma bmPrimeRight_le_bmPrimeLeft_of_lt {k ν : ℕ} {i j : PrimeIdx k} (hij : i < j) :
    bmPrimeRight k ν i ≤ bmPrimeLeft k ν j := by
  unfold bmPrimeRight bmPrimeLeft
  have hpow : 0 ≤ (2 : ℝ) ^ ν := by positivity
  have hij_nat : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hij
  have hij_cast : (i : ℝ) + 1 ≤ (j : ℝ) := by
    exact_mod_cast hij_nat
  have hfrac :
      ((i : ℝ) + 1) / (2 : ℝ) ^ (k + 5) ≤ (j : ℝ) / (2 : ℝ) ^ (k + 5) := by
    have hden : ((2 : ℝ) ^ (k + 5)) ≠ 0 := by positivity
    field_simp [hden]
    nlinarith
  nlinarith

lemma eventually_theta_increment_pos_mul_pow
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b) (hgap : ε * (a + b) < b - a) (hε : 0 < ε) :
    ∀ᶠ ν : ℕ in Filter.atTop, θ (b * (2 : ℝ) ^ ν) - θ (a * (2 : ℝ) ^ ν) > 0 := by
  have hpow : Filter.Tendsto (fun ν : ℕ ↦ (2 : ℝ) ^ ν) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hta : Filter.Tendsto (fun ν : ℕ ↦ a * (2 : ℝ) ^ ν) Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop ha
  have htb : Filter.Tendsto (fun ν : ℕ ↦ b * (2 : ℝ) ^ ν) Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop hb
  have hLittle : (θ - id) =o[Filter.atTop] id := chebyshev_asymptotic.isLittleO
  have hA :
      ∀ᶠ ν : ℕ in Filter.atTop,
        ‖(θ (a * (2 : ℝ) ^ ν) - a * (2 : ℝ) ^ ν)‖ ≤ ε * ‖a * (2 : ℝ) ^ ν‖ := by
    simpa [sub_eq_add_neg, Function.comp_def] using (hLittle.comp_tendsto hta).def hε
  have hB :
      ∀ᶠ ν : ℕ in Filter.atTop,
        ‖(θ (b * (2 : ℝ) ^ ν) - b * (2 : ℝ) ^ ν)‖ ≤ ε * ‖b * (2 : ℝ) ^ ν‖ := by
    simpa [sub_eq_add_neg, Function.comp_def] using (hLittle.comp_tendsto htb).def hε
  filter_upwards [hA, hB] with ν hAν hBν
  have hpow_pos : 0 < (2 : ℝ) ^ ν := by positivity
  have haν_pos : 0 < a * (2 : ℝ) ^ ν := mul_pos ha hpow_pos
  have hbν_pos : 0 < b * (2 : ℝ) ^ ν := mul_pos hb hpow_pos
  have hAν' := abs_le.mp hAν
  have hBν' := abs_le.mp hBν
  have hA_upper : θ (a * (2 : ℝ) ^ ν) ≤ a * (2 : ℝ) ^ ν + ε * (a * (2 : ℝ) ^ ν) := by
    rw [Real.norm_eq_abs, abs_of_pos haν_pos] at hAν'
    linarith
  have hB_lower : b * (2 : ℝ) ^ ν - ε * (b * (2 : ℝ) ^ ν) ≤ θ (b * (2 : ℝ) ^ ν) := by
    rw [Real.norm_eq_abs, abs_of_pos hbν_pos] at hBν'
    linarith
  have hgapν : (ε * (a + b)) * (2 : ℝ) ^ ν < (b - a) * (2 : ℝ) ^ ν := by
    gcongr
  nlinarith

/-- BM prime supply: for large dyadic scales, there are `2^k` distinct primes in the BM window. -/
theorem bm_many_primes (k : ℕ) :
    ∃ N, ∀ ν ≥ N,
      ∃ p : PrimeIdx k → ℕ,
        Pairwise (fun i j => p i ≠ p j) ∧
        (∀ i, Nat.Prime (p i)) ∧
        (∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
              (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν) := by
  let a : PrimeIdx k → ℝ := fun j => (23 : ℝ) / 16 + (j : ℝ) / (2 : ℝ) ^ (k + 5)
  let b : PrimeIdx k → ℝ := fun j => (23 : ℝ) / 16 + ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5)
  have h_event :
      ∀ᶠ ν : ℕ in Filter.atTop,
        ∀ j : PrimeIdx k, θ (b j * (2 : ℝ) ^ ν) - θ (a j * (2 : ℝ) ^ ν) > 0 := by
    rw [Filter.eventually_all]
    intro j
    have ha_pos : 0 < a j := by
      dsimp [a]
      positivity
    have hb_pos : 0 < b j := by
      dsimp [b]
      positivity
    have hgap :
        ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * (a j + b j) < b j - a j := by
      have hsum : a j + b j < 3 := by
        dsimp [a, b]
        have hval : ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) ≤ (1 : ℝ) / 32 := by
          have hj_nat : j.1 + 1 ≤ 2 ^ k := Nat.succ_le_of_lt j.2
          have hj_cast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
            exact_mod_cast hj_nat
          have hmul : (2 : ℝ) ^ (k + 5) = (2 : ℝ) ^ k * 32 := by
            rw [pow_add]
            norm_num
          rw [hmul]
          have hkpow : ((2 : ℝ) ^ k) ≠ 0 := by positivity
          field_simp [hkpow]
          nlinarith [hj_cast]
        have hval' : (j : ℝ) / (2 : ℝ) ^ (k + 5) ≤ (1 : ℝ) / 32 := by
          have hj_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
          have hfrac :
              (j : ℝ) / (2 : ℝ) ^ (k + 5) ≤ ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) := by
            gcongr
          exact le_trans hfrac hval
        nlinarith [hval, hval']
      have hdiff : b j - a j = (1 : ℝ) / (2 : ℝ) ^ (k + 5) := by
        dsimp [a, b]
        ring_nf
      rw [hdiff]
      have hkpow8 : 0 < (2 : ℝ) ^ (k + 8) := by positivity
      have hmul :
          ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * (a j + b j) <
            ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * 3 := by
        gcongr
      have htarget :
          ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * 3 < (1 : ℝ) / (2 : ℝ) ^ (k + 5) := by
        have hpow5 : 0 < (2 : ℝ) ^ (k + 5) := by positivity
        field_simp [hkpow8.ne', hpow5.ne']
        have hpow_split : (2 : ℝ) ^ (k + 8) = 8 * (2 : ℝ) ^ (k + 5) := by
          rw [pow_add]
          ring_nf
        nlinarith [hpow_split, hpow5]
      exact lt_trans hmul htarget
    have hε : 0 < (1 : ℝ) / (2 : ℝ) ^ (k + 8) := by positivity
    simpa [a, b] using
      eventually_theta_increment_pos_mul_pow
        (a := a j) (b := b j) (ε := (1 : ℝ) / (2 : ℝ) ^ (k + 8))
        ha_pos hb_pos hgap hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_event
  refine ⟨N, fun ν hν => ?_⟩
  have hν_all := hN ν hν
  have hPrimeExists :
      ∀ j : PrimeIdx k, ∃ p : ℕ, Nat.Prime p ∧
        bmPrimeLeft k ν j < (p : ℝ) ∧ (p : ℝ) ≤ bmPrimeRight k ν j := by
    intro j
    have hleft_lt_right : bmPrimeLeft k ν j < bmPrimeRight k ν j :=
      bmPrimeLeft_lt_right k ν j
    have htheta :
        θ (bmPrimeRight k ν j) - θ (bmPrimeLeft k ν j) > 0 := by
      simpa [bmPrimeLeft, bmPrimeRight] using hν_all j
    simpa [HasPrimeInInterval, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      theta_pos_implies_prime_in_interval hleft_lt_right htheta
  choose p hpPrime hpLower hpUpper using hPrimeExists
  refine ⟨p, ?_, hpPrime, ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · have hsep : bmPrimeRight k ν i ≤ bmPrimeLeft k ν j :=
        bmPrimeRight_le_bmPrimeLeft_of_lt hij'
      have hlt : (p i : ℝ) < p j := by
        exact lt_of_le_of_lt ((hpUpper i).trans hsep) (hpLower j)
      exact fun hEq => by
        exact (ne_of_lt hlt) (by exact_mod_cast hEq)
    · have hsep : bmPrimeRight k ν j ≤ bmPrimeLeft k ν i :=
        bmPrimeRight_le_bmPrimeLeft_of_lt hij'
      have hlt : (p j : ℝ) < p i := by
        exact lt_of_le_of_lt ((hpUpper j).trans hsep) (hpLower i)
      exact fun hEq => by
        exact (ne_of_gt hlt) (by exact_mod_cast hEq)
  · intro j
    constructor
    · exact lt_of_le_of_lt (bmPrimeLeft_lower_mem k ν j) (hpLower j)
    · exact lt_of_le_of_lt (hpUpper j) (bmPrimeRight_lt_upper k ν j)

/-- BM frequency vector on the prime-plus-integer block. -/
def bmAlpha {k ν : ℕ} (p : PrimeIdx k → ℕ) : BMIdx k ν → ℝ
  | Sum.inl i => Real.logb 2 (p i)
  | Sum.inr j => Real.logb 2 (bmIntVal ν j)

/-- BM target vector on the prime-plus-integer block. -/
def bmBeta (k ν : ℕ) : BMIdx k ν → ℝ
  | Sum.inl i => (i : ℝ) / (2 : ℝ) ^ k
  | Sum.inr _ => 0

/-- Flatten the BM sum index to a single `Fin` index for the Kronecker theorem. -/
abbrev bmFlatEquiv (k ν : ℕ) :
    BMIdx k ν ≃ Fin (2 ^ k + (2 ^ (ν - 2) + 1)) :=
  finSumFinEquiv

def bmFlatAlpha {k ν : ℕ} (p : PrimeIdx k → ℕ) :
    Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℝ :=
  bmAlpha p ∘ (bmFlatEquiv k ν).symm

def bmFlatBeta (k ν : ℕ) :
    Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℝ :=
  bmBeta k ν ∘ (bmFlatEquiv k ν).symm

lemma bmFlatAlpha_castAdd {k ν : ℕ} (p : PrimeIdx k → ℕ) (i : PrimeIdx k) :
    bmFlatAlpha p (Fin.castAdd (2 ^ (ν - 2) + 1) i) = Real.logb 2 (p i) := by
  simp [bmFlatAlpha, bmAlpha, bmFlatEquiv]

lemma bmFlatAlpha_natAdd {k ν : ℕ} (p : PrimeIdx k → ℕ) (j : IntIdx ν) :
    bmFlatAlpha p (Fin.natAdd (2 ^ k) j) = Real.logb 2 (bmIntVal ν j) := by
  simp [bmFlatAlpha, bmAlpha, bmFlatEquiv]

lemma bmFlatBeta_castAdd {k ν : ℕ} (i : PrimeIdx k) :
    bmFlatBeta k ν (Fin.castAdd (2 ^ (ν - 2) + 1) i) = (i : ℝ) / (2 : ℝ) ^ k := by
  simp [bmFlatBeta, bmBeta, bmFlatEquiv]

lemma bmFlatBeta_natAdd {k ν : ℕ} (j : IntIdx ν) :
    bmFlatBeta k ν (Fin.natAdd (2 ^ k) j) = 0 := by
  simp [bmFlatBeta, bmBeta, bmFlatEquiv]

/-- The first nontrivial prime-grid index, available once `k ≥ 1`. -/
def bmPrimeIdxOne (k : ℕ) (hk : 1 ≤ k) : PrimeIdx k :=
  ⟨1, by
    have hpow : (2 : ℕ) ≤ 2 ^ k := by
      simpa using pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by decide) hk
    omega⟩

lemma bmBeta_primeIdxOne_eq (k ν : ℕ) (hk : 1 ≤ k) :
    bmBeta k ν (Sum.inl (bmPrimeIdxOne k hk)) = 1 / (2 : ℝ) ^ k := by
  simp [bmBeta, bmPrimeIdxOne]

lemma bmFlatBeta_primeIdxOne_eq (k ν : ℕ) (hk : 1 ≤ k) :
    bmFlatBeta k ν
        (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk)) =
      1 / (2 : ℝ) ^ k := by
  simpa [bmFlatBeta, bmBeta, bmFlatEquiv] using bmBeta_primeIdxOne_eq k ν hk

lemma prime_not_dvd_pow_of_not_dvd {p a e : ℕ} (hp : Nat.Prime p) (hnot : ¬ p ∣ a) :
    ¬ p ∣ a ^ e := by
  intro h
  exact hnot (hp.dvd_of_dvd_pow h)

lemma bmIntVal_pos (ν : ℕ) (_hν : 3 ≤ ν) (j : IntIdx ν) : 0 < bmIntVal ν j := by
  have hbase : 0 < 7 * 2 ^ (ν - 3) := by
    have hpow : 0 < 2 ^ (ν - 3) := pow_pos (by omega) _
    omega
  exact lt_of_lt_of_le hbase (Nat.le_add_right _ _)

lemma bm_prime_gt_bmIntVal
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (i : PrimeIdx k) (j : IntIdx ν) :
    bmIntVal ν j < p i := by
  have hj_upper : (bmIntVal ν j : ℝ) ≤ ((9 : ℝ) / 8) * (2 : ℝ) ^ ν :=
    (bmIntVal_mem_Icc ν hν j).2
  have hp_lower : ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) := (hp_window i).1
  have hconst : ((9 : ℝ) / 8) * (2 : ℝ) ^ ν < ((23 : ℝ) / 16) * (2 : ℝ) ^ ν := by
    have hpow : 0 < (2 : ℝ) ^ ν := by positivity
    nlinarith
  have hlt : (bmIntVal ν j : ℝ) < (p i : ℝ) := lt_of_le_of_lt hj_upper (lt_trans hconst hp_lower)
  exact_mod_cast hlt

lemma bm_prime_ne_two
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (i : PrimeIdx k) :
    p i ≠ 2 := by
  have hp_lower : ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) := (hp_window i).1
  have hgt_two : (2 : ℝ) < (p i : ℝ) := by
    have hpow3 : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ ν := by
      exact pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hν
    have hpow : (8 : ℝ) ≤ (2 : ℝ) ^ ν := by
      norm_num at hpow3 ⊢
      exact hpow3
    nlinarith
  exact_mod_cast ne_of_gt hgt_two

lemma bm_prime_not_dvd_intVal
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (i : PrimeIdx k) (j : IntIdx ν) :
    ¬ p i ∣ bmIntVal ν j := by
  have hlt : bmIntVal ν j < p i := bm_prime_gt_bmIntVal hν p hp_window i j
  have hcop :
      Nat.Coprime (p i) (bmIntVal ν j) :=
    Nat.coprime_of_lt_prime (Nat.ne_of_gt (bmIntVal_pos ν hν j)) hlt (hpPrime i)
  exact (hpPrime i).coprime_iff_not_dvd.mp hcop

lemma bm_prime_not_dvd_other_prime
    {k : ℕ} (p : PrimeIdx k → ℕ)
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hpPairwise : Pairwise (fun i j => p i ≠ p j))
    {i i' : PrimeIdx k} (hii' : i ≠ i') :
    ¬ p i ∣ p i' := by
  intro hdiv
  exact hpPairwise hii' ((Nat.prime_dvd_prime_iff_eq (hpPrime i) (hpPrime i')).1 hdiv)

lemma bm_flat_intrel_of_prime_window
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hpPairwise : Pairwise (fun i j => p i ≠ p j))
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν) :
    ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
      (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
      ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z := by
  intro r hrel
  let rBM : BMIdx k ν → ℤ := fun x => r (bmFlatEquiv k ν x)
  rcases hrel with ⟨z, hz⟩
  have hzBM :
      ∑ x : BMIdx k ν, bmAlpha p x * (rBM x : ℝ) = z := by
    have hsum' :
        ∑ x : BMIdx k ν, bmAlpha p x * (rBM x : ℝ) =
          ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatAlpha p j * (r j : ℝ) := by
      exact Fintype.sum_equiv (bmFlatEquiv k ν)
        (fun x : BMIdx k ν => bmAlpha p x * (rBM x : ℝ))
        (fun j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) => bmFlatAlpha p j * (r j : ℝ))
        (fun x => by
          cases x with
          | inl i =>
              simp [rBM, bmFlatAlpha, bmAlpha, bmFlatEquiv]
          | inr j =>
              simp [rBM, bmFlatAlpha, bmAlpha, bmFlatEquiv])
    have hsum :
        ∑ x : BMIdx k ν, bmAlpha p x * (rBM x : ℝ) =
          ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatAlpha p j * (r j : ℝ) := by
      simpa [rBM, bmFlatAlpha, bmAlpha, bmFlatEquiv] using hsum'
    exact hsum.trans hz
  have hzSplit :
      (∑ i : PrimeIdx k, Real.logb 2 (p i : ℝ) * (rBM (Sum.inl i) : ℝ)) +
          ∑ j : IntIdx ν, Real.logb 2 (bmIntVal ν j : ℝ) * (rBM (Sum.inr j) : ℝ) = z := by
    simpa [bmAlpha, rBM, Fintype.sum_sum_type, mul_comm, mul_left_comm, mul_assoc] using hzBM
  let primePosProd : ℕ := ∏ i : PrimeIdx k, p i ^ zpos (rBM (Sum.inl i))
  let primeNegProd : ℕ := ∏ i : PrimeIdx k, p i ^ zneg (rBM (Sum.inl i))
  let intPosProd : ℕ := ∏ j : IntIdx ν, bmIntVal ν j ^ zpos (rBM (Sum.inr j))
  let intNegProd : ℕ := ∏ j : IntIdx ν, bmIntVal ν j ^ zneg (rBM (Sum.inr j))
  let A : ℕ := ((2 ^ zneg z) * primePosProd) * intPosProd
  let B : ℕ := ((2 ^ zpos z) * primeNegProd) * intNegProd
  have hp_ne_zero : ∀ i, p i ≠ 0 := fun i => (hpPrime i).ne_zero
  have hint_ne_zero : ∀ j, bmIntVal ν j ≠ 0 := fun j => (bmIntVal_pos ν hν j).ne'
  have hPrimeLog :
      Real.logb 2 (primePosProd : ℝ) - Real.logb 2 (primeNegProd : ℝ) =
        ∑ i : PrimeIdx k, Real.logb 2 (p i : ℝ) * (rBM (Sum.inl i) : ℝ) := by
    simpa [primePosProd, primeNegProd, rBM, mul_comm, mul_left_comm, mul_assoc] using
      (logb_nat_fintype_prod_zparts p (fun i => rBM (Sum.inl i)) hp_ne_zero)
  have hIntLog :
      Real.logb 2 (intPosProd : ℝ) - Real.logb 2 (intNegProd : ℝ) =
        ∑ j : IntIdx ν, Real.logb 2 (bmIntVal ν j : ℝ) * (rBM (Sum.inr j) : ℝ) := by
    simpa [intPosProd, intNegProd, rBM, mul_comm, mul_left_comm, mul_assoc] using
      (logb_nat_fintype_prod_zparts (bmIntVal ν) (fun j => rBM (Sum.inr j)) hint_ne_zero)
  have hprimePos_ne : primePosProd ≠ 0 := by
    dsimp [primePosProd]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact pow_ne_zero _ (hp_ne_zero i)
  have hprimeNeg_ne : primeNegProd ≠ 0 := by
    dsimp [primeNegProd]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact pow_ne_zero _ (hp_ne_zero i)
  have hintPos_ne : intPosProd ≠ 0 := by
    dsimp [intPosProd]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact pow_ne_zero _ (hint_ne_zero j)
  have hintNeg_ne : intNegProd ≠ 0 := by
    dsimp [intNegProd]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact pow_ne_zero _ (hint_ne_zero j)
  have hAlog :
      Real.logb 2 (A : ℝ) =
        zneg z + Real.logb 2 (primePosProd : ℝ) + Real.logb 2 (intPosProd : ℝ) := by
    dsimp [A]
    rw [logb_nat_mul (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimePos_ne) hintPos_ne,
      logb_nat_mul (pow_ne_zero _ two_ne_zero) hprimePos_ne]
    simp [Real.logb_pow, add_assoc]
  have hBlog :
      Real.logb 2 (B : ℝ) =
        zpos z + Real.logb 2 (primeNegProd : ℝ) + Real.logb 2 (intNegProd : ℝ) := by
    dsimp [B]
    rw [logb_nat_mul (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimeNeg_ne) hintNeg_ne,
      logb_nat_mul (pow_ne_zero _ two_ne_zero) hprimeNeg_ne]
    simp [Real.logb_pow, add_assoc]
  have hlogEq : Real.logb 2 (A : ℝ) = Real.logb 2 (B : ℝ) := by
    nlinarith [hzSplit, hPrimeLog, hIntLog, hAlog, hBlog, cast_zpos_sub_zneg z]
  have hA_pos : 0 < (A : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (show A ≠ 0 by
    dsimp [A]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimePos_ne) hintPos_ne)
  have hB_pos : 0 < (B : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (show B ≠ 0 by
    dsimp [B]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimeNeg_ne) hintNeg_ne)
  have hABreal : (A : ℝ) = (B : ℝ) := by
    exact Real.logb_injOn_pos one_lt_two (Set.mem_Ioi.2 hA_pos) (Set.mem_Ioi.2 hB_pos) hlogEq
  have hAB : A = B := by exact_mod_cast hABreal
  have hprimeCoeffZero : ∀ i : PrimeIdx k, rBM (Sum.inl i) = 0 := by
    intro i
    rcases lt_trichotomy (rBM (Sum.inl i)) 0 with hneg | hzero | hpos
    · exfalso
      have hdivFactor : p i ∣ p i ^ zneg (rBM (Sum.inl i)) := by
        exact dvd_pow_self _ (zneg_pos_of_neg hneg).ne'
      have hdivPrimeNeg : p i ∣ primeNegProd := by
        dsimp [primeNegProd]
        exact dvd_trans hdivFactor
          (Finset.dvd_prod_of_mem (fun i' : PrimeIdx k => p i' ^ zneg (rBM (Sum.inl i')))
            (Finset.mem_univ i))
      have hdivB : p i ∣ B := by
        have hfirst : p i ∣ (2 ^ zpos z) * primeNegProd := by
          exact dvd_mul_of_dvd_right hdivPrimeNeg (2 ^ zpos z)
        simpa [B, mul_assoc, mul_left_comm, mul_comm] using
          dvd_mul_of_dvd_right hfirst intNegProd
      have htwo_gt : 2 < p i := lt_of_le_of_ne (hpPrime i).two_le
        (Ne.symm (bm_prime_ne_two hν p hp_window i))
      have hnotTwo : ¬ p i ∣ 2 := by
        have hcop : Nat.Coprime (p i) 2 :=
          Nat.coprime_of_lt_prime (by decide) htwo_gt (hpPrime i)
        exact (hpPrime i).coprime_iff_not_dvd.mp hcop
      have hnotPrimePos : ¬ p i ∣ primePosProd := by
        dsimp [primePosProd]
        apply Prime.not_dvd_finset_prod (p := p i) (hpPrime i).prime
        intro i' hi'
        by_cases hii' : i = i'
        · subst hii'
          simp [zpos_eq_zero_of_nonpos hneg.le, (hpPrime i).ne_one]
        · exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
            (bm_prime_not_dvd_other_prime p hpPrime hpPairwise hii')
      have hnotIntPos : ¬ p i ∣ intPosProd := by
        dsimp [intPosProd]
        apply Prime.not_dvd_finset_prod (p := p i) (hpPrime i).prime
        intro j hj
        exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
          (bm_prime_not_dvd_intVal hν p hpPrime hp_window i j)
      have hnotA : ¬ p i ∣ A := by
        dsimp [A]
        have hnotFirst : ¬ p i ∣ (2 ^ zneg z) * primePosProd :=
          Nat.Prime.not_dvd_mul (hpPrime i)
            (prime_not_dvd_pow_of_not_dvd (hpPrime i) hnotTwo) hnotPrimePos
        exact Nat.Prime.not_dvd_mul (hpPrime i) hnotFirst hnotIntPos
      exact hnotA (hAB ▸ hdivB)
    · exact hzero
    · exfalso
      have hdivFactor : p i ∣ p i ^ zpos (rBM (Sum.inl i)) := by
        exact dvd_pow_self _ (zpos_pos_of_pos hpos).ne'
      have hdivPrimePos : p i ∣ primePosProd := by
        dsimp [primePosProd]
        exact dvd_trans hdivFactor
          (Finset.dvd_prod_of_mem (fun i' : PrimeIdx k => p i' ^ zpos (rBM (Sum.inl i')))
            (Finset.mem_univ i))
      have hdivA : p i ∣ A := by
        have hfirst : p i ∣ (2 ^ zneg z) * primePosProd := by
          exact dvd_mul_of_dvd_right hdivPrimePos (2 ^ zneg z)
        simpa [A, mul_assoc, mul_left_comm, mul_comm] using
          dvd_mul_of_dvd_right hfirst intPosProd
      have htwo_gt : 2 < p i := lt_of_le_of_ne (hpPrime i).two_le
        (Ne.symm (bm_prime_ne_two hν p hp_window i))
      have hnotTwo : ¬ p i ∣ 2 := by
        have hcop : Nat.Coprime (p i) 2 :=
          Nat.coprime_of_lt_prime (by decide) htwo_gt (hpPrime i)
        exact (hpPrime i).coprime_iff_not_dvd.mp hcop
      have hnotPrimeNeg : ¬ p i ∣ primeNegProd := by
        dsimp [primeNegProd]
        apply Prime.not_dvd_finset_prod (p := p i) (hpPrime i).prime
        intro i' hi'
        by_cases hii' : i = i'
        · subst hii'
          simp [zneg_eq_zero_of_nonneg hpos.le, (hpPrime i).ne_one]
        · exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
            (bm_prime_not_dvd_other_prime p hpPrime hpPairwise hii')
      have hnotIntNeg : ¬ p i ∣ intNegProd := by
        dsimp [intNegProd]
        apply Prime.not_dvd_finset_prod (p := p i) (hpPrime i).prime
        intro j hj
        exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
          (bm_prime_not_dvd_intVal hν p hpPrime hp_window i j)
      have hnotB : ¬ p i ∣ B := by
        dsimp [B]
        have hnotFirst : ¬ p i ∣ (2 ^ zpos z) * primeNegProd :=
          Nat.Prime.not_dvd_mul (hpPrime i)
            (prime_not_dvd_pow_of_not_dvd (hpPrime i) hnotTwo) hnotPrimeNeg
        exact Nat.Prime.not_dvd_mul (hpPrime i) hnotFirst hnotIntNeg
      exact hnotB (hAB ▸ hdivA)
  refine ⟨0, ?_⟩
  have hbetaBM :
      ∑ x : BMIdx k ν, bmBeta k ν x * (rBM x : ℝ) = 0 := by
    rw [Fintype.sum_sum_type]
    simp [bmBeta, hprimeCoeffZero, rBM]
  have hbetaFlat :
      ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatBeta k ν j * (r j : ℝ) = 0 := by
    have hbetaFlat' :
        ∑ x : BMIdx k ν, bmBeta k ν x * (rBM x : ℝ) =
          ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatBeta k ν j * (r j : ℝ) := by
      exact Fintype.sum_equiv (bmFlatEquiv k ν)
        (fun x : BMIdx k ν => bmBeta k ν x * (rBM x : ℝ))
        (fun j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) => bmFlatBeta k ν j * (r j : ℝ))
        (fun x => by
          cases x with
          | inl i =>
              simp [rBM, bmFlatBeta, bmBeta, bmFlatEquiv]
          | inr j =>
              simp [rBM, bmFlatBeta, bmBeta, bmFlatEquiv])
    exact hbetaFlat'.symm.trans hbetaBM
  simpa using hbetaFlat

lemma bm_prime_mul_mem_window (ν : ℕ) {p y : ℝ}
    (hp : p ∈ Ioo (((23 : ℝ) / 16) * 2 ^ ν) (((3 : ℝ) / 2) * 2 ^ ν))
    (hy : y ∈ I_inf) :
    p * y ∈ Ioo (((8 : ℝ) / 9) * 2 ^ ν) ((2 : ℝ) ^ ν) := by
  rcases hp with ⟨hp_lower, hp_upper⟩
  rcases hy with ⟨hy_lower, hy_upper⟩
  have hy_pos : 0 < y := by linarith
  constructor
  · have hp_times_y : (((23 : ℝ) / 16) * 2 ^ ν) * y < p * y := by
      exact mul_lt_mul_of_pos_right hp_lower hy_pos
    have hlower :
        (((23 : ℝ) / 16) * 2 ^ ν) * ((16 : ℝ) / 25) ≤
          (((23 : ℝ) / 16) * 2 ^ ν) * y := by
      gcongr
    have hnum :
        (((8 : ℝ) / 9) * 2 ^ ν) <
          (((23 : ℝ) / 16) * 2 ^ ν) * ((16 : ℝ) / 25) := by
      have hpow : 0 < (2 : ℝ) ^ ν := by positivity
      nlinarith
    exact lt_trans hnum (lt_of_le_of_lt hlower hp_times_y)
  · have hp_pos : 0 < p := by linarith
    have hy_times_p : p * y ≤ p * ((2 : ℝ) / 3) := by
      gcongr
    have hupper : p * ((2 : ℝ) / 3) < (((3 : ℝ) / 2) * 2 ^ ν) * ((2 : ℝ) / 3) := by
      exact mul_lt_mul_of_pos_right hp_upper (by norm_num)
    have hnum : (((3 : ℝ) / 2) * 2 ^ ν) * ((2 : ℝ) / 3) = (2 : ℝ) ^ ν := by
      ring
    simpa [hnum] using lt_of_le_of_lt hy_times_p hupper

lemma bm_half_grid_not_near_integer (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    ¬ |(m : ℝ) + 1 / (2 : ℝ) ^ k| < 1 / (4 * (2 : ℝ) ^ k) := by
  have hkpow : 0 < (2 : ℝ) ^ k := by positivity
  have hfrac_pos : 0 < 1 / (2 : ℝ) ^ k := by positivity
  have hpow_le : (2 : ℝ) ≤ 2 ^ k := by
    simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk
  have hfrac_le_half : 1 / (2 : ℝ) ^ k ≤ 1 / 2 := by
    simpa [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow_le)
  have hquarter : 1 / (4 * (2 : ℝ) ^ k) < 1 / (2 : ℝ) ^ k := by
    field_simp [hkpow.ne']
    nlinarith
  intro h
  rcases lt_or_ge m 0 with hm_neg | hm_nonneg
  · have hm_le : (m : ℝ) ≤ -1 := by
      exact_mod_cast (Int.le_sub_one_iff.mpr hm_neg)
    have habs_ge : 1 / (2 : ℝ) ^ k ≤ |(m : ℝ) + 1 / (2 : ℝ) ^ k| := by
      rw [abs_of_nonpos]
      · nlinarith
      · nlinarith
    have hsmall : |(m : ℝ) + 1 / (2 : ℝ) ^ k| < 1 / (2 : ℝ) ^ k := by
      exact lt_trans h hquarter
    exact (not_lt_of_ge habs_ge) hsmall
  · have hm_ge : (0 : ℝ) ≤ m := by exact_mod_cast hm_nonneg
    have habs_ge : 1 / (2 : ℝ) ^ k ≤ |(m : ℝ) + 1 / (2 : ℝ) ^ k| := by
      rw [abs_of_nonneg]
      · have : (1 / (2 : ℝ) ^ k : ℝ) ≤ (m : ℝ) + 1 / (2 : ℝ) ^ k := by
          nlinarith
        exact this
      · positivity
    have hsmall : |(m : ℝ) + 1 / (2 : ℝ) ^ k| < 1 / (2 : ℝ) ^ k := by
      exact lt_trans h hquarter
    exact (not_lt_of_ge habs_ge) hsmall

lemma bm_q_nonzero_of_first_prime_target
    {k : ℕ} (hk : 1 ≤ k) {q : ℤ} {p : ℤ} {a : ℝ}
    (hq :
      |(q : ℝ) * a - (p : ℝ) - 1 / (2 : ℝ) ^ k| <
        1 / (4 * (2 : ℝ) ^ k)) :
    q ≠ 0 := by
  intro hzero
  let s : ℝ := (p : ℝ) + 1 / (2 : ℝ) ^ k
  have hneg : |-s| < 1 / (4 * (2 : ℝ) ^ k) := by
    convert hq using 1
    · simp [s, hzero, sub_eq_add_neg, add_comm]
  have hrew : |s| < 1 / (4 * (2 : ℝ) ^ k) := by
    simpa [abs_neg] using hneg
  exact (bm_half_grid_not_near_integer k hk p) hrew

/-- BM-facing Kronecker wrapper: the common denominator can be chosen nonzero because one
prime-block target is the nonintegral point `1 / 2^k`. -/
lemma bm_common_q_int_nonzero
    {k ν : ℕ} (hk : 1 ≤ k) (p : PrimeIdx k → ℕ)
    (h_intrel :
      ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
        (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
        ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z) :
    ∃ q : ℤ, q ≠ 0 ∧ ∃ m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k) := by
  obtain ⟨q, m, hm⟩ :=
    kronecker_intrel_implies_approx_common_q_int
      (2 ^ k + (2 ^ (ν - 2) + 1)) (bmFlatAlpha p) (bmFlatBeta k ν) h_intrel
      (1 / (4 * (2 : ℝ) ^ k)) (by positivity)
  refine ⟨q, ?_, m, hm⟩
  have hcoord :
      |(q : ℝ) * bmFlatAlpha p
            (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk)) -
          (m (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk)) : ℝ) -
          1 / (2 : ℝ) ^ k| <
        1 / (4 * (2 : ℝ) ^ k) := by
    simpa [bmFlatBeta_primeIdxOne_eq k ν hk] using
      hm (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk))
  exact bm_q_nonzero_of_first_prime_target hk hcoord

lemma int_sign_mul_div_natAbs (q m : ℤ) (hq : q ≠ 0) :
    (((Int.sign q * m : ℤ) : ℝ) / (Int.natAbs q : ℝ)) = (m : ℝ) / (q : ℝ) := by
  rcases lt_trichotomy q 0 with hqneg | rfl | hqpos
  · have hsign : Int.sign q = -1 := Int.sign_eq_neg_one_of_neg hqneg
    have hqabs : (Int.natAbs q : ℝ) = -(q : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg]
      exact_mod_cast hqneg
    have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hqneg.ne
    calc
      (((Int.sign q * m : ℤ) : ℝ) / (Int.natAbs q : ℝ))
          = ((-(m : ℝ)) / (-(q : ℝ))) := by simp [hsign, hqabs]
      _ = (m : ℝ) / (q : ℝ) := by field_simp [hqreal]
  · contradiction
  · have hsign : Int.sign q = 1 := Int.sign_eq_one_of_pos hqpos
    have hqabs : (Int.natAbs q : ℝ) = (q : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos]
      exact_mod_cast hqpos
    simp [hsign, hqabs]

lemma bm_integer_lattice_of_common_q
    {k ν : ℕ} {p : PrimeIdx k → ℕ} {q : ℤ}
    (hq : q ≠ 0)
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k))
    {n : ℕ}
    (hn : (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν))
    (hν : 3 ≤ ν) :
    ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (Int.natAbs q : ℝ)| <
      1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
  obtain ⟨j, rfl⟩ := exists_bmIntVal_eq_of_mem_Ioo ν hν hn
  let idx : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) := Fin.natAdd (2 ^ k) j
  let z : ℤ := Int.sign q * m idx
  refine ⟨z, ?_⟩
  have hcoord :
      |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ)| <
        1 / (4 * (2 : ℝ) ^ k) := by
    simpa [idx, bmFlatAlpha_natAdd, bmFlatBeta_natAdd, sub_eq_add_neg] using hm idx
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqabs_pos : 0 < |(q : ℝ)| := by
    exact abs_pos.mpr hqreal
  have hscaled :
      |Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ)| <
        (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| := by
    have hmul :
        |(q : ℝ)| *
            |Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |(q : ℝ)| * |Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ)|
            = |(q : ℝ) * (Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ))| := by
                rw [abs_mul]
        _ = |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ)| := by
              congr 1
              field_simp [hq]
        _ < 1 / (4 * (2 : ℝ) ^ k) := by simpa [abs_sub_comm] using hcoord
    exact (lt_div_iff₀ hqabs_pos).2 (by simpa [mul_comm] using hmul)
  have hrewrite :
      ((z : ℝ) / (Int.natAbs q : ℝ)) = (m idx : ℝ) / (q : ℝ) := by
    simpa [z] using int_sign_mul_div_natAbs q (m idx) hq
  rw [hrewrite]
  have hqabs_cast : (Int.natAbs q : ℝ) = |(q : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hqabs_cast_pos : 0 < (Int.natAbs q : ℝ) := by
    rw [hqabs_cast]
    exact hqabs_pos
  have htarget :
      (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| =
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
    rw [← hqabs_cast]
    field_simp [hqabs_cast_pos.ne']
  rw [hqabs_cast]
  convert hscaled using 1
  ring_nf

lemma bm_prime_coordinate_of_common_q
    {k ν : ℕ} {p : PrimeIdx k → ℕ} {q : ℤ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k))
    (i : PrimeIdx k) :
    |(q : ℝ) * Real.logb 2 (p i) - (m (Fin.castAdd (2 ^ (ν - 2) + 1) i) : ℝ) -
        (i : ℝ) / (2 : ℝ) ^ k| <
      1 / (4 * (2 : ℝ) ^ k) := by
  simpa [bmFlatAlpha_castAdd, bmFlatBeta_castAdd] using
    hm (Fin.castAdd (2 ^ (ν - 2) + 1) i)

lemma bm_integer_coordinate_of_common_q
    {k ν : ℕ} {p : PrimeIdx k → ℕ} {q : ℤ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k))
    (j : IntIdx ν) :
    |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (m (Fin.natAdd (2 ^ k) j) : ℝ)| <
      1 / (4 * (2 : ℝ) ^ k) := by
  simpa [bmFlatAlpha_natAdd, bmFlatBeta_natAdd, sub_eq_add_neg] using
    hm (Fin.natAdd (2 ^ k) j)

lemma bm_kronecker_coordinate_data
    {k ν : ℕ} (hk : 1 ≤ k) (p : PrimeIdx k → ℕ)
    (h_intrel :
      ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
        (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
        ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z) :
    ∃ q : ℤ, q ≠ 0 ∧ ∃ m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
      (∀ i : PrimeIdx k,
        |(q : ℝ) * Real.logb 2 (p i) -
            (m (Fin.castAdd (2 ^ (ν - 2) + 1) i) : ℝ) -
            (i : ℝ) / (2 : ℝ) ^ k| <
          1 / (4 * (2 : ℝ) ^ k)) ∧
      (∀ j : IntIdx ν,
        |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) -
            (m (Fin.natAdd (2 ^ k) j) : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k)) := by
  obtain ⟨q, hq, m, hm⟩ := bm_common_q_int_nonzero hk p h_intrel
  refine ⟨q, hq, m, ?_, ?_⟩
  · intro i
    exact bm_prime_coordinate_of_common_q hm i
  · intro j
    exact bm_integer_coordinate_of_common_q hm j

lemma bm_nearest_grid (q k : ℕ) (hq : 0 < q) (x : ℝ) :
    ∃ j : PrimeIdx k, ∃ n : ℤ,
      |x + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n : ℝ) / (q : ℝ)| ≤
        1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
  let N : ℕ := 2 ^ k
  let t : ℝ := (q : ℝ) * (N : ℝ) * x
  let M : ℤ := round t
  let r : ℤ := (-M) % N
  let n : ℤ := -((-M) / N)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hr_nonneg : 0 ≤ r := by
    dsimp [r, N]
    exact Int.emod_nonneg _ (by exact_mod_cast hN_pos.ne')
  have hr_lt : r < N := by
    dsimp [r, N]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast hN_pos)
  have hr_lt_nat : Int.toNat r < N := by
    exact (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hN_pos)).2 (by simpa [N] using hr_lt)
  let j : PrimeIdx k := ⟨Int.toNat r, by
    simpa [N] using hr_lt_nat⟩
  refine ⟨j, n, ?_⟩
  have hj_eq_int : ((j : ℕ) : ℤ) = r := by
    dsimp [j]
    simp [Int.toNat_of_nonneg hr_nonneg]
  have hj_eq : (j : ℝ) = r := by
    exact_mod_cast hj_eq_int
  have hdecomp : (N : ℤ) * ((-M) / N) + (-M) % N = -M := by
    simpa [N] using (Int.mul_ediv_add_emod (-M) N)
  have hdecompZ : r - (N : ℤ) * n = -M := by
    dsimp [r, n]
    linarith
  have hdecomp' : (r : ℝ) - (N : ℝ) * (n : ℝ) = -(M : ℝ) := by
    exact_mod_cast hdecompZ
  have hround : |t - M| ≤ 1 / 2 := by
    simpa [t, M] using (abs_sub_round t)
  have hqN_pos : 0 < (q : ℝ) * (N : ℝ) := by
    positivity
  have hmul :
      ((q : ℝ) * (N : ℝ)) *
          |x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        1 / 2 := by
    calc
      ((q : ℝ) * (N : ℝ)) *
          |x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)|
          = |((q : ℝ) * (N : ℝ)) *
              (x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ))| := by
              rw [abs_mul, abs_of_pos hqN_pos]
      _ = |t - M| := by
            congr 1
            dsimp [t]
            have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
            have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
            field_simp [hqreal, hNreal]
            linarith [hdecomp']
      _ ≤ 1 / 2 := hround
  have hbound :
      |x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        (1 / 2) / ((q : ℝ) * (N : ℝ)) := by
    exact (le_div_iff₀ hqN_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hbound' :
      |x + (j : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        (1 / 2) / ((q : ℝ) * (N : ℝ)) := by
    simpa [hj_eq] using hbound
  have htarget :
      (1 / 2 : ℝ) / ((q : ℝ) * (N : ℝ)) = 1 / (2 * (q : ℝ) * (N : ℝ)) := by
    have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    field_simp [hqreal, hNreal]
  have hbound'' :
      |x + (j : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        1 / (2 * (q : ℝ) * (N : ℝ)) := by
    exact htarget ▸ hbound'
  simpa [N] using hbound''

lemma bm_prime_cover_of_positive_q
    {k ν q : ℕ} (hq : 0 < q)
    (p : PrimeIdx k → ℕ) (a : PrimeIdx k → ℤ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (happrox :
      ∀ i,
        |(q : ℝ) * Real.logb 2 (p i : ℝ) - (a i : ℝ) - (i : ℝ) / (2 : ℝ) ^ k| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
      (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * (2 : ℝ) ^ ν) ((2 : ℝ) ^ ν) ∧
      ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
  intro y hy
  obtain ⟨j, n₀, hgrid⟩ := bm_nearest_grid q k hq (Real.logb 2 y)
  have hqreal_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have happrox_div :
      |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
          (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
        1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
    have hmul :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ) <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ)
            = (q : ℝ) *
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                    (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by ring
        _ = |(q : ℝ) *
                (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| := by
              rw [abs_mul, abs_of_pos hqreal_pos]
        _ = |(q : ℝ) * Real.logb 2 (p j : ℝ) - (a j : ℝ) - (j : ℝ) / (2 : ℝ) ^ k| := by
              congr 1
              field_simp [hq.ne']
        _ < 1 / (4 * (2 : ℝ) ^ k) := happrox j
    have hdiv :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
          (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) := by
      exact (lt_div_iff₀ hqreal_pos).2 hmul
    have htarget :
        (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) =
          1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
      have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp [hqreal]
    exact htarget ▸ hdiv
  have hpj_mem :
      (p j : ℝ) ∈ Ioo (((23 : ℝ) / 16) * (2 : ℝ) ^ ν) (((3 : ℝ) / 2) * (2 : ℝ) ^ ν) := hp_window j
  have hpj_pos : 0 < p j := by
    have hpj_pos_real : 0 < (p j : ℝ) := by
      rcases hpj_mem with ⟨hpj_lower, _⟩
      have : 0 < ((23 : ℝ) / 16) * (2 : ℝ) ^ ν := by positivity
      linarith
    exact_mod_cast hpj_pos_real
  have hsum :
      |Real.logb 2 y + Real.logb 2 (p j : ℝ) - ((n₀ + a j : ℤ) : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
    have htri :
        |(Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)) +
            (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
              (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| <
          1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
      have hnorm :
          |(Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)) +
              (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| ≤
            |Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by
        exact abs_add_le _ _
      have hbound :
          |Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
            1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
        have hsum_lt :
            |Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)| +
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
              1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
          nlinarith
        have htarget :
            1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) <
              1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
          have hq2k_pos : 0 < (q : ℝ) * (2 : ℝ) ^ k := by positivity
          have hq2k_ne : (q : ℝ) * (2 : ℝ) ^ k ≠ 0 := hq2k_pos.ne'
          field_simp [hq2k_ne]
          nlinarith
        exact lt_trans hsum_lt htarget
      exact lt_of_le_of_lt hnorm hbound
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using htri
  refine ⟨p j, hpj_pos, bm_prime_mul_mem_window ν hpj_mem hy, ?_⟩
  refine ⟨n₀ + a j, ?_⟩
  have hy_pos : 0 < y := by
    rcases hy with ⟨hy₁, _⟩
    linarith
  rw [Real.logb_mul] <;> try positivity
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using hsum

lemma bm_prime_cover_of_negative_q
    {k ν q : ℕ} (hq : 0 < q)
    (p : PrimeIdx k → ℕ) (a : PrimeIdx k → ℤ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (happrox :
      ∀ i,
        |(q : ℝ) * Real.logb 2 (p i : ℝ) - (a i : ℝ) + (i : ℝ) / (2 : ℝ) ^ k| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
      (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * (2 : ℝ) ^ ν) ((2 : ℝ) ^ ν) ∧
      ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
  intro y hy
  obtain ⟨j, n₀, hgrid_raw⟩ := bm_nearest_grid q k hq (-Real.logb 2 y)
  have hgrid :
      |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| ≤
        1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
    let t : ℝ :=
      Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)
    have htmp : |-t| ≤ 1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
      have hEq :
          -t =
            -Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ) := by
        dsimp [t]
        have hdiv : -((n₀ : ℝ) / (q : ℝ)) = -(n₀ : ℝ) / (q : ℝ) := by ring
        simp [sub_eq_add_neg, add_comm, Int.cast_neg, hdiv]
      rw [hEq]
      exact hgrid_raw
    have htarget : |t| ≤ 1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
      simpa [abs_neg] using htmp
    simpa [t] using htarget
  have hqreal_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have happrox_div :
      |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
        1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
    have hmul :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ) <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ)
            = (q : ℝ) *
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                    (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by ring
        _ = |(q : ℝ) *
                (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| := by
              rw [abs_mul, abs_of_pos hqreal_pos]
        _ = |(q : ℝ) * Real.logb 2 (p j : ℝ) - (a j : ℝ) + (j : ℝ) / (2 : ℝ) ^ k| := by
              congr 1
              field_simp [hq.ne']
        _ < 1 / (4 * (2 : ℝ) ^ k) := happrox j
    have hdiv :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
          (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) := by
      exact (lt_div_iff₀ hqreal_pos).2 hmul
    have htarget :
        (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) =
          1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
      have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp [hqreal]
    exact htarget ▸ hdiv
  have hpj_mem :
      (p j : ℝ) ∈ Ioo (((23 : ℝ) / 16) * (2 : ℝ) ^ ν) (((3 : ℝ) / 2) * (2 : ℝ) ^ ν) := hp_window j
  have hpj_pos : 0 < p j := by
    have hpj_pos_real : 0 < (p j : ℝ) := by
      rcases hpj_mem with ⟨hpj_lower, _⟩
      have : 0 < ((23 : ℝ) / 16) * (2 : ℝ) ^ ν := by positivity
      linarith
    exact_mod_cast hpj_pos_real
  have hsum :
      |Real.logb 2 y + Real.logb 2 (p j : ℝ) - (((-n₀ + a j : ℤ) : ℝ) / (q : ℝ))| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
    have htri :
        |(Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)) +
            (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
              (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| <
          1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
      have hnorm :
          |(Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)) +
              (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| ≤
            |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by
        exact abs_add_le _ _
      have hbound :
          |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
            1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
        have hsum_lt :
            |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| +
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
              1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
          nlinarith
        have htarget :
            1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) <
              1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
          have hq2k_pos : 0 < (q : ℝ) * (2 : ℝ) ^ k := by positivity
          have hq2k_ne : (q : ℝ) * (2 : ℝ) ^ k ≠ 0 := hq2k_pos.ne'
          field_simp [hq2k_ne]
          nlinarith
        exact lt_trans hsum_lt htarget
      exact lt_of_le_of_lt hnorm hbound
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using htri
  refine ⟨p j, hpj_pos, bm_prime_mul_mem_window ν hpj_mem hy, ?_⟩
  refine ⟨-n₀ + a j, ?_⟩
  have hy_pos : 0 < y := by
    rcases hy with ⟨hy₁, _⟩
    linarith
  rw [Real.logb_mul] <;> try positivity
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using hsum

lemma bm_integer_cover_of_nonzero_q
    {k ν : ℕ} {q : ℤ} (hq : q ≠ 0) (hν : 3 ≤ ν)
    {p : PrimeIdx k → ℕ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ n : ℕ, (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) →
      ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (Int.natAbs q : ℝ)| <
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
  intro n hn
  exact bm_integer_lattice_of_common_q hq hm hn hν

lemma bm_integer_cover_of_coordinate_data
    {k ν : ℕ} {q : ℤ} (hq : q ≠ 0) (hν : 3 ≤ ν)
    (a : IntIdx ν → ℤ)
    (happrox :
      ∀ j : IntIdx ν,
        |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ n : ℕ, (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) →
      ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (Int.natAbs q : ℝ)| <
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
  intro n hn
  obtain ⟨j, rfl⟩ := exists_bmIntVal_eq_of_mem_Ioo ν hν hn
  let z : ℤ := Int.sign q * a j
  refine ⟨z, ?_⟩
  have hcoord :
      |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ)| <
        1 / (4 * (2 : ℝ) ^ k) := happrox j
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqabs_pos : 0 < |(q : ℝ)| := by
    exact abs_pos.mpr hqreal
  have hscaled :
      |Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ)| <
        (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| := by
    have hmul :
        |(q : ℝ)| *
            |Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |(q : ℝ)| *
            |Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ)|
            = |(q : ℝ) * (Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ))| := by
                rw [abs_mul]
        _ = |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ)| := by
              congr 1
              field_simp [hq]
        _ < 1 / (4 * (2 : ℝ) ^ k) := by simpa [abs_sub_comm] using hcoord
    exact (lt_div_iff₀ hqabs_pos).2 (by simpa [mul_comm] using hmul)
  have hrewrite :
      ((z : ℝ) / (Int.natAbs q : ℝ)) = (a j : ℝ) / (q : ℝ) := by
    simpa [z] using int_sign_mul_div_natAbs q (a j) hq
  rw [hrewrite]
  have hqabs_cast : (Int.natAbs q : ℝ) = |(q : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hqabs_cast_pos : 0 < (Int.natAbs q : ℝ) := by
    rw [hqabs_cast]
    exact hqabs_pos
  have htarget :
      (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| =
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
    rw [← hqabs_cast]
    field_simp [hqabs_cast_pos.ne']
  rw [hqabs_cast]
  convert hscaled using 1
  ring_nf

lemma bm_integer_cover_of_positive_q
    {k ν q : ℕ} (hq : 0 < q) (hν : 3 ≤ ν)
    {p : PrimeIdx k → ℕ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |((q : ℤ) : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ n : ℕ, (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) →
      ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (q : ℝ)| <
        1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
  intro n hn
  obtain ⟨z, hz⟩ :=
    bm_integer_lattice_of_common_q
      (k := k) (ν := ν) (p := p) (q := (q : ℤ))
      (by exact_mod_cast hq.ne') hm hn hν
  refine ⟨z, ?_⟩
  simpa using hz

lemma bm_approx_data_of_positive_flat_data
    (hData :
      ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
        ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
          ∃ q : ℕ, 0 < q ∧
            ∃ p : PrimeIdx k → ℕ,
              (∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
                    (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν) ∧
              ∃ m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
                (∀ j,
                  |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
                    1 / (4 * (2 : ℝ) ^ k))) :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ q : ℕ, 0 < q ∧
          (∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
            (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
            ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
              1 / ((q : ℝ) * 2 ^ k)) ∧
          (∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
            ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
              1 / (4 * (q : ℝ) * 2 ^ k)) := by
  obtain ⟨K₀, hK₀⟩ := hData
  refine ⟨K₀, fun k hk => ?_⟩
  obtain ⟨N_k, hN_k⟩ := hK₀ k hk
  refine ⟨max N_k 3, fun ν hν => ?_⟩
  obtain ⟨q, hq, p, hp_window, m, hm⟩ := hN_k ν ((le_max_left N_k 3).trans hν)
  refine ⟨q, hq, ?_, ?_⟩
  · exact bm_prime_cover_of_positive_q hq p
      (fun i => m (Fin.castAdd (2 ^ (ν - 2) + 1) i))
      hp_window
      (fun i => by simpa using bm_prime_coordinate_of_common_q hm i)
  · exact bm_integer_cover_of_positive_q hq ((le_max_right N_k 3).trans hν) hm

/-- **Kronecker–PNT approximation data** for the BM construction. -/
lemma bm_approx_data :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ q : ℕ, 0 < q ∧
          (∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
            (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
            ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
              1 / ((q : ℝ) * 2 ^ k)) ∧
          (∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
            ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
              1 / (4 * (q : ℝ) * 2 ^ k)) := by
  refine ⟨1, ?_⟩
  intro k hk
  obtain ⟨Np, hNp⟩ := bm_many_primes k
  refine ⟨max Np 3, ?_⟩
  intro ν hν
  have hνp : Np ≤ ν := (le_max_left Np 3).trans hν
  have hν3 : 3 ≤ ν := (le_max_right Np 3).trans hν
  obtain ⟨p, hpPairwise, hpPrime, hpWindow⟩ := hNp ν hνp
  have hIntrel :
      ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
        (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
        ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z :=
    bm_flat_intrel_of_prime_window hν3 p hpPairwise hpPrime hpWindow
  obtain ⟨qInt, hqInt, m, hPrimeCoords, hIntCoords⟩ :=
    bm_kronecker_coordinate_data hk p hIntrel
  let q : ℕ := Int.natAbs qInt
  have hq : 0 < q := Int.natAbs_pos.mpr hqInt
  refine ⟨q, hq, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hqInt with hqNeg | hqPos
    · have hqabs : (q : ℝ) = -(qInt : ℝ) := by
        have hqabs_int : ((Int.natAbs qInt : ℕ) : ℤ) = -qInt := by
          rw [Int.natCast_natAbs, abs_of_neg hqNeg]
        have hqabs_real : (((Int.natAbs qInt : ℕ) : ℤ) : ℝ) = ((-qInt : ℤ) : ℝ) := by
          exact_mod_cast hqabs_int
        dsimp [q]
        simpa using hqabs_real
      let aNeg : PrimeIdx k → ℤ := fun i => -m (Fin.castAdd (2 ^ (ν - 2) + 1) i)
      have happroxNeg :
          ∀ i,
            |(q : ℝ) * Real.logb 2 (p i : ℝ) - (aNeg i : ℝ) + (i : ℝ) / (2 : ℝ) ^ k| <
              1 / (4 * (2 : ℝ) ^ k) := by
        intro i
        have hi := hPrimeCoords i
        have hi_neg :
            |-( (qInt : ℝ) * Real.logb 2 (p i : ℝ) -
                (m (Fin.castAdd (2 ^ (ν - 2) + 1) i) : ℝ) -
                (i : ℝ) / (2 : ℝ) ^ k)| <
              1 / (4 * (2 : ℝ) ^ k) := by
          convert hi using 1
          rw [abs_neg]
        rw [hqabs]
        convert hi_neg using 1
        · simp [aNeg]
          ring_nf
      exact bm_prime_cover_of_negative_q hq p aNeg hpWindow happroxNeg
    · have hqabs : (q : ℝ) = (qInt : ℝ) := by
        have hqabs_int : ((Int.natAbs qInt : ℕ) : ℤ) = qInt := by
          rw [Int.natCast_natAbs, abs_of_nonneg hqPos.le]
        have hqabs_real : (((Int.natAbs qInt : ℕ) : ℤ) : ℝ) = (qInt : ℝ) := by
          exact_mod_cast hqabs_int
        dsimp [q]
        simpa using hqabs_real
      let aPos : PrimeIdx k → ℤ := fun i => m (Fin.castAdd (2 ^ (ν - 2) + 1) i)
      have happroxPos :
          ∀ i,
            |(q : ℝ) * Real.logb 2 (p i : ℝ) - (aPos i : ℝ) - (i : ℝ) / (2 : ℝ) ^ k| <
              1 / (4 * (2 : ℝ) ^ k) := by
        intro i
        rw [hqabs]
        simpa [aPos] using hPrimeCoords i
      exact bm_prime_cover_of_positive_q hq p aPos hpWindow happroxPos
  · have hIntApprox :
        ∀ j : IntIdx ν,
          |(qInt : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) -
              (m (Fin.natAdd (2 ^ k) j) : ℝ)| <
            1 / (4 * (2 : ℝ) ^ k) := by
        intro j
        simpa using hIntCoords j
    have hIntWindow :=
      bm_integer_cover_of_coordinate_data hqInt hν3
        (fun j => m (Fin.natAdd (2 ^ k) j)) hIntApprox
    intro n hn
    obtain ⟨z, hz⟩ := hIntWindow n hn
    exact ⟨z, by simpa [q] using hz⟩

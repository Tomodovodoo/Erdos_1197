import Mathlib
import PNTBridge
import RequestProject_BMCore

/-!
# A Negative Answer to the Eventual Covering Question

We formalize the following result: there exists a measurable set `E ⊂ (0,∞)` of positive
Lebesgue measure such that for every `x ∈ [16/25, 2/3]`, there are infinitely many
positive integers `n` for which `x ∉ (r/n)·E` for every positive integer `r`.

The construction uses:
- `F := ⋃ k, H k` where `H k` are pairwise disjoint open "shells"
- `E := I_F \ Φ(F)` where `I_F = (8/9, 1)` and `Φ` captures integer-multiple shadows

The proof relies on the Buczolich–Mauldin shell construction, which is stated here
without proof (`disjoint_shells`). Everything else is proved from this single input.

## References

* Z. Buczolich, R. D. Mauldin, *On the convergence of ∑ f(nx) for measurable functions*
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 800000

/-! ## Definitions -/

/-- `Φ(A) = {x ∈ [1/2, 1) : ∃ m ≥ 1, m·x ∈ A}`.
    This is the "shadow" of `A` under positive integer multiples, restricted to `[1/2, 1)`. -/
def Phi (A : Set ℝ) : Set ℝ :=
  Ico (1/2 : ℝ) 1 ∩ {x | ∃ m : ℕ, 0 < m ∧ ((m : ℝ) * x) ∈ A}

/-- `I_F = (8/9, 1)`, the fundamental interval from which `E` is carved. -/
def I_F : Set ℝ := Ioo (8/9 : ℝ) 1

/-- `MultSat(E) = ⋃_{r≥1} r·E`, the multiplicative saturation of `E`. -/
def MultSat (E : Set ℝ) : Set ℝ :=
  {y | ∃ r : ℕ, 0 < r ∧ ∃ e ∈ E, y = (r : ℝ) * e}

/-! ## Buczolich–Mauldin shell construction

The proof of `disjoint_shells` follows the architecture of [BuMa99]:
1. The **BM Lemma** (`bm_lemma`) constructs, for each large `k` and `ν`,
   an open shell `H ⊆ (2^{ν-1}, 2^ν)` covering `I_∞` with small shadow measure.
2. The **assembly** step selects shells in distinct dyadic intervals (ensuring
   pairwise disjointness) and bounds the total shadow measure by a geometric series. -/

/-- `Phi ∅ = ∅`: the shadow of the empty set is empty. -/
@[simp]
lemma Phi_empty : Phi ∅ = ∅ := by
  ext x; simp [Phi]

/-! ### BM shell definition and properties -/

/-- The BM shell: points in `((8/9)·2^ν, 2^ν)` whose `log₂` is within
    `1/(q·2^k)` of a lattice point `n/q`. -/
def bm_shell (k ν q : ℕ) : Set ℝ :=
  {y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) |
    ∃ n : ℤ, |Real.logb 2 y - (n : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * 2 ^ k)}

/-
The BM shell is open (for `q > 0`).
-/
lemma bm_shell_isOpen (k ν q : ℕ) (_hq : 0 < q) : IsOpen (bm_shell k ν q) := by
  refine' isOpen_iff_mem_nhds.mpr fun x hx => _;
  obtain ⟨ n, hn ⟩ := hx.2;
  -- Since $| \log_2 x - n / q | < 1 / (q * 2^k)$, there exists an open interval around $x$ where $| \log_2 y - n / q | < 1 / (q * 2^k)$.
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ y, abs (y - x) < ε → abs (Real.logb 2 y - n / q) < 1 / (q * 2 ^ k) := by
    exact Metric.mem_nhds_iff.mp ( ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun y => |Real.logb 2 y - ↑n / ↑q| ) x from ContinuousAt.abs ( ContinuousAt.sub ( ContinuousAt.div_const ( Real.continuousAt_log ( by linarith [ hx.1.1, show ( 0 : ℝ ) < 2 ^ ν by positivity ] ) ) _ ) continuousAt_const ) ) ( Iio_mem_nhds hn ) );
  filter_upwards [ Ioo_mem_nhds hx.1.1 hx.1.2, Metric.ball_mem_nhds x hε.1 ] with y hy₁ hy₂ using ⟨ hy₁, n, hε.2 y hy₂ ⟩

/-
The BM shell is contained in the dyadic interval `(2^{ν-1}, 2^ν)`.
-/
lemma bm_shell_subset_dyadic (k ν q : ℕ) :
    bm_shell k ν q ⊆ Ioo ((2 : ℝ) ^ ν / 2) ((2 : ℝ) ^ ν) := by
  exact Set.Subset.trans ( Set.inter_subset_left ) ( Set.Ioo_subset_Ioo ( by linarith [ pow_pos ( zero_lt_two' ℝ ) ν ] ) le_rfl )

/-
If the Kronecker covering data holds, then `I_∞ ⊆ Φ(bm_shell)`.
-/
lemma bm_shell_covers (k ν q : ℕ)
    (h_cover : ∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
      (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
      ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * 2 ^ k)) :
    I_inf ⊆ Phi (bm_shell k ν q) := by
  intro x hx;
  -- By definition of Phi, we need to show that x is in Ico (1/2, 1) and there exists an m such that m*x is in bm_shell.
  apply And.intro;
  · constructor <;> linarith [ Set.mem_Icc.mp hx ];
  · exact Exists.elim ( h_cover x hx ) fun m hm => ⟨ m, hm.1, hm.2.1, hm.2.2 ⟩

/-
**Shadow containment**: if `y ∈ I_F ∩ Φ(bm_shell)`, then `log₂ y` is within
    `2/(q·2^k)` of some lattice point `m/q`.
-/
lemma bm_shadow_containment (k ν q : ℕ) (_hq : 0 < q)
    (h_lattice : ∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
      ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
        1 / (4 * (q : ℝ) * 2 ^ k)) :
    I_F ∩ Phi (bm_shell k ν q) ⊆
    {y ∈ I_F | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| <
      2 / ((q : ℝ) * 2 ^ k)} := by
  intro y hy;
  -- Since $y \in I_F \cap \Phi(bm_shell)$, there exists $n \in \mathbb{N}$ such that $n \cdot y \in bm_shell$.
  obtain ⟨n, hn_pos, hn_shell⟩ : ∃ n : ℕ, 0 < n ∧ n * y ∈ bm_shell k ν q := by
    cases hy.2 ; aesop;
  obtain ⟨ m₁, hm₁ ⟩ := h_lattice n (by
  constructor <;> nlinarith [ hn_shell.1.1, hn_shell.1.2, hy.1.1, hy.1.2 ])
  obtain ⟨ m₂, hm₂ ⟩ := hn_shell.2;
  rw [ Real.logb_mul ] at hm₂ <;> norm_num at *;
  · exact ⟨ hy.1, m₂ - m₁, by rw [ abs_lt ] at *; constructor <;> push_cast <;> ring_nf at * <;> linarith ⟩;
  · linarith;
  · linarith [ hy.1.1, hy.1.2 ]

/-! ### Auxiliary lemmas for the thin-set measure bound -/

/-
`logb 2 (9/8) < 1/5`, equivalently `(9/8)^5 < 2`.
-/
lemma logb_nine_eighth_lt : Real.logb 2 (9 / 8 : ℝ) < 1 / 5 := by
  rw [ Real.logb_lt_iff_lt_rpow ] <;> norm_num;
  rw [ Real.lt_rpow_iff_log_lt ] <;> norm_num;
  rw [ div_mul_eq_mul_div, lt_div_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_lt_log ]

/-
For `c ≤ 0` and `0 ≤ δ ≤ 1`, `2^(c+δ) - 2^(c-δ) ≤ 2δ`.
    Follows from convexity: `2^δ ≤ 1+δ` (secant on `[0,1]`), `2^(-δ) ≥ 1-δ` (tangent).
-/
lemma rpow_interval_width (c δ : ℝ) (hc : c ≤ 0) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (2 : ℝ) ^ (c + δ) - (2 : ℝ) ^ (c - δ) ≤ 2 * δ := by
  rw [ Real.rpow_sub, Real.rpow_add ] <;> norm_num;
  rw [ add_div', le_div_iff₀ ] <;> try positivity;
  -- Since $c \leq 0$, we have $2^c \leq 1$. Also, by convexity, $2^\delta \leq 1 + \delta(2 - 1) = 1 + \delta$.
  have h_exp : (2 : ℝ) ^ c ≤ 1 ∧ (2 : ℝ) ^ δ ≤ 1 + δ := by
    refine' ⟨ by rw [ Real.rpow_le_one_iff_of_pos ] <;> norm_num ; linarith, _ ⟩;
    have := @Real.geom_mean_le_arith_mean;
    specialize this { 0, 1 } ( fun i => if i = 0 then 1 - δ else δ ) ( fun i => if i = 0 then 1 else 2 ) ; norm_num at *;
    linarith [ this hδ1 hδ0 ];
  nlinarith [ Real.rpow_pos_of_pos zero_lt_two c, Real.rpow_pos_of_pos zero_lt_two δ, mul_le_mul_of_nonneg_left h_exp.1 ( Real.rpow_nonneg zero_le_two δ ), mul_le_mul_of_nonneg_left h_exp.2 ( Real.rpow_nonneg zero_le_two c ), Real.rpow_le_rpow_of_exponent_le ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hc, Real.rpow_le_rpow_of_exponent_le ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hδ0 ]

/-
**Thin set measure bound**: the set of `y ∈ I_F` whose `log₂` is within
    `2/(q·2^k)` of a lattice point `m/q` has measure less than `5 · 2⁻ᵏ`.
-/
lemma thin_set_measure_bound (q : ℕ) (hq : 0 < q) (k : ℕ) (hk : 7 ≤ k) :
    volume {y ∈ Ioo (8/9 : ℝ) 1 |
      ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| <
        2 / ((q : ℝ) * 2 ^ k)} <
    ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
  -- The set S is contained in the union of intervals Ioo (2^(m/q - δ)) (2^(m/q + δ)) for m in a finite range.
  have h_union : {y ∈ Ioo (8 / 9 : ℝ) 1 | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| < 2 / ((q : ℝ) * 2 ^ k)} ⊆ ⋃ m ∈ Finset.Icc (⌈(q : ℝ) * (Real.logb 2 (8 / 9) - 2 / ((q : ℝ) * 2 ^ k))⌉ : ℤ) 0, Ioo (2 ^ ((m : ℝ) / (q : ℝ) - 2 / ((q : ℝ) * 2 ^ k))) (2 ^ ((m : ℝ) / (q : ℝ) + 2 / ((q : ℝ) * 2 ^ k))) := by
    intro y hy
    obtain ⟨hy_range, m, hm⟩ := hy
    have hm_range : ⌈(q : ℝ) * (Real.logb 2 (8 / 9) - 2 / ((q : ℝ) * 2 ^ k))⌉ ≤ m ∧ m ≤ 0 := by
      constructor;
      · have hm_range : Real.logb 2 y > Real.logb 2 (8 / 9) := by
          exact Real.logb_lt_logb ( by norm_num ) ( by norm_num ) hy_range.1;
        exact Int.ceil_le.mpr ( by nlinarith [ abs_lt.mp hm, show ( q : ℝ ) > 0 by positivity, mul_div_cancel₀ ( m : ℝ ) ( by positivity : ( q : ℝ ) ≠ 0 ) ] );
      · have hm_neg : Real.logb 2 y < 0 := by
          rw [ Real.logb_neg_iff ] <;> linarith [ hy_range.1, hy_range.2 ];
        contrapose! hm_neg;
        rw [ abs_lt ] at hm;
        ring_nf at *;
        nlinarith [ show ( m : ℝ ) ≥ 1 by exact_mod_cast hm_neg, inv_pos.mpr ( by positivity : 0 < ( q : ℝ ) ), pow_le_pow_of_le_one ( by positivity : ( 0 : ℝ ) ≤ 2⁻¹ ) ( by norm_num ) ( show k ≥ 1 by linarith ), mul_inv_cancel₀ ( by positivity : ( q : ℝ ) ≠ 0 ) ];
    simp +zetaDelta at *;
    refine' ⟨ m, _, hm_range, _ ⟩;
    · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by linarith ), Real.log_rpow ] <;> norm_num;
      rw [ Real.logb ] at hm ; nlinarith [ abs_lt.mp hm, Real.log_pos one_lt_two, mul_div_cancel₀ ( Real.log y ) ( show ( Real.log 2 ) ≠ 0 by positivity ) ];
    · rw [ ← Real.log_lt_log_iff ( by linarith ) ( by positivity ), Real.log_rpow ] <;> norm_num;
      rw [ Real.logb ] at hm ; nlinarith [ abs_lt.mp hm, Real.log_pos one_lt_two, mul_div_cancel₀ ( Real.log y ) ( show ( Real.log 2 ) ≠ 0 by positivity ) ];
  -- The measure of the union of intervals is at most the sum of their lengths.
  have h_measure : MeasureTheory.volume {y ∈ Ioo (8 / 9 : ℝ) 1 | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| < 2 / ((q : ℝ) * 2 ^ k)} ≤ (Finset.card (Finset.Icc (⌈(q : ℝ) * (Real.logb 2 (8 / 9) - 2 / ((q : ℝ) * 2 ^ k))⌉ : ℤ) 0)) * ENNReal.ofReal (4 / ((q : ℝ) * 2 ^ k)) := by
    refine' le_trans ( MeasureTheory.measure_mono h_union ) _;
    refine' le_trans ( MeasureTheory.measure_biUnion_finset_le _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun _ _ => _ ) _;
    use fun m => ENNReal.ofReal ( 4 / ( q * 2 ^ k ) );
    · rw [ Real.volume_Ioo ];
      refine' ENNReal.ofReal_le_ofReal _;
      convert rpow_interval_width _ _ _ _ _ using 1 <;> ring_nf <;> norm_num;
      · exact mul_nonpos_of_nonpos_of_nonneg ( Int.cast_nonpos.mpr ( Finset.mem_Icc.mp ‹_› |>.2 ) ) ( by positivity );
      · field_simp;
        exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) hk ) zero_le_two ) ( by norm_num; linarith [ show ( q : ℝ ) ≥ 1 by norm_cast ] );
    · norm_num;
  -- The number of nonzero terms is at most $q * \log_2(9/8) + 2 / 2^k + 1$.
  have h_card : Finset.card (Finset.Icc (⌈(q : ℝ) * (Real.logb 2 (8 / 9) - 2 / ((q : ℝ) * 2 ^ k))⌉ : ℤ) 0) ≤ (q : ℝ) * Real.logb 2 (9 / 8) + 2 / 2 ^ k + 1 := by
    rw [ show ( 9 / 8 : ℝ ) = ( 8 / 9 ) ⁻¹ by norm_num, Real.logb_inv ] ; norm_num;
    rw [ show ( 2 : ℝ ) / 2 ^ k = 2 / ( 2 ^ k : ℝ ) by ring, mul_sub, mul_div_assoc' ];
    norm_num [ mul_div_mul_left, hq.ne' ];
    rw [ show ( 1 - ⌈ ( q : ℝ ) * Real.logb 2 ( 8 / 9 ) - 2 / 2 ^ k⌉ : ℤ ) = -⌈ ( q : ℝ ) * Real.logb 2 ( 8 / 9 ) - 2 / 2 ^ k⌉ + 1 by ring ] ; norm_num;
    rcases n : -⌈ ( q : ℝ ) * Real.logb 2 ( 8 / 9 ) - 2 / 2 ^ k⌉ + 1 with ( _ | n ) <;> norm_num [ n ];
    · norm_num [ ← @Int.cast_inj ℝ ] at * ; linarith [ Int.le_ceil ( ( q : ℝ ) * Real.logb 2 ( 8 / 9 ) - 2 / 2 ^ k ) ];
    · nlinarith [ show ( q : ℝ ) ≥ 1 by norm_cast, show ( 2 : ℝ ) ^ k ≥ 1 by exact one_le_pow₀ ( by norm_num ), show ( Real.logb 2 ( 8 / 9 ) ) ≤ 0 by rw [ Real.logb_nonpos_iff ] <;> norm_num, div_nonneg zero_le_two ( show ( 0 : ℝ ) ≤ 2 ^ k by positivity ) ];
  -- Substitute the bound on the number of nonzero terms into the measure inequality.
  have h_final : MeasureTheory.volume {y ∈ Ioo (8 / 9 : ℝ) 1 | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| < 2 / ((q : ℝ) * 2 ^ k)} ≤ ENNReal.ofReal ((q * Real.logb 2 (9 / 8) + 2 / 2 ^ k + 1) * (4 / ((q : ℝ) * 2 ^ k))) := by
    refine le_trans h_measure ?_;
    rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num;
    · gcongr;
      · exact add_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.logb_nonneg ( by norm_num ) ( by norm_num ) ) ) ( by positivity ) ) zero_le_one;
      · convert h_card using 1;
        norm_num [ Int.toNat_of_nonneg, Int.ceil_nonneg ];
      · rw [ ENNReal.toReal_ofReal ( by positivity ) ];
    · exact ENNReal.mul_ne_top ( by norm_num ) ( ENNReal.ofReal_ne_top );
    · exact mul_nonneg ( add_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.logb_nonneg ( by norm_num ) ( by norm_num ) ) ) ( by positivity ) ) zero_le_one ) ( by positivity );
  refine lt_of_le_of_lt h_final ?_;
  rw [ ENNReal.ofReal_lt_ofReal_iff ] <;> ring_nf <;> norm_num [ hq.ne', hk ];
  norm_num [ pow_mul, mul_assoc, mul_comm, mul_left_comm, hq.ne' ];
  have := logb_nine_eighth_lt;
  nlinarith [ show ( q : ℝ ) ≥ 1 by norm_cast, inv_pos.mpr ( by positivity : 0 < ( q : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( q : ℝ ) ≠ 0 ), pow_pos ( by positivity : 0 < ( 1 / 2 : ℝ ) ) k, pow_le_pow_of_le_one ( by positivity : 0 ≤ ( 1 / 2 : ℝ ) ) ( by norm_num ) hk, mul_le_mul_of_nonneg_left this.le ( by positivity : 0 ≤ ( 1 / 2 : ℝ ) ^ k ) ]

/-- Shadow measure bound: if the lattice data holds and `q ≥ 1`, then
    `μ(I_F ∩ Φ(bm_shell)) < 5 · 2⁻ᵏ`. -/
lemma bm_shell_shadow_small (k ν q : ℕ) (hq : 0 < q) (hk : 7 ≤ k)
    (h_lattice : ∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
      ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
        1 / (4 * (q : ℝ) * 2 ^ k)) :
    volume (I_F ∩ Phi (bm_shell k ν q)) < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
  calc volume (I_F ∩ Phi (bm_shell k ν q))
      _ ≤ volume {y ∈ I_F | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| <
            2 / ((q : ℝ) * 2 ^ k)} := measure_mono (bm_shadow_containment k ν q hq h_lattice)
      _ = volume {y ∈ Ioo (8/9 : ℝ) 1 | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| <
            2 / ((q : ℝ) * 2 ^ k)} := by rfl
      _ < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := thin_set_measure_bound q hq k hk

/-- **The Buczolich–Mauldin Lemma** ([BuMa99, Lemma]).

For each sufficiently large `k` and dyadic scale `ν`, there is an open set
`H ⊆ (2^{ν−1}, 2^ν)` satisfying `I_∞ ⊆ Φ(H)` and `μ(I_F ∩ Φ(H)) < 5 · 2⁻ᵏ`.

The proof constructs `H = bm_shell k ν q` where `q` is obtained from Kronecker's
theorem applied to primes and integers in the appropriate ranges. -/
lemma bm_lemma :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ H : Set ℝ,
          IsOpen H ∧
          H ⊆ Ioo ((2 : ℝ) ^ ν / 2) ((2 : ℝ) ^ ν) ∧
          I_inf ⊆ Phi H ∧
          volume (I_F ∩ Phi H) < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
  obtain ⟨K₀, hKr⟩ := bm_approx_data
  refine ⟨max K₀ 7, fun k hk => ?_⟩
  obtain ⟨N_k, hN⟩ := hKr k ((le_max_left K₀ 7).trans hk)
  refine ⟨N_k, fun ν hν => ?_⟩
  obtain ⟨q, hq, h_cover, h_lattice⟩ := hN ν hν
  exact ⟨bm_shell k ν q,
    bm_shell_isOpen k ν q hq,
    bm_shell_subset_dyadic k ν q,
    bm_shell_covers k ν q h_cover,
    bm_shell_shadow_small k ν q hq ((le_max_right K₀ 7).trans hk) h_lattice⟩

/-
Any function `N : ℕ → ℕ` is eventually dominated by a strictly increasing sequence.
-/
lemma exists_strictMono_above (K : ℕ) (N : ℕ → ℕ) :
    ∃ ν : ℕ → ℕ, (∀ i j, K ≤ i → i < j → ν i < ν j) ∧
      ∀ k, K ≤ k → N k ≤ ν k := by
  use fun k => Nat.recOn ( k - K ) ( N K ) fun k ihk => ihk + N ( k + K + 1 ) + 1;
  refine' ⟨ _, _ ⟩;
  · intro i j hi hj; induction hj <;> simp_all +arith +decide;
    · rw [ Nat.succ_sub ( by linarith ) ];
      grind;
    · exact lt_of_lt_of_le ‹_› ( by rw [ Nat.sub_add_comm ( by linarith ) ] ; simp +arith +decide );
  · intro k hk;
    induction hk <;> simp +arith +decide [ * ];
    simp_all +arith +decide [ Nat.succ_sub ( show K ≤ _ from by assumption ), add_comm K ]

/-
Dyadic intervals `(2^n / 2, 2^n)` are disjoint for distinct `n`.
-/
lemma Ioo_dyadic_disjoint {n m : ℕ} (h : n ≠ m) :
    Disjoint (Ioo ((2 : ℝ) ^ n / 2) ((2 : ℝ) ^ n))
      (Ioo ((2 : ℝ) ^ m / 2) ((2 : ℝ) ^ m)) := by
  cases lt_or_gt_of_ne h;
  · refine' Set.disjoint_left.mpr fun x hx₁ hx₂ => _;
    -- Since $n < m$, we have $2^n \leq 2^{m-1}$.
    have h_pow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (m - 1) := by
      exact pow_le_pow_right₀ ( by norm_num ) ( Nat.le_pred_of_lt ‹_› );
    cases m <;> norm_num [ pow_succ' ] at * ; linarith;
  · rw [ Set.disjoint_left ];
    intro x hx₁ hx₂; have := pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( Nat.succ_le_of_lt ‹m < n› ) ; norm_num [ pow_succ' ] at * ; linarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2 ] ;

/-
Geometric tail bound: `∑_{k ≥ K} 5 · (1/2)^k < μ(I_F) = 1/9` when `K ≥ 7`.
-/
lemma tsum_geometric_lt_I_F {K : ℕ} (hK : 7 ≤ K)
    {a : ℕ → ℝ≥0∞}
    (ha : ∀ k, K ≤ k → a k ≤ ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k))
    (ha0 : ∀ k, k < K → a k = 0) :
    ∑' k, a k < volume I_F := by
  -- Applying the bound on each term to the sum, we get ∑' k, a k ≤ ∑' k, ENNReal.ofReal (5 * (1/2)^k) for k ≥ K.
  have h_sum_le : ∑' k, a k ≤ ∑' k, if k ≥ K then (ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k)) else 0 := by
    apply ENNReal.tsum_le_tsum;
    aesop;
  -- The sum of the geometric series $\sum_{k=K}^{\infty} 5 \cdot (1/2)^k$ is $5 \cdot (1/2)^K / (1 - 1/2) = 10 \cdot (1/2)^K$.
  have h_geo_sum : ∑' k, (if k ≥ K then (ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k)) else 0) = ENNReal.ofReal (10 * (1 / 2 : ℝ) ^ K) := by
    have h_geo_sum : ∑' k, (if k ≥ K then (5 * (1 / 2 : ℝ) ^ k) else 0) = 10 * (1 / 2 : ℝ) ^ K := by
      have h_geo_sum : ∑' k, (if k ≥ K then (5 * (1 / 2 : ℝ) ^ k) else 0) = ∑' k, (5 * (1 / 2 : ℝ) ^ (k + K)) := by
        rw [ ← Summable.sum_add_tsum_nat_add K ];
        · rw [ Finset.sum_eq_zero ] <;> aesop;
        · exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by split_ifs <;> norm_num ) ( summable_geometric_two.mul_left 5 );
      convert h_geo_sum using 1 ; ring_nf;
      rw [ tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one ] <;> ring_nf <;> norm_num;
    rw [ ← h_geo_sum, ENNReal.ofReal_tsum_of_nonneg ];
    · exact tsum_congr fun n => by split_ifs <;> norm_num;
    · intro n; split_ifs <;> positivity;
    · exact ( by contrapose! h_geo_sum; erw [ tsum_eq_zero_of_not_summable h_geo_sum ] ; positivity );
  refine lt_of_le_of_lt h_sum_le <| h_geo_sum ▸ ?_;
  rw [ show I_F = Set.Ioo ( 8 / 9 ) 1 by rfl, Real.volume_Ioo ] ; norm_num;
  rw [ ← ENNReal.toReal_lt_toReal ] <;> norm_num;
  · exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) hK ) ( by norm_num ) ) ( by norm_num );
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ( ENNReal.pow_ne_top <| ENNReal.ofReal_ne_top )

/-- **Disjoint shells** — the key construction for the counterexample.

There exist pairwise disjoint open sets `H k` (for `k ≥ K`) such that:
- every `x ∈ I_∞` belongs to `Φ(H k)` for each `k ≥ K`,
- the total measure `∑_k μ(I_F ∩ Φ(H k))` is strictly less than `μ(I_F)`.

**Proof.** Apply the BM Lemma to obtain shells `H₀ k ⊆ (2^{ν(k)−1}, 2^{ν(k)})`
in distinct dyadic intervals (via a strictly increasing choice of `ν`). Pairwise
disjointness follows from the shells lying in non-overlapping dyadic intervals;
the measure bound follows from a geometric series comparison. -/
lemma disjoint_shells :
    ∃ (K : ℕ) (H : ℕ → Set ℝ),
      (∀ k, k < K → H k = ∅) ∧
      (∀ k, K ≤ k → IsOpen (H k)) ∧
      (Pairwise fun i j => Disjoint (H i) (H j)) ∧
      (∀ k, K ≤ k → I_inf ⊆ Phi (H k)) ∧
      ∑' k, volume (I_F ∩ Phi (H k)) < volume I_F := by
  -- Step 1: Apply the BM Lemma
  obtain ⟨K₀, hBM⟩ := bm_lemma
  -- Step 2: Set K large enough for both the BM construction and the geometric sum bound
  set K := max K₀ 7
  -- Step 3: Uniformly choose thresholds N_k for all k
  have hN_ex : ∀ k, ∃ Nk : ℕ, K ≤ k → ∀ ν, Nk ≤ ν →
      ∃ H : Set ℝ, IsOpen H ∧ H ⊆ Ioo ((2 : ℝ) ^ ν / 2) ((2 : ℝ) ^ ν) ∧
        I_inf ⊆ Phi H ∧
        volume (I_F ∩ Phi H) < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
    intro k
    by_cases hk : K ≤ k
    · exact let ⟨Nk, hNk⟩ := hBM k ((le_max_left K₀ 7).trans hk); ⟨Nk, fun _ => hNk⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose N hN using hN_ex
  -- Step 4: Choose ν strictly increasing above N
  obtain ⟨ν, hν_strict, hν_ge⟩ := exists_strictMono_above K N
  -- Step 5: Construct individual shells
  have hH_ex : ∀ k, ∃ Hk : Set ℝ, K ≤ k →
      IsOpen Hk ∧ Hk ⊆ Ioo ((2 : ℝ) ^ ν k / 2) ((2 : ℝ) ^ ν k) ∧
        I_inf ⊆ Phi Hk ∧
        volume (I_F ∩ Phi Hk) < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
    intro k
    by_cases hk : K ≤ k
    · exact let ⟨Hk, hHk⟩ := hN k hk (ν k) (hν_ge k hk); ⟨Hk, fun _ => hHk⟩
    · exact ⟨∅, fun h => absurd h hk⟩
  choose H₀ hH₀ using hH_ex
  -- Step 6: Assemble: H k = ∅ for k < K, H₀ k for k ≥ K
  let H : ℕ → Set ℝ := fun k => if K ≤ k then H₀ k else ∅
  have hH_pos : ∀ k, K ≤ k → H k = H₀ k := fun k hk => if_pos hk
  have hH_neg : ∀ k, ¬ K ≤ k → H k = ∅ := fun k hk => if_neg hk
  refine ⟨K, H, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) Empty below K
    intro k hk; exact hH_neg k (not_le.mpr hk)
  · -- (2) Open above K
    intro k hk; rw [hH_pos k hk]; exact (hH₀ k hk).1
  · -- (3) Pairwise disjoint
    intro i j hij
    by_cases hi : K ≤ i <;> by_cases hj : K ≤ j
    · rw [hH_pos i hi, hH_pos j hj]
      exact (Ioo_dyadic_disjoint (by
        intro heq; rcases lt_or_gt_of_ne hij with h | h
        · exact absurd heq (ne_of_lt (hν_strict i j hi h))
        · exact absurd heq.symm (ne_of_lt (hν_strict j i hj h))
      )).mono (hH₀ i hi).2.1 (hH₀ j hj).2.1
    · rw [hH_neg j hj]; exact disjoint_bot_right
    · rw [hH_neg i hi]; exact disjoint_bot_left
    · rw [hH_neg i hi]; exact disjoint_bot_left
  · -- (4) Covering
    intro k hk; rw [hH_pos k hk]; exact (hH₀ k hk).2.2.1
  · -- (5) Tsum bound
    have ha : ∀ k, K ≤ k → volume (I_F ∩ Phi (H k)) ≤
        ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
      intro k hk; rw [hH_pos k hk]; exact le_of_lt (hH₀ k hk).2.2.2
    have ha0 : ∀ k, k < K → volume (I_F ∩ Phi (H k)) = 0 := by
      intro k hk; rw [hH_neg k (not_le.mpr hk), Phi_empty, Set.inter_empty, measure_empty]
    exact tsum_geometric_lt_I_F (le_max_right K₀ 7) ha ha0

/-! ## Helper lemmas about `Phi` -/

/-
`Φ` distributes over countable unions (subset direction):
    `Φ(⋃ k, H k) ⊆ ⋃ k, Φ(H k)`.
-/
lemma Phi_subset_iUnion (H : ℕ → Set ℝ) :
    Phi (⋃ k, H k) ⊆ ⋃ k, Phi (H k) := by
  intro x hx;
  simp_all +decide [ Phi ];
  tauto

/-
`Φ(A)` is measurable when `A` is measurable.
    Indeed, `Φ(A) = [1/2,1) ∩ ⋃_{m≥1} (· * m)⁻¹'(A)`.
-/
lemma Phi_measurableSet {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (Phi A) := by
  refine' MeasurableSet.inter _ _;
  · exact measurableSet_Ico;
  · -- The set {x | ∃ m, 0 < m ∧ (m : ℝ) * x ∈ A} can be written as the union over all m ≥ 1 of the preimage of A under the function x ↦ mx.
    have h_union : {x : ℝ | ∃ m : ℕ, 0 < m ∧ (m : ℝ) * x ∈ A} = ⋃ m : ℕ, ⋃ hm : 0 < m, (fun x => (m : ℝ) * x) ⁻¹' A := by
      aesop;
    exact h_union ▸ MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun hm => measurable_const.mul measurable_id hA

/-! ## Interval arithmetic lemmas -/

/-
`I_F = (8/9, 1) ⊆ [1/2, 1)`.
-/
lemma I_F_subset_Ico : I_F ⊆ Ico (1/2 : ℝ) 1 := by
  exact Set.Ioo_subset_Ico_self.trans ( Set.Ico_subset_Ico ( by norm_num ) ( by norm_num ) )

/-
`I_F = (8/9, 1)` has positive measure.
-/
lemma I_F_volume_pos : 0 < volume I_F := by
  erw [ Real.volume_Ioo ] ; norm_num

/-
`I_F = (8/9, 1)` has finite measure.
-/
lemma I_F_volume_ne_top : volume I_F ≠ ⊤ := by
  erw [ Real.volume_Ioo ] ; norm_num

/-! ## Core lemmas of the counterexample construction -/

/-
`F` and `MultSat(I_F \ Φ(F))` are disjoint.
    If `y ∈ F ∩ MultSat(I_F \ Φ(F))`, then `y = r·e` with `e ∈ I_F \ Φ(F)`.
    Since `e ∈ I_F ⊆ [1/2,1)` and `r·e = y ∈ F`, we get `e ∈ Φ(F)`, contradicting `e ∉ Φ(F)`.
-/
lemma F_disjoint_MultSat (F : Set ℝ) :
    Disjoint F (MultSat (I_F \ Phi F)) := by
  unfold MultSat;
  simp +decide [ Phi, Set.disjoint_left ];
  intro y hy n hn x hx h; exact fun hxy => h ( by linarith [ Set.mem_Ioo.mp hx ] ) ( by linarith [ Set.mem_Ioo.mp hx ] ) n hn <| hxy ▸ hy;

/-
If `x ∈ Φ(H k)` for all `k ≥ K` and the `H k` are pairwise disjoint,
    then `{n : n·x ∈ ⋃ H k}` is infinite.
    The witnesses `m_k` from `Φ(H k)` are distinct because `H k` are disjoint.
-/
lemma inf_many_hits (x : ℝ) (K : ℕ) (H : ℕ → Set ℝ)
    (h_cover : ∀ k, K ≤ k → x ∈ Phi (H k))
    (h_disj : Pairwise fun i j => Disjoint (H i) (H j)) :
    {n : ℕ | 0 < n ∧ ((n : ℝ) * x) ∈ ⋃ k, H k}.Infinite := by
  -- By assumption, $x \in \Phi(H_k)$ for all $k \ge K$, so there exists $m_k \ge 1$ such that $m_k * x \in H_k$.
  have h_exists_mk : ∀ k, K ≤ k → ∃ m_k : ℕ, 0 < m_k ∧ m_k * x ∈ H k := by
    exact fun k hk => by rcases h_cover k hk |>.2 with ⟨ m, hm₁, hm₂ ⟩ ; exact ⟨ m, hm₁, hm₂ ⟩ ;
  choose! m hm₁ hm₂ using h_exists_mk;
  -- The function $k \mapsto m_k$ is injective on $\{k | K \le k\}$.
  have h_inj : Set.InjOn m (Set.Ici K) := by
    intro k hk l hl hkl; have := hm₂ k hk; have := hm₂ l hl; simp_all +decide [ Set.disjoint_left ] ;
    exact Classical.not_not.1 fun h => h_disj h this ( hm₂ l hl );
  exact Set.infinite_of_injective_forall_mem ( fun i j hij => by have := h_inj ( by norm_num : K ≤ K + i ) ( by norm_num : K ≤ K + j ) hij; aesop ) fun n => ⟨ hm₁ _ ( by linarith ), Set.mem_iUnion.mpr ⟨ _, hm₂ _ ( by linarith ) ⟩ ⟩

/-
`E = I_F \ Φ(⋃ H k)` has positive measure when the shadows `Φ(H k)` are small.
    Uses `Φ(⋃ H k) ⊆ ⋃ Φ(H k)`, measure subadditivity, and the hypothesis
    `∑ μ(I_F ∩ Φ(H k)) < μ(I_F)`.
-/
lemma E_pos_measure (H : ℕ → Set ℝ)
    (hH_meas : ∀ k, MeasurableSet (H k))
    (h_sum : ∑' k, volume (I_F ∩ Phi (H k)) < volume I_F) :
    0 < volume (I_F \ Phi (⋃ k, H k)) := by
  have h_diff : volume (I_F \ Phi (⋃ k, H k)) = volume I_F - volume (I_F ∩ Phi (⋃ k, H k)) := by
    rw [ ← MeasureTheory.measure_diff ];
    · aesop;
    · exact Set.inter_subset_left;
    · refine' MeasurableSet.nullMeasurableSet _;
      refine' MeasurableSet.inter ( measurableSet_Ioo ) _;
      apply_rules [ Phi_measurableSet, MeasurableSet.iUnion ];
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( by erw [ Real.volume_Ioo ] ; norm_num ) );
  have h_subadd : volume (I_F ∩ Phi (⋃ k, H k)) ≤ ∑' k, volume (I_F ∩ Phi (H k)) := by
    refine' le_trans ( MeasureTheory.measure_mono _ ) _;
    exact ⋃ k, I_F ∩ Phi ( H k );
    · exact fun x hx => by rcases hx.2.2 with ⟨ m, hm, hm' ⟩ ; rcases Set.mem_iUnion.1 hm' with ⟨ k, hk ⟩ ; exact Set.mem_iUnion.2 ⟨ k, ⟨ hx.1, ⟨ hx.2.1, m, hm, hk ⟩ ⟩ ⟩ ;
    · exact MeasureTheory.measure_iUnion_le _;
  exact h_diff.symm ▸ tsub_pos_of_lt ( lt_of_le_of_lt h_subadd h_sum )

/-! ## Main theorem -/

/-
**Negative answer to the eventual covering question.**

There exists a measurable set `E ⊂ (0,∞)` of positive Lebesgue measure such that
for every `x ∈ [16/25, 2/3]`, there are infinitely many positive integers `n` for which
`x ∉ (r/n)·E` for every positive integer `r`.

In particular, it is _not_ true that for every positive-measure `E ⊂ (0,∞)`,
for a.e. `x > 0`, for all sufficiently large `n`, there exists `r ≥ 1` with `x ∈ (r/n)·E`.
-/
theorem negative_answer :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioi 0 ∧ 0 < volume E ∧
      ∀ x ∈ I_inf,
        {n : ℕ | 0 < n ∧ ∀ r : ℕ, 0 < r →
          ¬∃ e ∈ E, x = ((r : ℝ) / (n : ℝ)) * e}.Infinite := by
  -- Set F := ⋃ k, H k, E := I_F \ Phi F.
  obtain ⟨K, H, hH_empty, hH_open, hH_disj, hH_cover, hH_sum⟩ := disjoint_shells;
  set F := ⋃ k, H k;
  set E := I_F \ Phi F;
  refine' ⟨ E, _, _, _, _ ⟩;
  · apply_rules [ MeasurableSet.diff, measurableSet_Ioo, Phi_measurableSet ];
    exact MeasurableSet.iUnion fun k => if hk : k < K then by aesop else hH_open k ( le_of_not_gt hk ) |> IsOpen.measurableSet;
  · exact fun x hx => hx.1.1.trans_le' <| by norm_num;
  · convert E_pos_measure H _ hH_sum;
    exact fun k => if hk : k < K then by aesop else hH_open k ( le_of_not_gt hk ) |> IsOpen.measurableSet;
  · intro x hx
    have h_inf : {n : ℕ | 0 < n ∧ (n : ℝ) * x ∈ F}.Infinite := by
      exact inf_many_hits x K H ( fun k hk => hH_cover k hk hx ) hH_disj;
    refine' h_inf.mono _;
    intro n hn
    obtain ⟨hn_pos, hn_F⟩ := hn
    use hn_pos
    intro r hr ⟨e, he_E, he_eq⟩
    have h_contra : (n : ℝ) * x ∈ MultSat E := by
      use r;
      exact ⟨ hr, e, he_E, by rw [ he_eq, div_mul_eq_mul_div, mul_div_cancel₀ _ ( by positivity ) ] ⟩;
    exact absurd ( F_disjoint_MultSat F ) ( Set.not_disjoint_iff_nonempty_inter.mpr ⟨ _, hn_F, h_contra ⟩ )

end

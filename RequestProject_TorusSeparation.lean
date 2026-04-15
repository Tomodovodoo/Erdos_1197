/-
# Hard Direction of Kronecker's Theorem

This file contains the proof of the hard direction of Kronecker's approximation
theorem in the BM-facing common-denominator form used by the Buczolich–Mauldin
construction, along with the torus-separation infrastructure that supports it.
-/
import Mathlib

open scoped BigOperators

noncomputable section

/-! ## Classification of closed subgroups of ℝ -/

/-- A closed nontrivial additive subgroup of ℝ is either all of ℝ or cyclic. -/
lemma closed_addsubgroup_of_real (S : AddSubgroup ℝ) (hS : IsClosed (S : Set ℝ))
    (hne : ∃ x ∈ S, x ≠ 0) :
    (S : Set ℝ) = Set.univ ∨
    ∃ a : ℝ, 0 < a ∧ (S : Set ℝ) = Set.range (fun n : ℤ => n * a) := by
  by_cases ha : sInf ({x : ℝ | 0 < x ∧ x ∈ S}) = 0
  · have h_dense : ∀ ε > 0, ∃ x ∈ S, 0 < x ∧ x < ε := by
      intro ε hε_pos
      have h_inf : ∃ x ∈ {x : ℝ | 0 < x ∧ x ∈ S}, x < ε := by
        contrapose! ha
        exact ne_of_gt <| lt_of_lt_of_le hε_pos <| le_csInf
          ⟨|hne.choose|, ⟨abs_pos.mpr hne.choose_spec.2,
            by simpa using S.zsmul_mem hne.choose_spec.1 1⟩⟩
          fun x hx => ha x hx
      aesop
    have h_dense : ∀ y : ℝ, ∀ ε > 0, ∃ x ∈ S, |x - y| < ε := by
      intro y ε hε_pos
      obtain ⟨x, hxS, hx_pos, hx_lt⟩ := h_dense ε hε_pos
      have h_seq : ∀ n : ℤ, n * x ∈ S := fun n => by simpa using S.zsmul_mem hxS n
      exact ⟨⌊y / x⌋ * x, h_seq _, by
        rw [abs_lt]; constructor <;>
          nlinarith [Int.floor_le (y / x), Int.lt_floor_add_one (y / x),
            mul_div_cancel₀ y hx_pos.ne']⟩
    exact Or.inl <| Set.eq_univ_of_forall fun y =>
      hS.closure_subset_iff.mpr (Set.Subset.refl _) <|
        mem_closure_iff_nhds_basis Metric.nhds_basis_ball |>.2 fun ε hε =>
          h_dense y ε hε
  · have ha_pos : 0 < sInf {x | 0 < x ∧ x ∈ S} := by
      exact lt_of_le_of_ne
        (by apply_rules [Real.sInf_nonneg]; rintro x ⟨hx₁, hx₂⟩; linarith) (Ne.symm ha)
    have ha_least : ∀ x ∈ S, 0 < x → sInf {x | 0 < x ∧ x ∈ S} ≤ x :=
      fun x hx hx' => csInf_le ⟨0, fun y hy => hy.1.le⟩ ⟨hx', hx⟩
    have ha_mem : sInf {x | 0 < x ∧ x ∈ S} ∈ S := by
      obtain ⟨xn, hxn⟩ : ∃ xn : ℕ → ℝ,
          (∀ n, 0 < xn n ∧ xn n ∈ S) ∧
          Filter.Tendsto xn Filter.atTop (nhds (sInf {x | 0 < x ∧ x ∈ S})) := by
        have h_seq : ∀ ε > 0, ∃ x ∈ S, 0 < x ∧ |x - sInf {x | 0 < x ∧ x ∈ S}| < ε := by
          exact fun ε ε_pos => by
            rcases exists_lt_of_csInf_lt
              (show {x : ℝ | 0 < x ∧ x ∈ S}.Nonempty from by contrapose! ha; aesop)
              (lt_add_of_pos_right _ ε_pos)
              with ⟨x, hx₁, hx₂⟩
            exact ⟨x, hx₁.2, hx₁.1, abs_lt.mpr
              ⟨by linarith [ha_least x hx₁.2 hx₁.1], by linarith [ha_least x hx₁.2 hx₁.1]⟩⟩
        exact ⟨fun n => Classical.choose (h_seq (1 / (n + 1)) (by positivity)),
          fun n => ⟨(Classical.choose_spec (h_seq (1 / (n + 1)) (by positivity))).2.1,
            (Classical.choose_spec (h_seq (1 / (n + 1)) (by positivity))).1⟩,
          tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero
            (fun _ => by positivity)
            (fun n => (Classical.choose_spec (h_seq (1 / (n + 1)) (by positivity))).2.2.le)
            tendsto_one_div_add_atTop_nhds_zero_nat⟩
      exact hS.mem_of_tendsto hxn.2 (Filter.Eventually.of_forall fun n => hxn.1 n |>.2)
    have hS_eq : S = AddSubgroup.zmultiples (sInf {x | 0 < x ∧ x ∈ S}) := by
      have hS_eq : ∀ x ∈ S, ∃ n : ℤ, x = n * sInf {x | 0 < x ∧ x ∈ S} := by
        intro x hx; by_contra h_contra
        obtain ⟨n, hn⟩ : ∃ n : ℤ, n * sInf {x | 0 < x ∧ x ∈ S} ≤ x ∧
            x < (n + 1) * sInf {x | 0 < x ∧ x ∈ S} :=
          ⟨⌊x / sInf {x | 0 < x ∧ x ∈ S}⌋, by
            nlinarith [Int.floor_le (x / sInf {x | 0 < x ∧ x ∈ S}),
              mul_div_cancel₀ x ha], by
            nlinarith [Int.lt_floor_add_one (x / sInf {x | 0 < x ∧ x ∈ S}),
              mul_div_cancel₀ x ha]⟩
        have h_c : x - n * sInf {x | 0 < x ∧ x ∈ S} ∈ S ∧
            0 < x - n * sInf {x | 0 < x ∧ x ∈ S} ∧
            x - n * sInf {x | 0 < x ∧ x ∈ S} < sInf {x | 0 < x ∧ x ∈ S} :=
          ⟨by simpa using S.sub_mem hx (S.zsmul_mem ha_mem n),
           lt_of_le_of_ne (by linarith)
             (Ne.symm <| by intro H; exact h_contra ⟨n, by linarith⟩), by linarith⟩
        linarith [ha_least _ h_c.1 h_c.2.1]
      refine le_antisymm ?_ ?_ <;> intro x hx <;>
        simp_all +decide [AddSubgroup.mem_zmultiples_iff]
      · simpa only [eq_comm] using hS_eq x hx
      · obtain ⟨k, rfl⟩ := hx; exact by simpa using S.zsmul_mem ha_mem k
    exact Or.inr ⟨sInf {x | 0 < x ∧ x ∈ S}, ha_pos, by
      have hS_eq' := hS_eq
      ext x; simp only [Set.mem_range, SetLike.mem_coe]
      constructor
      · intro hx; rw [hS_eq'] at hx
        obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
        exact ⟨k, by rw [← hk]; simp [zsmul_eq_mul]⟩
      · rintro ⟨n, rfl⟩; show _ ∈ S
        have : n • sInf {x | 0 < x ∧ x ∈ S} = (n : ℝ) * sInf {x | 0 < x ∧ x ∈ S} := by
          simp [zsmul_eq_mul]
        rw [← this]; exact S.zsmul_mem ha_mem n⟩

/-
A closed additive subgroup of ℝ containing 1 is either all of ℝ or (1/d)·ℤ.
-/
lemma closed_addsubgroup_contains_one (S : AddSubgroup ℝ) (hS : IsClosed (S : Set ℝ))
    (h1 : (1 : ℝ) ∈ S) :
    (S : Set ℝ) = Set.univ ∨
    ∃ d : ℕ, 0 < d ∧ (S : Set ℝ) = Set.range (fun n : ℤ => (n : ℝ) / (d : ℝ)) := by
  by_cases h : ∃ x ∈ S, x ≠ 0;
  · have := @closed_addsubgroup_of_real S hS h;
    obtain this | ⟨ a, ha, ha' ⟩ := this;
    · exact Or.inl this;
    · -- Since $1 \in S$, we have $1 = k \cdot a$ for some integer $k$.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, 1 = k * a := by
        exact ha'.subset h1 |> fun ⟨ k, hk ⟩ => ⟨ k, hk.symm ⟩;
      refine Or.inr ⟨ k.natAbs, ?_, ?_ ⟩ <;> norm_num [ ha', abs_of_pos ( show 0 < k from by exact_mod_cast ( by nlinarith : ( 0 :ℝ ) < k ) ) ];
      · rintro rfl; norm_num at hk;
      · grind;
  · grind +locals

/-! ## Hard direction for n = 1 (arbitrary m) -/

/-
The hard direction of Kronecker's theorem for n = 1.
This uses the classification of closed subgroups of ℝ.
-/
theorem kronecker_intrel_implies_approx_n1 (m : ℕ) (α : Fin m → ℝ) (β : ℝ)
    (h_intrel : ∀ r : ℤ,
      (∀ i : Fin m, ∃ z : ℤ, α i * (r : ℝ) = ↑z) →
      ∃ z : ℤ, β * (r : ℝ) = ↑z) :
    ∀ ε : ℝ, ε > 0 →
      ∃ q : Fin m → ℤ, ∃ p : ℤ,
        |∑ i : Fin m, (q i : ℝ) * α i - (p : ℝ) - β| < ε := by
  -- Let $G$ be the additive subgroup of ℝ generated by $\{\alpha_i : i \in \text{Fin } m\} \cup \{1\}$.
  let G := AddSubgroup.closure ({↑1} ∪ Set.range α);
  -- By the properties of the closure of a subgroup, $\beta \in \overline{G}$.
  have h_beta_closure : β ∈ closure (G : Set ℝ) := by
    -- Since $G$ is a closed subgroup of $\mathbb{R}$ containing $1$, by the classification of closed subgroups of $\mathbb{R}$, we have $\overline{G} = \mathbb{R}$ or $\overline{G} = \frac{1}{d}\mathbb{Z}$ for some $d \in \mathbb{N}$.
    have hG_closure : closure (G : Set ℝ) = Set.univ ∨ ∃ d : ℕ, 0 < d ∧ closure (G : Set ℝ) = Set.range (fun n : ℤ => (n : ℝ) / (d : ℝ)) := by
      convert closed_addsubgroup_contains_one ( AddSubgroup.topologicalClosure G ) ( isClosed_closure ) _ using 1;
      exact subset_closure <| AddSubgroup.subset_closure <| Set.mem_union_left _ <| Set.mem_singleton _;
    cases' hG_closure with h h;
    · aesop;
    · obtain ⟨ d, hd₀, hd ⟩ := h;
      -- Since $d·αᵢ ∈ ℤ$ for all $i$, we have $d·β ∈ ℤ$ by the hypothesis $h_intrel$.
      have h_d_beta_int : ∃ z : ℤ, β * d = z := by
        apply h_intrel;
        intro i
        have h_alpha_i : α i ∈ closure (G : Set ℝ) := by
          exact subset_closure <| AddSubgroup.subset_closure <| Set.mem_union_right _ <| Set.mem_range_self _;
        rw [ hd ] at h_alpha_i; obtain ⟨ z, hz ⟩ := h_alpha_i; use z; simp_all +decide [ div_eq_iff, hd₀.ne' ] ;
      exact hd.symm ▸ ⟨ h_d_beta_int.choose, by rw [ div_eq_iff ( by positivity ) ] ; linarith [ h_d_beta_int.choose_spec ] ⟩;
  rw [ Metric.mem_closure_iff ] at h_beta_closure;
  intro ε hε;
  obtain ⟨ b, hb₁, hb₂ ⟩ := h_beta_closure ε hε;
  -- Since $b \in G$, we can write $b = \sum_{i=1}^m q_i \alpha_i + p$ for some integers $q_i$ and $p$.
  obtain ⟨q, p, hq⟩ : ∃ q : Fin m → ℤ, ∃ p : ℤ, b = ∑ i, q i * α i + p := by
    refine' AddSubgroup.closure_induction ( fun x hx => _ ) _ _ _ hb₁;
    · rcases hx with ( rfl | ⟨ i, rfl ⟩ ) <;> [ exact ⟨ 0, 1, by norm_num ⟩ ; exact ⟨ fun j => if j = i then 1 else 0, 0, by simp +decide ⟩ ];
    · exact ⟨ 0, 0, by norm_num ⟩;
    · rintro x y hx hy ⟨ q₁, p₁, rfl ⟩ ⟨ q₂, p₂, rfl ⟩ ; exact ⟨ q₁ + q₂, p₁ + p₂, by simp +decide [ Finset.sum_add_distrib, add_mul, add_assoc, add_left_comm, add_comm ] ⟩ ;
    · rintro x hx ⟨ q, p, rfl ⟩ ; exact ⟨ -q, -p, by simp +decide [ Finset.sum_neg_distrib ] ; ring ⟩ ;
  exact ⟨ q, -p, by rw [ abs_sub_comm ] ; simpa [ hq ] using hb₂ ⟩

-- proved by subagent (see git history)

/-! ## Torus Separation Infrastructure -/

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

abbrev T := UnitAddTorus d

/-- A convenient normalized Haar measure on a compact additive group. -/
noncomputable def subgroupUnivPositiveCompact {α : Type*} [AddGroup α] [TopologicalSpace α]
    [ContinuousAdd α] [ContinuousNeg α] [CompactSpace α] [Nonempty α] :
    TopologicalSpace.PositiveCompacts α :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

def torusTranslate (a : UnitAddTorus d) : C(UnitAddTorus d, UnitAddTorus d) :=
  ContinuousMap.id _ + ContinuousMap.const _ a

def avgOverSubgroup (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) : C(UnitAddTorus d, ℂ) :=
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  ∫ h : H, f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) ∂μH

lemma integrable_translateFamily (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) :
    Integrable
      (fun h : H => f.comp (torusTranslate (d := d) (h : UnitAddTorus d)))
      (addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hcont :
      Continuous (fun h : H =>
        f.comp (torusTranslate (d := d) (h : UnitAddTorus d))) := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    change Continuous (fun z : H × UnitAddTorus d => f (z.2 + (z.1 : UnitAddTorus d)))
    exact f.continuous.comp
      ((continuous_snd).add ((continuous_subtype_val).comp continuous_fst))
  simpa [μH] using
    (hcont.continuousOn.integrableOn_compact (μ := μH) (K := (Set.univ : Set H)) isCompact_univ)

lemma avgOverSubgroup_apply (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) (y : UnitAddTorus d) :
    avgOverSubgroup (d := d) H f y =
      ∫ h : H, f (y + h) ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
  rw [avgOverSubgroup, ContinuousMap.integral_apply (integrable_translateFamily (d := d) H f)]
  rfl

lemma avgOverSubgroup_norm_le (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) :
    ‖avgOverSubgroup (d := d) H f‖ ≤ ‖f‖ := by
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hμ : μH Set.univ = 1 := by
    simpa [μH] using
      (addHaarMeasure_self (G := H) (K₀ := subgroupUnivPositiveCompact (α := H)))
  haveI : IsFiniteMeasure μH := ⟨by simp [hμ]⟩
  refine (ContinuousMap.norm_le (f := avgOverSubgroup (d := d) H f) (norm_nonneg _)).2 ?_
  intro y
  rw [avgOverSubgroup_apply]
  have hbound : ∀ᵐ h : H ∂μH, ‖f (y + h)‖ ≤ ‖f‖ := by
    exact Filter.Eventually.of_forall (fun h => f.norm_coe_le_norm (y + h))
  calc
    ‖∫ h : H, f (y + h) ∂μH‖ ≤ ‖f‖ * μH.real Set.univ := by
      exact MeasureTheory.norm_integral_le_of_norm_le_const (μ := μH) hbound
    _ = ‖f‖ := by
      rw [Measure.real_def, hμ, ENNReal.toReal_one, mul_one]

lemma avgOverSubgroup_sub (H : ClosedAddSubgroup (UnitAddTorus d))
    (f g : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H (f - g) =
      avgOverSubgroup (d := d) H f - avgOverSubgroup (d := d) H g := by
  rw [avgOverSubgroup, avgOverSubgroup, avgOverSubgroup]
  have hcomp :
      (fun h : H => (f - g).comp (torusTranslate (d := d) (h : UnitAddTorus d))) =
        fun h : H =>
          f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) -
            g.comp (torusTranslate (d := d) (h : UnitAddTorus d)) := by
    funext h
    ext y
    rfl
  rw [hcomp]
  rw [integral_sub (integrable_translateFamily (d := d) H f)
    (integrable_translateFamily (d := d) H g)]

lemma avgOverSubgroup_add (H : ClosedAddSubgroup (UnitAddTorus d))
    (f g : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H (f + g) =
      avgOverSubgroup (d := d) H f + avgOverSubgroup (d := d) H g := by
  rw [avgOverSubgroup, avgOverSubgroup, avgOverSubgroup]
  have hcomp :
      (fun h : H => (f + g).comp (torusTranslate (d := d) (h : UnitAddTorus d))) =
        fun h : H =>
          f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) +
            g.comp (torusTranslate (d := d) (h : UnitAddTorus d)) := by
    funext h
    ext y
    rfl
  rw [hcomp]
  rw [integral_add (integrable_translateFamily (d := d) H f)
    (integrable_translateFamily (d := d) H g)]

lemma avgOverSubgroup_smul (H : ClosedAddSubgroup (UnitAddTorus d))
    (c : ℂ) (f : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H (c • f) =
      c • avgOverSubgroup (d := d) H f := by
  rw [avgOverSubgroup, avgOverSubgroup]
  have hcomp :
      (fun h : H => (c • f).comp (torusTranslate (d := d) (h : UnitAddTorus d))) =
        fun h : H => c • f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) := by
    funext h
    ext y
    rfl
  rw [hcomp, integral_smul]

lemma avgOverSubgroup_norm_sub_le (H : ClosedAddSubgroup (UnitAddTorus d))
    (f g : C(UnitAddTorus d, ℂ)) :
    ‖avgOverSubgroup (d := d) H f - avgOverSubgroup (d := d) H g‖ ≤ ‖f - g‖ := by
  rw [← avgOverSubgroup_sub (d := d) H f g]
  exact avgOverSubgroup_norm_le (d := d) H (f - g)

lemma avgOverSubgroup_lipschitz (H : ClosedAddSubgroup (UnitAddTorus d)) :
    LipschitzWith 1 (avgOverSubgroup (d := d) H : C(UnitAddTorus d, ℂ) → C(UnitAddTorus d, ℂ)) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro f g
  simpa [dist_eq_norm] using avgOverSubgroup_norm_sub_le (d := d) H f g

lemma avgOverSubgroup_continuous (H : ClosedAddSubgroup (UnitAddTorus d)) :
    Continuous (avgOverSubgroup (d := d) H : C(UnitAddTorus d, ℂ) → C(UnitAddTorus d, ℂ)) :=
  (avgOverSubgroup_lipschitz (d := d) H).continuous

lemma integral_mFourier_eq_zero_of_nontrivial
    (n : d → ℤ) (H : ClosedAddSubgroup (UnitAddTorus d)) (h : H)
    (hh : UnitAddTorus.mFourier n h ≠ 1) :
    ∫ h : H, UnitAddTorus.mFourier n (h : UnitAddTorus d)
      ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) = 0 := by
  let μ : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hmul :
      ∀ x : H,
        UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) =
          UnitAddTorus.mFourier n (h : UnitAddTorus d) *
            UnitAddTorus.mFourier n (x : UnitAddTorus d) := by
    intro x
    simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
      Finset.prod_mul_distrib, mul_comm]
  have htrans :
      ∫ x : H, UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) ∂μ =
        UnitAddTorus.mFourier n (h : UnitAddTorus d) *
          ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
    calc
      ∫ x : H, UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) ∂μ
          = ∫ x : H, UnitAddTorus.mFourier n (h : UnitAddTorus d) *
              UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
              apply integral_congr_ae
              filter_upwards with x
              rw [hmul x]
      _ = UnitAddTorus.mFourier n (h : UnitAddTorus d) *
            ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
            rw [integral_const_mul]
  have hself :
      ∫ x : H, UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) ∂μ =
        ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
    simpa [μ] using
      (MeasureTheory.integral_add_right_eq_self
        (μ := μ) (f := fun x : H => UnitAddTorus.mFourier n (x : UnitAddTorus d)) h)
  have hEq :
      ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ =
        UnitAddTorus.mFourier n (h : UnitAddTorus d) *
          ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ :=
    hself.symm.trans htrans
  have hzero :
      (1 - UnitAddTorus.mFourier n (h : UnitAddTorus d)) *
        ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ = 0 := by
    have hzero' :
        ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ -
          UnitAddTorus.mFourier n (h : UnitAddTorus d) *
            ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ = 0 := by
      exact sub_eq_zero.mpr hEq
    simpa [sub_mul] using hzero'
  rcases mul_eq_zero.mp hzero with hbad | hgood
  · exact False.elim <| hh <| (sub_eq_zero.mp hbad).symm
  · exact hgood

def torusAnnihilator (H : ClosedAddSubgroup (UnitAddTorus d)) : Set (d → ℤ) :=
  {n | ∀ h : H, UnitAddTorus.mFourier n (h : UnitAddTorus d) = 1}

lemma avgOverSubgroup_mFourier_of_mem_ann
    (H : ClosedAddSubgroup (UnitAddTorus d)) (n : d → ℤ)
    (hn : n ∈ torusAnnihilator (d := d) H) :
    avgOverSubgroup (d := d) H (UnitAddTorus.mFourier n) = UnitAddTorus.mFourier n := by
  ext y
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hμ : μH Set.univ = 1 := by
    simpa [μH] using
      (addHaarMeasure_self (G := H) (K₀ := subgroupUnivPositiveCompact (α := H)))
  rw [avgOverSubgroup_apply]
  have hmul :
      ∀ h : H,
        UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) =
          UnitAddTorus.mFourier n y * UnitAddTorus.mFourier n (h : UnitAddTorus d) := by
    intro h
    simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
      Finset.prod_mul_distrib]
  have hconst :
      ∀ h : H,
        UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) =
          UnitAddTorus.mFourier n y := by
    intro h
    rw [hmul h, hn h, mul_one]
  calc
    ∫ h : H, UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) ∂μH
        = ∫ h : H, UnitAddTorus.mFourier n y ∂μH := by
            apply integral_congr_ae
            filter_upwards with h
            rw [hconst h]
    _ = UnitAddTorus.mFourier n y := by
          rw [integral_const, Measure.real_def, hμ, ENNReal.toReal_one, one_smul]

lemma avgOverSubgroup_mFourier_of_not_mem_ann
    (H : ClosedAddSubgroup (UnitAddTorus d)) (n : d → ℤ)
    (hn : n ∉ torusAnnihilator (d := d) H) :
    avgOverSubgroup (d := d) H (UnitAddTorus.mFourier n) = 0 := by
  ext y
  rw [avgOverSubgroup_apply]
  have hmul :
      ∀ h : H,
        UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) =
          UnitAddTorus.mFourier n y * UnitAddTorus.mFourier n (h : UnitAddTorus d) := by
    intro h
    simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
      Finset.prod_mul_distrib]
  obtain ⟨h, hh⟩ : ∃ h : H, UnitAddTorus.mFourier n (h : UnitAddTorus d) ≠ 1 := by
    by_contra hcontra
    apply hn
    intro h
    by_contra hh
    exact hcontra ⟨h, hh⟩
  calc
    ∫ h' : H, UnitAddTorus.mFourier n (y + (h' : UnitAddTorus d))
        ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H)))
        = ∫ h' : H, UnitAddTorus.mFourier n y *
            UnitAddTorus.mFourier n (h' : UnitAddTorus d)
            ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
              apply integral_congr_ae
              filter_upwards with h'
              rw [hmul h']
    _ = UnitAddTorus.mFourier n y *
          ∫ h' : H, UnitAddTorus.mFourier n (h' : UnitAddTorus d)
            ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
              rw [integral_const_mul]
    _ = 0 := by
          rw [integral_mFourier_eq_zero_of_nontrivial (d := d) n H h hh, mul_zero]

def annSubmodule (H : ClosedAddSubgroup (UnitAddTorus d)) :
    Submodule ℂ C(UnitAddTorus d, ℂ) :=
  Submodule.span ℂ ((fun n : d → ℤ => UnitAddTorus.mFourier n) '' torusAnnihilator (d := d) H)

lemma avgOverSubgroup_mem_annSubmodule_mFourier
    (H : ClosedAddSubgroup (UnitAddTorus d)) (n : d → ℤ) :
    avgOverSubgroup (d := d) H (UnitAddTorus.mFourier n) ∈ annSubmodule (d := d) H := by
  by_cases hn : n ∈ torusAnnihilator (d := d) H
  · have hmem : UnitAddTorus.mFourier n ∈ annSubmodule (d := d) H := by
      exact Submodule.subset_span ⟨n, hn, rfl⟩
    simpa [avgOverSubgroup_mFourier_of_mem_ann (d := d) H n hn] using hmem
  · rw [avgOverSubgroup_mFourier_of_not_mem_ann (d := d) H n hn]
    exact Submodule.zero_mem (annSubmodule (d := d) H)

lemma avgOverSubgroup_mem_annSubmodule_of_mem_span
    (H : ClosedAddSubgroup (UnitAddTorus d))
    {f : C(UnitAddTorus d, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d)))) :
    avgOverSubgroup (d := d) H f ∈ annSubmodule (d := d) H := by
  let p :
      (g : C(UnitAddTorus d, ℂ)) →
        g ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d))) → Prop :=
    fun g _ => avgOverSubgroup (d := d) H g ∈ annSubmodule (d := d) H
  change p f hf
  refine Submodule.span_induction (s := Set.range (UnitAddTorus.mFourier (d := d))) (p := p) ?_ ?_ ?_ ?_ hf
  · intro g hg
    rcases hg with ⟨n, rfl⟩
    exact avgOverSubgroup_mem_annSubmodule_mFourier (d := d) H n
  · simp [p, avgOverSubgroup]
  · intro x y hx hy hxmem hymem
    simpa [p, avgOverSubgroup_add (d := d) H x y] using
      (annSubmodule (d := d) H).add_mem hxmem hymem
  · intro c x hx hxmem
    simpa [p, avgOverSubgroup_smul (d := d) H c x] using
      (annSubmodule (d := d) H).smul_mem c hxmem

lemma avgOverSubgroup_mem_closure_annSubmodule
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H f ∈ closure (annSubmodule (d := d) H : Set C(UnitAddTorus d, ℂ)) := by
  have hf :
      f ∈ closure (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d))) :
        Set C(UnitAddTorus d, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe,
      UnitAddTorus.span_mFourier_closure_eq_top]
    simp
  refine map_mem_closure (avgOverSubgroup_continuous (d := d) H) hf ?_
  intro g hg
  exact avgOverSubgroup_mem_annSubmodule_of_mem_span (d := d) H hg

def sameValueCLM (x : UnitAddTorus d) : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ x : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ) -
    (ContinuousMap.evalCLM ℂ (0 : UnitAddTorus d) : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ)

def sameValueSubmodule (x : UnitAddTorus d) : Submodule ℂ C(UnitAddTorus d, ℂ) :=
  (sameValueCLM (d := d) x).toLinearMap.ker

omit [Fintype d] in
lemma mem_sameValueSubmodule_iff
    (x : UnitAddTorus d) (f : C(UnitAddTorus d, ℂ)) :
    f ∈ sameValueSubmodule (d := d) x ↔ f x = f 0 := by
  simp [sameValueSubmodule, sameValueCLM, sub_eq_zero]

omit [Fintype d] in
lemma isClosed_sameValueSubmodule (x : UnitAddTorus d) :
    IsClosed (sameValueSubmodule (d := d) x : Set C(UnitAddTorus d, ℂ)) := by
  simpa [sameValueSubmodule] using
    (ContinuousLinearMap.isClosed_ker (sameValueCLM (d := d) x))

lemma annSubmodule_le_sameValueSubmodule
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1) :
    annSubmodule (d := d) H ≤ sameValueSubmodule (d := d) x := by
  refine Submodule.span_le.2 ?_
  intro f hf
  rcases hf with ⟨n, hn, rfl⟩
  show UnitAddTorus.mFourier n ∈ sameValueSubmodule (d := d) x
  rw [mem_sameValueSubmodule_iff]
  calc
    UnitAddTorus.mFourier n x = 1 := hx n hn
    _ = UnitAddTorus.mFourier n (0 : UnitAddTorus d) := by
      symm
      simp [UnitAddTorus.mFourier]

lemma closure_annSubmodule_le_sameValueSubmodule
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1) :
    closure (annSubmodule (d := d) H : Set C(UnitAddTorus d, ℂ)) ⊆
      sameValueSubmodule (d := d) x := by
  have hclosure :
      (annSubmodule (d := d) H).topologicalClosure ≤ sameValueSubmodule (d := d) x :=
    Submodule.topologicalClosure_minimal (annSubmodule (d := d) H)
      (annSubmodule_le_sameValueSubmodule (d := d) H x hx)
      (isClosed_sameValueSubmodule (d := d) x)
  simpa [Submodule.topologicalClosure_coe] using hclosure

lemma avgOverSubgroup_eq_at_zero_of_annihilator
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1)
    (f : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H f x = avgOverSubgroup (d := d) H f 0 := by
  have havg_closure :=
    avgOverSubgroup_mem_closure_annSubmodule (d := d) H f
  have havg_same :
      avgOverSubgroup (d := d) H f ∈ sameValueSubmodule (d := d) x :=
    closure_annSubmodule_le_sameValueSubmodule (d := d) H x hx havg_closure
  exact (mem_sameValueSubmodule_iff (d := d) x _).mp havg_same

def xPlusH (H : ClosedAddSubgroup (UnitAddTorus d)) (x : UnitAddTorus d) :
    Set (UnitAddTorus d) :=
  Set.range fun h : H => x + (h : UnitAddTorus d)

omit [Fintype d] in
lemma isCompact_xPlusH
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d) :
    IsCompact (xPlusH (d := d) H x) := by
  simpa [xPlusH] using
    (isCompact_range
      (continuous_const.add continuous_subtype_val :
        Continuous fun h : H => x + (h : UnitAddTorus d)))

omit [Fintype d] in
lemma disjoint_xPlusH
    (H : ClosedAddSubgroup (UnitAddTorus d))
    {x : UnitAddTorus d}
    (hx : x ∉ H) :
    Disjoint (xPlusH (d := d) H x) (H : Set (UnitAddTorus d)) := by
  refine Set.disjoint_left.2 ?_
  intro y hyx hyH
  rcases hyx with ⟨h, rfl⟩
  exact hx <| by
    simpa using H.sub_mem hyH h.2

lemma subgroup_univ_measure
    (H : ClosedAddSubgroup (UnitAddTorus d)) :
    (addHaarMeasure (subgroupUnivPositiveCompact (α := H))) Set.univ = 1 := by
  simpa using
    (addHaarMeasure_self (G := H) (K₀ := subgroupUnivPositiveCompact (α := H)))

lemma integral_const_subgroup
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (c : ℂ) :
    (∫ _h : H, c ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H)))) = c := by
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hμ : μH Set.univ = 1 := by
    simpa [μH] using subgroup_univ_measure (d := d) H
  haveI : IsFiniteMeasure μH := ⟨by simp [hμ]⟩
  rw [integral_const, Measure.real_def, hμ, ENNReal.toReal_one, one_smul]

def ofRealContinuousMap (f : C(UnitAddTorus d, ℝ)) : C(UnitAddTorus d, ℂ) where
  toFun y := (f y : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

lemma avgOverSubgroup_zero_at_zero
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ))
    (hf : Set.EqOn f (fun _ => 0) (H : Set (UnitAddTorus d))) :
    avgOverSubgroup (d := d) H f 0 = 0 := by
  rw [avgOverSubgroup_apply]
  have hconst : (fun h : H => f (0 + (h : UnitAddTorus d))) = fun _ : H => 0 := by
    funext h
    simpa using hf (x := (h : UnitAddTorus d)) h.2
  rw [hconst, integral_zero]

lemma avgOverSubgroup_one_at_x
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (f : C(UnitAddTorus d, ℂ))
    (hf : Set.EqOn f (fun _ => 1) (xPlusH (d := d) H x)) :
    avgOverSubgroup (d := d) H f x = 1 := by
  rw [avgOverSubgroup_apply]
  have hconst : (fun h : H => f (x + (h : UnitAddTorus d))) = fun _ : H => 1 := by
    funext h
    exact hf (x := x + (h : UnitAddTorus d)) ⟨h, rfl⟩
  rw [hconst]
  exact integral_const_subgroup (d := d) H 1

theorem mem_of_mFourier_eq_one_on_annihilator
    (H : ClosedAddSubgroup (UnitAddTorus d))
    {x : UnitAddTorus d}
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1) :
    x ∈ H := by
  by_contra hxnot
  obtain ⟨fR, hfR0, hfR1, _⟩ :=
    exists_continuous_zero_one_of_isCompact'
      (isCompact_xPlusH (d := d) H x) H.isClosed'
      (disjoint_xPlusH (d := d) H hxnot)
  let f : C(UnitAddTorus d, ℂ) := ofRealContinuousMap (d := d) fR
  have hf0 : Set.EqOn f (fun _ => 0) (H : Set (UnitAddTorus d)) := by
    intro y hy
    change ((fR y : ℂ) = 0)
    simpa [f] using hfR0 (x := y) hy
  have hf1 : Set.EqOn f (fun _ => 1) (xPlusH (d := d) H x) := by
    intro y hy
    change ((fR y : ℂ) = 1)
    simpa [f] using hfR1 (x := y) hy
  have h_eq :
      avgOverSubgroup (d := d) H f x = avgOverSubgroup (d := d) H f 0 :=
    avgOverSubgroup_eq_at_zero_of_annihilator (d := d) H x hx f
  have h0 : avgOverSubgroup (d := d) H f 0 = 0 :=
    avgOverSubgroup_zero_at_zero (d := d) H f hf0
  have h1 : avgOverSubgroup (d := d) H f x = 1 :=
    avgOverSubgroup_one_at_x (d := d) H x f hf1
  have : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = avgOverSubgroup (d := d) H f x := by simpa using h1.symm
      _ = avgOverSubgroup (d := d) H f 0 := h_eq
      _ = 0 := h0
  exact one_ne_zero this

lemma mFourier_eq_one_iff_exists_int
    (n : ℕ) (r : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier r (fun j => ((x j : ℝ) : AddCircle (1 : ℝ))) = 1 ↔
      ∃ z : ℤ, (∑ j, x j * (r j : ℝ)) = z := by
  have hmfourier :
      UnitAddTorus.mFourier r (fun j => ((x j : ℝ) : AddCircle (1 : ℝ))) =
        Complex.exp (2 * Real.pi * Complex.I * (∑ j, x j * (r j : ℝ))) := by
    calc
      UnitAddTorus.mFourier r (fun j => ((x j : ℝ) : AddCircle (1 : ℝ))) =
          ∏ j, Complex.exp (2 * Real.pi * Complex.I * ((r j : ℝ) * x j)) := by
            simp [UnitAddTorus.mFourier, mul_assoc, mul_left_comm, mul_comm]
      _ = Complex.exp (∑ j, 2 * Real.pi * Complex.I * ((r j : ℝ) * x j)) := by
            rw [← Complex.exp_sum]
      _ = Complex.exp (2 * Real.pi * Complex.I * (∑ j, x j * (r j : ℝ))) := by
            congr 1
            rw [show ((↑(∑ j, x j * (r j : ℝ)) : ℝ) : ℂ) =
                ∑ j, (((x j * (r j : ℝ)) : ℝ) : ℂ) by
                  simp]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [hmfourier]
  constructor
  · intro h
    rw [Complex.exp_eq_one_iff] at h
    rcases h with ⟨m, hm⟩
    use m
    have him := congrArg Complex.im hm
    simp at him
    nlinarith [Real.pi_pos]
  · rintro ⟨z, hz⟩
    rw [hz]
    rw [Complex.exp_eq_one_iff]
    refine ⟨z, ?_⟩
    simp [mul_left_comm, mul_comm]

/-- A BM-facing specialization of Kronecker's hard direction: one common denominator for many
target coordinates. The nonzero-denominator normalization is deferred to the BM application. -/
theorem kronecker_intrel_implies_approx_common_q_int
    (n : ℕ) (α β : Fin n → ℝ)
    (h_intrel : ∀ r : Fin n → ℤ,
      (∃ z : ℤ, ∑ j, α j * (r j : ℝ) = z) →
      ∃ z : ℤ, ∑ j, β j * (r j : ℝ) = z) :
    ∀ ε > 0, ∃ q : ℤ, ∃ p : Fin n → ℤ,
      ∀ j, |(q : ℝ) * α j - (p j : ℝ) - β j| < ε := by
  intro ε hε
  let αbar : UnitAddTorus (Fin n) := fun j => ((α j : ℝ) : AddCircle (1 : ℝ))
  let βbar : UnitAddTorus (Fin n) := fun j => ((β j : ℝ) : AddCircle (1 : ℝ))
  let Z : AddSubgroup (UnitAddTorus (Fin n)) := AddSubgroup.zmultiples αbar
  let H : ClosedAddSubgroup (UnitAddTorus (Fin n)) :=
    ⟨Z.topologicalClosure, AddSubgroup.isClosed_topologicalClosure Z⟩
  have hα_mem : αbar ∈ H := by
    change αbar ∈ Z.topologicalClosure
    exact AddSubgroup.le_topologicalClosure Z <|
      by
        change αbar ∈ AddSubgroup.zmultiples αbar
        convert AddSubgroup.zsmul_mem_zmultiples αbar (1 : ℤ) using 1
        simp
  have hβ_mem : βbar ∈ H := by
    apply mem_of_mFourier_eq_one_on_annihilator (H := H)
    intro r hr
    have hα_fourier : UnitAddTorus.mFourier r αbar = 1 := by
      exact hr ⟨αbar, hα_mem⟩
    have hα_int : ∃ z : ℤ, (∑ j, α j * (r j : ℝ)) = z := by
      exact (mFourier_eq_one_iff_exists_int n r α).mp hα_fourier
    have hβ_int := h_intrel r hα_int
    exact (mFourier_eq_one_iff_exists_int n r β).mpr hβ_int
  have hβ_closure : βbar ∈ closure (Z : Set (UnitAddTorus (Fin n))) := by
    simpa [H, Z, AddSubgroup.topologicalClosure_coe] using hβ_mem
  rw [Metric.mem_closure_iff] at hβ_closure
  obtain ⟨x, hxS, hxdist⟩ := hβ_closure ε hε
  obtain ⟨q, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hxS
  refine ⟨q, fun j => round ((q : ℝ) * α j - β j), ?_⟩
  intro j
  have hcoord :
      dist (((q • αbar) : UnitAddTorus (Fin n)) j) (βbar j) < ε := by
    simpa [dist_comm] using (dist_pi_lt_iff hε).mp hxdist j
  have hnorm :
      ‖((((q : ℝ) * α j - β j : ℝ) : AddCircle (1 : ℝ)))‖ < ε := by
    simpa [dist_eq_norm, αbar, βbar, zsmul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using hcoord
  have hround :
      |((q : ℝ) * α j - β j) - round ((q : ℝ) * α j - β j)| < ε := by
    have := hnorm
    rw [AddCircle.norm_eq] at this
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hround

end

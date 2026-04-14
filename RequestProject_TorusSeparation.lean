/-
# Hard Direction of Kronecker's Theorem

This file contains the proof of the hard direction of Kronecker's approximation
theorem for the case n = 1 (arbitrary m), along with the infrastructure needed
for the general case.

The general case (arbitrary n) requires the double annihilator theorem for the
n-torus (Pontryagin duality), which states that a closed subgroup of (ℝ/ℤ)ⁿ
is determined by its annihilator in ℤⁿ. This is left as sorry.
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 1600000

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

/-! ## The full hard direction (general n × m case) -/

/-- The hard direction of Kronecker's theorem (general case).

The proof proceeds as follows:
1. Define the subgroup G of ℝⁿ generated by the α-vectors and ℤⁿ.
2. Show that β is in the closure of G using the integer-relation condition.
3. The key step uses the **torus separation lemma** (double annihilator theorem):
   for a closed subgroup H of (ℝ/ℤ)ⁿ, x ∈ H iff ⟨r, x⟩ ∈ ℤ for all r ∈ Ann(H).
4. The torus separation lemma is proved by induction on n, using:
   - Classification of closed subgroups of ℝ/ℤ (n=1 base case)
   - Character extension: continuous group homomorphisms from closed subgroups
     of (ℝ/ℤ)ⁿ to ℝ/ℤ are restrictions of integer linear forms
   This is equivalent to a special case of Pontryagin duality for compact
   abelian groups. -/
theorem kronecker_intrel_implies_approx_general (m n : ℕ) (α : Fin m → Fin n → ℝ) (β : Fin n → ℝ)
    (h_intrel : ∀ r : Fin n → ℤ,
      (∀ i : Fin m, ∃ z : ℤ, ∑ j : Fin n, α i j * (r j : ℝ) = ↑z) →
      ∃ z : ℤ, ∑ j : Fin n, β j * (r j : ℝ) = ↑z) :
    ∀ ε : ℝ, ε > 0 →
      ∃ q : Fin m → ℤ, ∃ p : Fin n → ℤ,
        ∀ j : Fin n, |∑ i : Fin m, (q i : ℝ) * α i j - (p j : ℝ) - β j| < ε := by
  sorry

end
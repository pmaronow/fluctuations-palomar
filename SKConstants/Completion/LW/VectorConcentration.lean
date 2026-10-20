module

public import SKConstants.SKDisorderNorm
public import SKConstants.Completion.LM4.FactorialBernstein

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Metric Set
open scoped BigOperators NNReal ENNReal InnerProductSpace

namespace SKConstants.Completion.LW

lemma euclidean_half_separated_card_le (n : ℕ)
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (hN : ∀ x ∈ N, ‖x‖ ≤ 1)
    (hsep : (↑N : Set (EuclideanSpace ℝ (Fin n))).Pairwise
      (fun x y => (1 / 2 : ℝ) < dist x y)) :
    (N.card : ℝ) ≤ (5 : ℝ) ^ n := by
  have hd : PairwiseDisjoint (↑N : Set (EuclideanSpace ℝ (Fin n)))
      (fun x => ball x (1 / 4 : ℝ)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hdist := dist_triangle x z y
    have hxz : dist x z < (1 / 4 : ℝ) := by simpa [dist_comm] using hzx
    have hzy' : dist z y < (1 / 4 : ℝ) := hzy
    have hxy' := hsep hx hy hxy
    linarith
  have hsub : (⋃ x ∈ N, ball x (1 / 4 : ℝ)) ⊆
      ball (0 : EuclideanSpace ℝ (Fin n)) (5 / 4 : ℝ) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    have hdist := dist_triangle z x 0
    have hxn : dist x 0 ≤ 1 := by simpa using hN x hx
    change dist z 0 < (5 / 4 : ℝ)
    have hzxn : dist z x < (1 / 4 : ℝ) := hzx
    linarith
  have hvol := measureReal_mono hsub (measure_ball_lt_top (μ := volume)).ne
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)] at hvol
  simp_rw [euclidean_real_ball_scale n _ (1 / 4 : ℝ) (by norm_num)] at hvol
  rw [Finset.sum_const, nsmul_eq_mul,
    euclidean_real_ball_scale n _ (5 / 4 : ℝ) (by norm_num)] at hvol
  have hv : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    exact ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ (by norm_num)))
      (measure_ball_lt_top (μ := volume)).ne
  have hp : 0 < (1 / 4 : ℝ) ^ n := pow_pos (by norm_num) _
  have he : (5 / 4 : ℝ) ^ n = (5 : ℝ) ^ n * (1 / 4 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  rw [he] at hvol
  nlinarith [mul_pos hp hv]

theorem exists_euclidean_half_net (n : ℕ) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ N, ‖x‖ ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 → ∃ y ∈ N, dist x y ≤ (1 / 2 : ℝ)) ∧
      (N.card : ℝ) ≤ (5 : ℝ) ^ n := by
  let A := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  obtain ⟨D, hDA, hDf, hDc⟩ :=
    exists_finite_isCover_of_isCompact (ε := (1 / 4 : ℝ≥0)) (by norm_num)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hcover : coveringNumber (1 / 4 : ℝ≥0) A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hDf)
    exact hDc.coveringNumber_le_encard hDA
  have hpack : packingNumber (1 / 2 : ℝ≥0) A ≠ ⊤ := by
    apply ne_top_of_le_ne_top hcover
    calc
      _ = packingNumber (2 * (1 / 4 : ℝ≥0)) A := by norm_num
      _ ≤ externalCoveringNumber (1 / 4 : ℝ≥0) A :=
        packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ coveringNumber (1 / 4 : ℝ≥0) A := externalCoveringNumber_le_coveringNumber _ _
  let S := maximalSeparatedSet (1 / 2 : ℝ≥0) A
  have hSf : S.Finite := Set.encard_ne_top_iff.mp (by
    rw [show S.encard = packingNumber (1 / 2 : ℝ≥0) A from encard_maximalSeparatedSet hpack]
    exact hpack)
  have hSA : S ⊆ A := maximalSeparatedSet_subset
  have hSc : IsCover (1 / 2 : ℝ≥0) A S := isCover_maximalSeparatedSet hpack
  have hSs : IsSeparated (1 / 2 : ℝ≥0) S := isSeparated_maximalSeparatedSet
  refine ⟨hSf.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [A, mem_closedBall, dist_zero_right] using hSA (hSf.mem_toFinset.mp hx)
  · intro x hx
    have hxA : x ∈ A := by simpa only [A, mem_closedBall, dist_zero_right] using hx
    obtain ⟨y, hy, hxy⟩ := hSc hxA
    refine ⟨y, hSf.mem_toFinset.mpr hy, ?_⟩
    change edist x y ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) at hxy
    rw [edist_dist] at hxy
    have hh : ENNReal.ofReal (1 / 2 : ℝ) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [← hh] at hxy
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hxy
  · apply euclidean_half_separated_card_le n hSf.toFinset
    · intro x hx
      simpa only [A, mem_closedBall, dist_zero_right] using hSA (hSf.mem_toFinset.mp hx)
    · intro x hx y hy hxy
      have h := hSs (hSf.mem_toFinset.mp hx) (hSf.mem_toFinset.mp hy) hxy
      change ((1 / 2 : ℝ≥0) : ℝ≥0∞) < edist x y at h
      rw [edist_dist] at h
      have hh : ENNReal.ofReal (1 / 2 : ℝ) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      rw [← hh] at h
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp h

theorem norm_le_of_half_net {d : ℕ} (z : EuclideanSpace ℝ (Fin d))
    (N : Finset (EuclideanSpace ℝ (Fin d)))
    (hcover : ∀ x, ‖x‖ ≤ 1 → ∃ a ∈ N, dist x a ≤ (1/2 : ℝ))
    {b : ℝ} (hb : 0 ≤ b) (htest : ∀ a ∈ N, |⟪z,a⟫_ℝ| ≤ b) :
    ‖z‖ ≤ 2*b := by
  by_cases hz : z = 0
  · simpa [hz] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let x := (‖z‖⁻¹ : ℝ) • z
  have hx : ‖x‖ = 1 := by simp [x, norm_smul, hn.ne']
  obtain ⟨a, ha, hxa⟩ := hcover x hx.le
  have hi : ⟪z,x⟫_ℝ = ‖z‖ := by
    rw [show x = (‖z‖⁻¹ : ℝ) • z from rfl, inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
  have hd : |⟪z,x-a⟫_ℝ| ≤ ‖z‖/2 := by
    calc
      _ ≤ ‖z‖ * ‖x-a‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖z‖ * (1/2 : ℝ) := mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using hxa) (norm_nonneg _)
      _ = _ := by ring
  have htri : |⟪z,x⟫_ℝ| ≤ |⟪z,x-a⟫_ℝ| + |⟪z,a⟫_ℝ| := by
    rw [inner_sub_right]
    have H := abs_add_le (⟪z,x⟫_ℝ-⟪z,a⟫_ℝ) ⟪z,a⟫_ℝ
    simpa only [sub_add_cancel] using H
  rw [hi, abs_of_pos hn] at htri
  linarith [htest a ha]

theorem iid_vector_average_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n d : ℕ} (hn : 0 < n)
    (U : Ω → EuclideanSpace ℝ (Fin d)) (hU : Measurable U)
    {v radius η : ℝ} (hv : 0 < v) (hr : 0 < radius) (hη : 0 < η)
    (hRows : ∀ a : EuclideanSpace ℝ (Fin d), ‖a‖ ≤ 1 →
      Concentration.LocalQuadraticMGF (fun ω => ⟪U ω,a⟫_ℝ) μ v radius) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | 2*η < ‖(n : ℝ)⁻¹ • ∑ i : Fin n, U (ω i)‖} ≤
        2 * (5 : ℝ)^d * Real.exp (-(n : ℝ) *
          min (η^2/(4*v)) (radius*η/2)) := by
  classical
  let P := Measure.pi (fun _ : Fin n => μ)
  obtain ⟨N, hN, hcover, hcard⟩ := exists_euclidean_half_net d
  let E (a : EuclideanSpace ℝ (Fin d)) : Set (Fin n → Ω) :=
    {ω | η ≤ |(∑ i : Fin n, ⟪U (ω i),a⟫_ℝ)/(n : ℝ)|}
  have hsub : {ω | 2*η < ‖(n : ℝ)⁻¹ • ∑ i : Fin n, U (ω i)‖} ⊆
      ⋃ a ∈ N, E a := by
    intro ω hω
    by_contra hnot
    have htest (a : EuclideanSpace ℝ (Fin d)) (ha : a ∈ N) :
        |⟪(n : ℝ)⁻¹ • ∑ i : Fin n, U (ω i),a⟫_ℝ| ≤ η := by
      have hlt : |(∑ i : Fin n, ⟪U (ω i),a⟫_ℝ)/(n : ℝ)| < η := by
        apply lt_of_not_ge
        intro H
        exact hnot (by simp only [mem_iUnion]; exact ⟨a,ha,H⟩)
      simpa only [inner_smul_left, sum_inner, RCLike.conj_to_real, div_eq_mul_inv,
        mul_comm] using hlt.le
    exact (not_lt_of_ge (norm_le_of_half_net _ N hcover hη.le htest)) hω
  calc
    P.real {ω | 2*η < ‖(n : ℝ)⁻¹ • ∑ i : Fin n, U (ω i)‖}
        ≤ P.real (⋃ a ∈ N, E a) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ a ∈ N, P.real (E a) := measureReal_biUnion_finset_le N _
    _ ≤ ∑ _a ∈ N, 2 * Real.exp (-(n : ℝ) *
        min (η^2/(4*v)) (radius*η/2)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hmeas : Measurable (fun ω => ⟪U ω,a⟫_ℝ) := by fun_prop
      have H := LM4.iid_sum_abs_of_localMGF μ hmeas (hRows a (hN a ha)) hv hr hn hη
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hevent : E a = {ω : Fin n → Ω |
          (n : ℝ)*η ≤ |∑ i : Fin n, ⟪U (ω i),a⟫_ℝ|} := by
        ext ω
        simp only [E, mem_ofPred_eq, abs_div, abs_of_pos hnR]
        rw [le_div_iff₀ hnR, mul_comm η]
      rw [hevent]
      exact H
    _ = 2 * (N.card : ℝ) * Real.exp (-(n : ℝ) *
        min (η^2/(4*v)) (radius*η/2)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by gcongr

end SKConstants.Completion.LW


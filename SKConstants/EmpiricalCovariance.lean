module

public import SKConstants.SubGaussianProducts
public import SKConstants.QuadraticNet

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace NNReal Matrix.Norms.L2Operator

namespace SKConstants.Concentration

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d : ℕ}

def centeredEmpiricalCovariance
    (μ : Measure Ω) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun j k ↦ (∑ i, (X i ω j * X i ω k - ∫ u, X i u j * X i u k ∂μ)) / (n : ℝ)

theorem measurable_centeredEmpiricalCovariance
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (hMeas : ∀ i, Measurable (X i)) :
    Measurable (centeredEmpiricalCovariance μ X) := by
  unfold centeredEmpiricalCovariance
  fun_prop

lemma matrix_quadratic_eq_sum (A : Matrix (Fin d) (Fin d) ℝ)
    (a : EuclideanSpace ℝ (Fin d)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A a, a⟫_ℝ =
      ∑ j, ∑ k, a j * a k * A j k := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma linearForm_square_eq_sum (x a : EuclideanSpace ℝ (Fin d)) :
    ⟪x, a⟫_ℝ ^ 2 = ∑ j, ∑ k, a j * a k * (x j * x k) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma linearForm_square_integral_eq_sum
    (X : Ω → EuclideanSpace ℝ (Fin d))
    (hInt : ∀ j k, Integrable (fun ω ↦ X ω j * X ω k) μ)
    (a : EuclideanSpace ℝ (Fin d)) :
    (∫ ω, ⟪X ω, a⟫_ℝ ^ 2 ∂μ) =
      ∑ j, ∑ k, a j * a k * ∫ ω, X ω j * X ω k ∂μ := by
  simp_rw [linearForm_square_eq_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro k _
      exact (hInt j k).const_mul (a j * a k)
  · intro j _
    exact integrable_finsetSum _ (fun k _ ↦ (hInt j k).const_mul (a j * a k))

theorem centeredEmpiricalCovariance_quadratic
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hInt : ∀ i j k, Integrable (fun ω ↦ X i ω j * X i ω k) μ)
    (ω : Ω) (a : EuclideanSpace ℝ (Fin d)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredEmpiricalCovariance μ X ω) a, a⟫_ℝ =
      (∑ i, centeredObservable μ (fun u ↦ ⟪X i u, a⟫_ℝ ^ 2) ω) / (n : ℝ) := by
  rw [matrix_quadratic_eq_sum]
  simp only [centeredEmpiricalCovariance, centeredObservable,
    ← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
  apply congrArg (fun r : ℝ ↦ r / (n : ℝ))
  calc
    _ = ∑ j, ∑ i, ∑ k,
        a j * a k * (X i ω j * X i ω k - ∫ u, X i u j * X i u k ∂μ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k,
        a j * a k * (X i ω j * X i ω k - ∫ u, X i u j * X i u k ∂μ) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← linearForm_square_eq_sum, ← linearForm_square_integral_eq_sum (X i) (hInt i)]

theorem centeredEmpiricalCovariance_symmetric
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (ω : Ω)
    (a b : EuclideanSpace ℝ (Fin d)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredEmpiricalCovariance μ X ω) a, b⟫_ℝ =
      ⟪a, Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredEmpiricalCovariance μ X ω) b⟫_ℝ := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hs : centeredEmpiricalCovariance μ X ω k j =
      centeredEmpiricalCovariance μ X ω j k := by
    simp only [centeredEmpiricalCovariance, mul_comm]
  rw [hs]
  ring

lemma subGaussian_row_coordinate_integrable_product [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ (Fin d)) (K : ℝ≥0) (hK : 0 < K)
    (hMGF : ∀ a : EuclideanSpace ℝ (Fin d), ‖a‖ ≤ 1 →
      HasSubgaussianMGF (fun ω ↦ ⟪X ω, a⟫_ℝ) K μ) (j k : Fin d) :
    Integrable (fun ω ↦ X ω j * X ω k) μ := by
  have hcoord (l : Fin d) : HasSubgaussianMGF (fun ω ↦ X ω l) K μ := by
    simpa [EuclideanSpace.inner_single_right] using
      hMGF (EuclideanSpace.single l 1) (by simp only [PiLp.norm_single, norm_one, le_refl])
  have hm := (subGaussian_product_factorial_moments μ
    (fun ω ↦ X ω j) (fun ω ↦ X ω k) K hK (hcoord j) (hcoord k)).1 1
  apply hm.mono' ((hcoord j).aestronglyMeasurable.mul (hcoord k).aestronglyMeasurable)
  filter_upwards with ω
  simp only [Real.norm_eq_abs, pow_one, Pi.mul_apply, le_refl]

theorem independent_covariance_quadratic_tail
    (hn : 0 < n) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (K : ℝ≥0) (hK : 0 < K)
    (hMGF : ∀ i (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      HasSubgaussianMGF (fun ω ↦ ⟪X i ω, a⟫_ℝ) K μ)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    μ.real {ω | η ≤
      |⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredEmpiricalCovariance μ X ω) a, a⟫_ℝ|} ≤
      2 * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (4 * (2 * (4 * Real.exp 1 * (K : ℝ)) ^ 2)))
        ((1 / (8 * Real.exp 1 * (K : ℝ))) * η / 2)) := by
  have : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  let Y : Fin n → Ω → ℝ :=
    fun i ↦ centeredObservable μ (fun u ↦ ⟪X i u, a⟫_ℝ ^ 2)
  have hYIndep : iIndepFun Y μ := by
    convert hIndep.comp
      (fun i (v : EuclideanSpace ℝ (Fin d)) ↦
        ⟪v, a⟫_ℝ ^ 2 - ∫ u, ⟪X i u, a⟫_ℝ ^ 2 ∂μ)
      (fun _ ↦ by fun_prop) using 1
    rfl
  have hYMeas : ∀ i, Measurable (Y i) := by
    intro i
    change Measurable (fun ω ↦ ⟪X i ω, a⟫_ℝ ^ 2 - ∫ u, ⟪X i u, a⟫_ℝ ^ 2 ∂μ)
    have hXi := hMeas i
    fun_prop
  have hRows : ∀ i, LocalQuadraticMGF (Y i) μ
      (2 * (4 * Real.exp 1 * (K : ℝ)) ^ 2) (1 / (8 * Real.exp 1 * (K : ℝ))) := by
    intro i
    apply subGaussian_centered_square_localMGF μ _ _ K hK (hMGF i a ha)
    have hXi := hMeas i
    fun_prop
  have hInt : ∀ i j k, Integrable (fun ω ↦ X i ω j * X i ω k) μ :=
    fun i ↦ subGaussian_row_coordinate_integrable_product (X i) K hK (hMGF i)
  simp_rw [centeredEmpiricalCovariance_quadratic X hInt]
  exact independent_average_bernstein hn hYIndep hYMeas hRows
    (by have hKR : 0 < (K : ℝ) := NNReal.coe_pos.mpr hK; positivity)
    (by have hKR : 0 < (K : ℝ) := NNReal.coe_pos.mpr hK; positivity) hη

theorem independent_empirical_covariance_operator_tail
    (hn : 0 < n) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (K : ℝ≥0) (hK : 0 < K)
    (hMGF : ∀ i (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      HasSubgaussianMGF (fun ω ↦ ⟪X i ω, a⟫_ℝ) K μ)
    (η : ℝ) (hη : 0 < η) :
    μ.real {ω | 2 * η < ‖centeredEmpiricalCovariance μ X ω‖} ≤
      2 * (9 : ℝ) ^ d * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (4 * (2 * (4 * Real.exp 1 * (K : ℝ)) ^ 2)))
        ((1 / (8 * Real.exp 1 * (K : ℝ))) * η / 2)) := by
  classical
  have : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  obtain ⟨N, hN, hcover, hcard⟩ := exists_euclidean_quarter_net d
  let E : EuclideanSpace ℝ (Fin d) → Set Ω := fun a ↦
    {ω | η ≤
      |⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredEmpiricalCovariance μ X ω) a, a⟫_ℝ|}
  have hsub : {ω | 2 * η < ‖centeredEmpiricalCovariance μ X ω‖} ⊆ ⋃ a ∈ N, E a := by
    intro ω hω
    by_contra hωE
    have hquad : ∀ a ∈ N,
        |⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredEmpiricalCovariance μ X ω) a, a⟫_ℝ| ≤ η := by
      intro a ha
      have hnot : ¬ η ≤
          |⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredEmpiricalCovariance μ X ω) a, a⟫_ℝ| := by
        intro he
        apply hωE
        simp only [Set.mem_iUnion]
        exact ⟨a, ha, he⟩
      exact (lt_of_not_ge hnot).le
    have hbound := symmetric_opNorm_le_of_quarter_net
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredEmpiricalCovariance μ X ω))
      (centeredEmpiricalCovariance_symmetric X ω) N hN hcover η hη.le hquad
    rw [Matrix.l2_opNorm_toEuclideanCLM] at hbound
    exact (not_lt_of_ge hbound) hω
  calc
    μ.real {ω | 2 * η < ‖centeredEmpiricalCovariance μ X ω‖}
        ≤ μ.real (⋃ a ∈ N, E a) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ a ∈ N, μ.real (E a) := measureReal_biUnion_finset_le N _
    _ ≤ ∑ _a ∈ N, 2 * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (4 * (2 * (4 * Real.exp 1 * (K : ℝ)) ^ 2)))
        ((1 / (8 * Real.exp 1 * (K : ℝ))) * η / 2)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact independent_covariance_quadratic_tail hn X hIndep hMeas K hK hMGF a (hN a ha) η hη
    _ = 2 * (N.card : ℝ) * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (4 * (2 * (4 * Real.exp 1 * (K : ℝ)) ^ 2)))
        ((1 / (8 * Real.exp 1 * (K : ℝ))) * η / 2)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by gcongr

theorem independent_empirical_covariance_operator_tail_explicit
    (hn : 0 < n) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (K : ℝ≥0) (hK : 0 < K)
    (hMGF : ∀ i (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      HasSubgaussianMGF (fun ω ↦ ⟪X i ω, a⟫_ℝ) K μ)
    (η : ℝ) (hη : 0 < η) :
    μ.real {ω | 2 * η < ‖centeredEmpiricalCovariance μ X ω‖} ≤
      2 * (9 : ℝ) ^ d * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (128 * Real.exp 1 ^ 2 * (K : ℝ) ^ 2))
        (η / (16 * Real.exp 1 * (K : ℝ)))) := by
  have h := independent_empirical_covariance_operator_tail hn X hIndep hMeas K hK hMGF η hη
  have hden : 4 * (2 * (4 * Real.exp 1 * (K : ℝ)) ^ 2) =
      128 * Real.exp 1 ^ 2 * (K : ℝ) ^ 2 := by ring
  have hlin : (1 / (8 * Real.exp 1 * (K : ℝ))) * η / 2 =
      η / (16 * Real.exp 1 * (K : ℝ)) := by ring
  simpa only [hden, hlin] using h

end SKConstants.Concentration

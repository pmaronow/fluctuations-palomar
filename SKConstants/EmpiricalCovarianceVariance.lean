module

public import SKConstants.EmpiricalCovariance
public import SKConstants.SubGaussianSquaresVariance

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace NNReal Matrix.Norms.L2Operator

namespace SKConstants.Concentration

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n d : ℕ}

theorem independent_covariance_quadratic_variance_tail
    (hn : 0 < n) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (K : ℝ≥0) (hK : 0 < K)
    (hMGF : ∀ i (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      HasSubgaussianMGF (fun ω ↦ ⟪X i ω, a⟫_ℝ) K μ)
    (s : ℝ) (hs : 0 < s)
    (hSecond : ∀ i (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      (∫ ω, ⟪X i ω, a⟫_ℝ ^ 2 ∂μ) ≤ s)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    μ.real {ω | η ≤
      |⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (centeredEmpiricalCovariance μ X ω) a, a⟫_ℝ|} ≤
      2 * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (64 * s * squareVarianceScale (K : ℝ) s))
        (η / (8 * squareVarianceScale (K : ℝ) s))) := by
  have : IsProbabilityMeasure μ := hIndep.isProbabilityMeasure
  have hB : 0 < squareVarianceScale (K : ℝ) s := squareVarianceScale_pos hs
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
      (16 * s * squareVarianceScale (K : ℝ) s)
      (1 / (4 * squareVarianceScale (K : ℝ) s)) := by
    intro i
    apply subGaussian_centered_square_logarithmic_variance_localMGF μ _ _ K hK
      (hMGF i a ha) s hs (hSecond i a ha)
    have hXi := hMeas i
    fun_prop
  have hInt : ∀ i j k, Integrable (fun ω ↦ X i ω j * X i ω k) μ :=
    fun i ↦ subGaussian_row_coordinate_integrable_product (X i) K hK (hMGF i)
  simp_rw [centeredEmpiricalCovariance_quadratic X hInt]
  have h := independent_average_bernstein hn hYIndep hYMeas hRows
    (by positivity) (by positivity) hη
  have hden : 4 * (16 * s * squareVarianceScale (K : ℝ) s) =
      64 * s * squareVarianceScale (K : ℝ) s := by ring
  have hlin : (1 / (4 * squareVarianceScale (K : ℝ) s)) * η / 2 =
      η / (8 * squareVarianceScale (K : ℝ) s) := by ring
  simpa only [hden, hlin] using h

theorem independent_empirical_covariance_operator_variance_tail
    (hn : 0 < n) (X : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hIndep : iIndepFun X μ) (hMeas : ∀ i, Measurable (X i))
    (K : ℝ≥0) (hK : 0 < K)
    (hMGF : ∀ i (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      HasSubgaussianMGF (fun ω ↦ ⟪X i ω, a⟫_ℝ) K μ)
    (s : ℝ) (hs : 0 < s)
    (hSecond : ∀ i (a : EuclideanSpace ℝ (Fin d)), ‖a‖ ≤ 1 →
      (∫ ω, ⟪X i ω, a⟫_ℝ ^ 2 ∂μ) ≤ s)
    (η : ℝ) (hη : 0 < η) :
    μ.real {ω | 2 * η < ‖centeredEmpiricalCovariance μ X ω‖} ≤
      2 * (9 : ℝ) ^ d * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (64 * s * squareVarianceScale (K : ℝ) s))
        (η / (8 * squareVarianceScale (K : ℝ) s))) := by
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
        (η ^ 2 / (64 * s * squareVarianceScale (K : ℝ) s))
        (η / (8 * squareVarianceScale (K : ℝ) s))) := by
      apply Finset.sum_le_sum
      intro a ha
      exact independent_covariance_quadratic_variance_tail hn X hIndep hMeas K hK hMGF
        s hs hSecond a (hN a ha) η hη
    _ = 2 * (N.card : ℝ) * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (64 * s * squareVarianceScale (K : ℝ) s))
        (η / (8 * squareVarianceScale (K : ℝ) s))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by gcongr

end SKConstants.Concentration

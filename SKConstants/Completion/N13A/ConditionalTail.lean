module

public import SKConstants.Completion.N13A.Statements

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SKConstants.Completion.N13A

theorem restricted_gaussian_upper_tail {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (G : Set A) (hG : MeasurableSet G) (Z : A → ℝ)
    (hZ : AEMeasurable Z (μ.restrict G)) (V u : ℝ) (hV : 0 < V) (hu : 0 < u)
    (hmgf : ∀ θ : ℝ,
      (∫⁻ y in G, ENNReal.ofReal (Real.exp (θ * Z y)) ∂μ) ≤
        ENNReal.ofReal (Real.exp (θ^2 * V / 2))) :
    μ {y | y ∈ G ∧ u ≤ Z y} ≤ ENNReal.ofReal (Real.exp (-u^2 / (2*V))) := by
  let θ := u / V
  have hθ : 0 < θ := div_pos hu hV
  have hm := meas_ge_le_lintegral_div
    ((hZ.const_mul θ).exp.ennreal_ofReal)
    (ε := ENNReal.ofReal (Real.exp (θ*u)))
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
  have hsub : {y | u ≤ Z y} ⊆
      {y | ENNReal.ofReal (Real.exp (θ*u)) ≤ ENNReal.ofReal (Real.exp (θ*Z y))} := by
    intro y hy
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hy hθ.le))
  have hrestrict : μ {y | y ∈ G ∧ u ≤ Z y} = (μ.restrict G) {y | u ≤ Z y} := by
    rw [Measure.restrict_apply' hG]
    congr 1
    ext y
    simp [and_comm]
  rw [hrestrict]
  calc
    _ ≤ (μ.restrict G)
        {y | ENNReal.ofReal (Real.exp (θ*u)) ≤ ENNReal.ofReal (Real.exp (θ*Z y))} :=
      measure_mono hsub
    _ ≤ _ := hm
    _ ≤ ENNReal.ofReal (Real.exp (θ^2*V/2)) /
        ENNReal.ofReal (Real.exp (θ*u)) := by gcongr; exact hmgf θ
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
      congr 2
      dsimp [θ]
      field_simp
      ring

theorem restricted_gaussian_two_sided_tail {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (G : Set A) (hG : MeasurableSet G) (Z : A → ℝ)
    (hZ : AEMeasurable Z (μ.restrict G)) (V u : ℝ) (hV : 0 < V) (hu : 0 < u)
    (hmgf : ∀ θ : ℝ,
      (∫⁻ y in G, ENNReal.ofReal (Real.exp (θ * Z y)) ∂μ) ≤
        ENNReal.ofReal (Real.exp (θ^2 * V / 2))) :
    μ {y | y ∈ G ∧ u < |Z y|} ≤ ENNReal.ofReal (2 * Real.exp (-u^2 / (2*V))) := by
  have hp := restricted_gaussian_upper_tail μ G hG Z hZ V u hV hu hmgf
  have hn := restricted_gaussian_upper_tail μ G hG (fun y => -Z y) hZ.neg V u hV hu
    (fun θ => by simpa only [mul_neg, neg_mul, neg_sq] using hmgf (-θ))
  calc
    _ ≤ μ ({y | y ∈ G ∧ u ≤ Z y} ∪ {y | y ∈ G ∧ u ≤ -Z y}) := by
      apply measure_mono
      intro y hy
      rcases lt_abs.mp hy.2 with h | h
      · exact Or.inl ⟨hy.1, h.le⟩
      · exact Or.inr ⟨hy.1, by linarith⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-u^2 / (2*V))) +
        ENNReal.ofReal (Real.exp (-u^2 / (2*V))) := add_le_add hp hn
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

theorem conditional_mgf_bound_on_row_event {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure A) [IsProbabilityMeasure μ]
    (rows : A → B) (hrows : Measurable rows) (S : Set B) (hS : MeasurableSet S)
    (Z : A → ℝ) (variance : B → ℝ) (V : ℝ)
    (hvar : ∀ y, rows y ∈ S → variance (rows y) ≤ V)
    (hlaw : ∀ θ : ℝ,
      (∫⁻ y in rows ⁻¹' S, ENNReal.ofReal (Real.exp (θ*Z y)) ∂μ) =
        ∫⁻ y in rows ⁻¹' S, ENNReal.ofReal (Real.exp (θ^2*variance (rows y)/2)) ∂μ) :
    ∀ θ : ℝ,
      (∫⁻ y in rows ⁻¹' S, ENNReal.ofReal (Real.exp (θ*Z y)) ∂μ) ≤
        ENNReal.ofReal (Real.exp (θ^2*V/2)) := by
  intro θ
  rw [hlaw θ]
  calc
    _ ≤ ∫⁻ _y in rows ⁻¹' S, ENNReal.ofReal (Real.exp (θ^2*V/2)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hrows hS)] with y hy
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hvar y hy) (sq_nonneg θ)) (by norm_num)
    _ ≤ _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
      exact mul_le_of_le_one_right (by positivity) prob_le_one

end SKConstants.Completion.N13A

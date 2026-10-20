module

public import SKConstants.Completion.LW.FiniteScalarMGF
public import SKConstants.Completion.LW.ProductMGFProducer
public import Mathlib.Analysis.Normed.Module.Normalize

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW
open SKConstantsOAI.ZeroTemperatureSK Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem normalized_direction_norm_le {k : ℕ} (a : EuclideanSpace ℝ (Fin k)) :
    ‖NormedSpace.normalize a‖ ≤ 1 := by
  by_cases ha : a=0
  · simp [ha]
  · exact (NormedSpace.norm_normalize ha).le

theorem projection_hasSubgaussian_of_unit {μ : Measure Ω} {k : ℕ}
    (T : Ω → EuclideanSpace ℝ (Fin k)) {R : ℝ} (hR : 0 ≤ R)
    (hT : ∀ a : EuclideanSpace ℝ (Fin k), ‖a‖ ≤ 1 →
      HasSubgaussianMGF (fun ω => ⟪T ω,a⟫_ℝ) (Real.toNNReal R) μ)
    (a : EuclideanSpace ℝ (Fin k)) :
    HasSubgaussianMGF (fun ω => ⟪T ω,a⟫_ℝ) (Real.toNNReal (R*‖a‖^2)) μ := by
  have H := (hT (NormedSpace.normalize a) (normalized_direction_norm_le a)).const_mul ‖a‖
  convert H using 1
  · ext ω
    rw [← real_inner_smul_right, NormedSpace.norm_smul_normalize]
  · apply NNReal.eq
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ hR,
      Real.coe_toNNReal _ (mul_nonneg hR (sq_nonneg ‖a‖))]
    change R*‖a‖^2 = ‖a‖^2*R
    ring

theorem projection_crossMoment_of_isometry {μ : Measure Ω} {k : ℕ}
    (T : Ω → EuclideanSpace ℝ (Fin k))
    (hLp : ∀ a : EuclideanSpace ℝ (Fin k), MemLp (fun ω => ⟪T ω,a⟫_ℝ) 2 μ)
    (hIso : ∀ a : EuclideanSpace ℝ (Fin k), (∫ ω, ⟪T ω,a⟫_ℝ^2 ∂μ) = ‖a‖^2)
    (a b : EuclideanSpace ℝ (Fin k)) :
    (∫ ω, ⟪T ω,a⟫_ℝ * ⟪T ω,b⟫_ℝ ∂μ) = ⟪a,b⟫_ℝ := by
  have H := hIso (a+b)
  have he (ω : Ω) : ⟪T ω,a+b⟫_ℝ^2 =
      ⟪T ω,a⟫_ℝ^2+2*(⟪T ω,a⟫_ℝ * ⟪T ω,b⟫_ℝ)+⟪T ω,b⟫_ℝ^2 := by
    rw [inner_add_right]; ring
  simp_rw [he] at H
  have hiab : Integrable (fun ω => ⟪T ω,a⟫_ℝ * ⟪T ω,b⟫_ℝ) μ :=
    (hLp a).integrable_mul (hLp b)
  have h1 := integral_add ((hLp a).integrable_sq.add (hiab.const_mul 2)) (hLp b).integrable_sq
  have h2 := integral_add (hLp a).integrable_sq (hiab.const_mul 2)
  simp only [Pi.add_apply] at h1 h2
  rw [h1, h2, integral_const_mul, hIso a, hIso b, norm_add_sq_real] at H
  linarith

theorem posteriorRow_projection_duration_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0)
    (a : EuclideanSpace ℝ (Fin k)) :
    HasSubgaussianMGF (fun u => ⟪posteriorRow W β t k u,a⟫_ℝ)
      (Real.toNNReal (∑ j : Fin k,
        (a j / posteriorWeight W β t k j)^2*previousDuration t j))
      (linkedScalarLaw W Z β V) := by
  let s (j : Fin k) := posteriorWeight W β t k j
  let c (j : ℕ) : ℝ := if hj : j<k then a ⟨j,hj⟩ / s ⟨j,hj⟩ else 0
  have he (w : Ω) : ⟪actualParisiNormalizedPosteriorRow W β t k w,a⟫_ℝ =
      weightedIncrement W β t c k w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, star_trivial, actualParisiNormalizedPosteriorRow,
      WithLp.ofLp_toLp, weightedIncrement, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [c, Finset.mem_range.mp hj, dite_true, s, posteriorWeight]
    ring
  have hp : weightedDurationProxy t c k = Real.toNNReal
      (∑ j : Fin k, (a j / posteriorWeight W β t k j)^2*previousDuration t j) := by
    have hep : (weightedDurationProxy t c k : ℝ) =
        ∑ j : Fin k, (a j / posteriorWeight W β t k j)^2*previousDuration t j := by
      rw [weightedDurationProxy_coe t ht.monotone, Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [c, Finset.mem_range.mp hj, dite_true, s]
    rw [← hep, Real.toNNReal_coe]
  have H := weightedIncrement_hasSubgaussianMGF W β hβ t ht.monotone c k
  rw [hp] at H
  have H' := H.congr (ae_of_all _ (fun w => (he w).symm))
  apply HasSubgaussianMGF.of_map
    (X := fun w => ⟪actualParisiNormalizedPosteriorRow W β t k w,a⟫_ℝ)
    (actualParisiFullQuerySpinLaw_path_hasLaw W Z β V).aemeasurable
  rw [(actualParisiFullQuerySpinLaw_path_hasLaw W Z β V).map_eq]
  exact H'

theorem posteriorRow_weighted_block_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0)
    (w : EuclideanSpace ℝ (Fin k)) {B : ℝ}
    (hw : ∀ j, |w j / posteriorWeight W β t k j| ≤ B) (J : Finset (Fin k)) :
    HasSubgaussianMGF (fun u => ⟪posteriorRow W β t k u,coordinateProjection J w⟫_ℝ)
      (Real.toNNReal (B^2*∑ j ∈ J, previousDuration t j)) (linkedScalarLaw W Z β V) := by
  apply hasSubgaussianMGF_of_proxy_le
    (posteriorRow_projection_duration_hasSubgaussianMGF W Z β hβ t ht k V _)
  apply Real.toNNReal_mono
  rw [Finset.mul_sum]
  have he : (∑ j : Fin k,
      (coordinateProjection J w j / posteriorWeight W β t k j)^2*previousDuration t j) =
      ∑ j ∈ J, (w j / posteriorWeight W β t k j)^2*previousDuration t j := by
    simp only [coordinateProjection_apply, ite_div, zero_div, ite_pow,
      zero_pow (by norm_num : 2 ≠ 0), ite_mul, zero_mul]
    simp
  rw [he]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right
    (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw j) 2)
  exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht.monotone (Nat.le_succ _)))

end SKConstants.Completion.LW

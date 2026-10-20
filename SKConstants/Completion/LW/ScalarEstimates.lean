module

public import SKConstants.Completion.LW.LinkedScalarRows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def curvatureCellEnergy (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (j : ℕ) (w : Ω) : ℝ :=
  ∫ v in (t j : ℝ)..(t (j+1) : ℝ),
    (actualParisiFullCurvature β v (actualParisiFullScalarProcess W β v.toNNReal w))^2

theorem curvatureCellEnergy_nonneg (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (j : ℕ) (w : Ω) :
    0 ≤ curvatureCellEnergy W β t j w :=
  intervalIntegral.integral_nonneg (NNReal.coe_le_coe.mpr (ht (Nat.le_succ _)))
    (fun _ _ => sq_nonneg _)

theorem curvatureCellEnergy_le_duration (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (j : ℕ) (w : Ω) :
    curvatureCellEnergy W β t j w ≤ previousDuration t j :=
  actual_curvature_cell_integral_le W β w (NNReal.coe_le_coe.mpr (ht (Nat.le_succ _)))

theorem actual_normalized_curvature_budget
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0) (hV : t k ≤ V)
    (α : EuclideanSpace ℝ (Fin k)) (w : Ω) :
    (∑ j : Fin k, (α j / posteriorWeight W β t k j)^2 * curvatureCellEnergy W β t j w) ≤
      (actualParisiPosteriorRowMGFProxy W β V : ℝ) * ‖α‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply normalized_cell_bracket_le
    (fun j : Fin k => α j) (fun j => posteriorWeight W β t k j)
    (fun j => previousDuration t j) (fun j => curvatureCellEnergy W β t j w)
    (NNReal.coe_pos.mpr (actualParisiPosteriorRowMGFProxy_pos W β V))
  · intro j
    exact NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ
      (t j) (t (j+1)) (ht (Nat.lt_succ_self _)))
  · intro j
    exact curvatureCellEnergy_le_duration W β t ht.monotone j w
  · intro j
    have H := actualParisiPosteriorIntervalScale_duration_budget W β hβ
      (t j) (t (j+1)) V (ht (Nat.lt_succ_self _)) ((ht.monotone (by omega)).trans hV)
    have HR := NNReal.coe_le_coe.mpr H
    rw [NNReal.coe_sub (ht.monotone (Nat.le_succ _)), NNReal.coe_mul, NNReal.coe_pow] at HR
    apply (div_le_iff₀ (NNReal.coe_pos.mpr (actualParisiPosteriorRowMGFProxy_pos W β V))).mpr
    simpa only [previousDuration, posteriorWeight, mul_comm] using HR

theorem actual_weighted_curvature_budget
    (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (r : ℕ) (I : DyadicCore.Interval r) (wgt : Fin (2^r) → ℝ)
    {B : ℝ} (hw : ∀ j ∈ dyadicIntervalSets r I, |wgt j| ≤ B) (w : Ω) :
    (∑ j ∈ dyadicIntervalSets r I, wgt j ^ 2 * curvatureCellEnergy W β t j w) ≤
      B^2 * nodeDuration r (fun j => previousDuration t j) I := by
  unfold nodeDuration
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul
  · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw j hj) 2
  · exact curvatureCellEnergy_le_duration W β t ht j w
  · exact curvatureCellEnergy_nonneg W β t ht j w
  · exact sq_nonneg _

theorem posteriorRow_secondMoment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0)
    (α : EuclideanSpace ℝ (Fin k)) :
    (∫ u, ⟪posteriorRow W β t k u,α⟫_ℝ^2 ∂linkedScalarLaw W Z β V) = ‖α‖^2 := by
  have hm : Measurable (fun w => ⟪actualParisiNormalizedPosteriorRow W β t k w,α⟫_ℝ^2) := by
    have H := measurable_actualParisiNormalizedPosteriorRow W β t k
    fun_prop
  exact ((actualParisiFullQuerySpinLaw_path_hasLaw W Z β V).integral_comp
    hm.aestronglyMeasurable).trans (actualParisiNormalizedPosteriorRow_secondMoment W β hβ t ht k α)

theorem queryRow_secondMoment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0)
    (α : EuclideanSpace ℝ (Fin k)) :
    (∫ u, ⟪queryRow W Z β hβ t k u,α⟫_ℝ^2 ∂linkedScalarLaw W Z β V) = ‖α‖^2 := by
  letI := W.isProbability
  letI := Z.isProbability
  let Q := actualParisiQueryBrownianSystem W Z β hβ
  letI := Q.isProbability
  have hm : Measurable (fun u =>
      ⟪scalarNormalizedBrownianRow (d := k) Q.B (fun j => t (j+1)) u,α⟫_ℝ^2) := by
    have H := measurable_scalarNormalizedBrownianRow (d := k) Q.B Q.measurable (fun j => t (j+1))
    fun_prop
  exact ((linkedScalarLaw_drivers_hasLaw W Z β V).integral_comp hm.aestronglyMeasurable).trans
    (scalarNormalizedBrownianRow_linearForm_secondMoment Q.law Q.B
      Q.brownian.toIsPreBrownianReal (fun j => t (j+1))
      (fun _ _ hij => ht (Nat.add_lt_add_right hij 1)) α)

theorem queryRow_unit_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0)
    (α : EuclideanSpace ℝ (Fin k)) (hα : ‖α‖ ≤ 1) :
    HasSubgaussianMGF (fun u => ⟪queryRow W Z β hβ t k u,α⟫_ℝ) 1
      (linkedScalarLaw W Z β V) := by
  letI := W.isProbability
  letI := Z.isProbability
  letI := (actualParisiQueryBrownianSystem W Z β hβ).isProbability
  apply HasSubgaussianMGF.of_map
    (X := fun u => ⟪scalarNormalizedBrownianRow
      (actualParisiQueryBrownianSystem W Z β hβ).B (fun j => t (j+1)) u,α⟫_ℝ)
    (linkedScalarLaw_drivers_hasLaw W Z β V).aemeasurable
  rw [(linkedScalarLaw_drivers_hasLaw W Z β V).map_eq]
  exact scalarNormalizedBrownianRow_unit_hasSubgaussianMGF _ _
    (actualParisiQueryBrownianSystem W Z β hβ).brownian.toIsPreBrownianReal
    (fun j => t (j+1)) (fun _ _ hij => ht (Nat.add_lt_add_right hij 1)) α hα

theorem posteriorWeight_node_norm_sq_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (r : ℕ) (I : DyadicCore.Interval r) :
    ‖coordinateProjection (dyadicIntervalSets r I) (posteriorWeight W β t (2^r))‖^2 ≤
      nodeDuration r (fun j => previousDuration t j) I := by
  rw [coordinateProjection_norm_sq]
  apply Finset.sum_le_sum
  intro j _
  rw [posteriorWeight_eq_integral W β hβ t ht, LQ.posteriorScale]
  have hn : 0 ≤ ∫ v in (t j : ℝ)..(t (j+1) : ℝ),
      actualParisiFullSusceptibilitySquareExpected W β v :=
    intervalIntegral.integral_nonneg (NNReal.coe_le_coe.mpr (ht.monotone (Nat.le_succ _)))
      (fun v _ => (actualParisiFullSusceptibilitySquareExpected_bounds W β v).1)
  rw [Real.sq_sqrt hn]
  have H := intervalIntegral.integral_mono_on
    (NNReal.coe_le_coe.mpr (ht.monotone (Nat.le_succ _)))
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (t j : ℝ) (t (j+1)))
    (fun v _ => (actualParisiFullSusceptibilitySquareExpected_bounds W β v).2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one, previousDuration] using H

end SKConstants.Completion.LW

module
public import SKConstants.ParisiAverageLimit
public import SKConstants.ParisiCDFOverlapDerivative
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFSquareSusceptibility

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem scalarCDFAverage_eq_actualBrownian_expectation
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 0 < β) (α : StieltjesFunction ℝ)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) {g : ℝ → ℝ} (hg : BoundedSmooth g) :
    scalarCDFAverage β α 0 (Real.toNNReal r)
      (scalarCDFValue β α r (Real.toNNReal (1-r))) g 0 =
    ∫ w, g (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*r)) w) ∂W.law := by
  let := W.isProbability
  let v := Real.toNNReal (β^2*r)
  let B : ℝ≥0 := hg.bound.choose
  have hv : (v:ℝ) < β^2 := by
    rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) hr.1)]
    exact (mul_lt_mul_of_pos_left hr.2 (sq_pos_of_pos hβ)).trans_eq (mul_one _)
  have hmeas n : AEStronglyMeasurable
      (fun w => g ((parisiGridFeedback β α n).solution W.driver v w)) W.law :=
    (hg.smooth.continuous.measurable.comp ((parisiGridFeedback β α n).solution_measurable W v)).aestronglyMeasurable
  have hbound n : ∀ᵐ w ∂W.law, ‖g ((parisiGridFeedback β α n).solution W.driver v w)‖ ≤ (B:ℝ) :=
    Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs] using hg.bound.choose_spec _)
  have hpoint : ∀ᵐ w ∂W.law, Tendsto
      (fun n => g ((parisiGridFeedback β α n).solution W.driver v w)) atTop
      (𝓝 (g (finiteTemperatureCDFProcess W β α ha h1 v w))) := by
    filter_upwards [] with w
    exact (hg.smooth.continuous.tendsto _).comp
      (parisiGridFeedback_solution_tendsto W β hβ.ne' α ha h1 v hv w)
  have hi := tendsto_integral_of_dominated_convergence (fun _ : Ω => (B:ℝ)) hmeas
    (integrable_const _) hbound hpoint
  have heq n := finiteFeedback_grid_expectation_eq_scalarCDFAverage W β hβ α α.mono ha
    (parisiGridMesh n) (parisiGridMesh_pos n) (n+1) (parisiGridMesh_horizon n) hr hg
  have hi' : Tendsto (fun n => scalarCDFAverage β (gridCDF α (parisiGridMesh n)) 0 (Real.toNNReal r)
      (scalarCDFValue β (gridCDF α (parisiGridMesh n)) r (Real.toNNReal (1-r))) g 0) atTop
      (𝓝 (∫ w, g (finiteTemperatureCDFProcess W β α ha h1 v w) ∂W.law)) := by
    apply hi.congr'
    exact Eventually.of_forall (fun n => heq n)
  exact tendsto_nhds_unique (parisiGridCDF_average_tendsto β α α.mono ha hr hg) hi'

lemma scalarCDFGradient_boundedSmooth (β : ℝ) (hβ : β ≠ 0) (α : StieltjesFunction ℝ)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    BoundedSmooth (scalarCDFGradient β α r (Real.toNNReal (1-r))) := by
  have H := (scalarCDFValue_regularDatum β α ha hβ hr.1 hr.2).deriv_bounded
  have ht : Real.toNNReal (1-r) ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr (by simp only [NNReal.coe_one]; linarith [hr.1])
  rw [←scalarCDF_gradient_eq_deriv ha α.mono β r _ ht] at H
  exact H

lemma scalarCDFHessian_boundedSmooth (β : ℝ) (hβ : β ≠ 0) (α : StieltjesFunction ℝ)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    BoundedSmooth (scalarCDFHessian β α r (Real.toNNReal (1-r))) := by
  have H := (scalarCDFGradient_boundedSmooth β hβ α ha hr).deriv
  have ht : Real.toNNReal (1-r) ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr (by simp only [NNReal.coe_one]; linarith [hr.1])
  have he : deriv (scalarCDFGradient β α r (Real.toNNReal (1-r))) = scalarCDFHessian β α r (Real.toNNReal (1-r)) :=
    funext (fun x => (scalarCDFGradient_hasDerivAt β ha α.mono r _ ht x).deriv)
  rw [he] at H
  exact H

theorem scalarCDFOverlap_eq_actualBrownian
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 0 < β) (α : StieltjesFunction ℝ)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    scalarCDFOverlap β α r = brownianCDFOverlap W β α ha h1 r := by
  have H := scalarCDFGradient_boundedSmooth β hβ.ne' α ha hr
  have Hsq : BoundedSmooth (fun x => (scalarCDFGradient β α r (Real.toNNReal (1-r)) x)^2) := by
    simpa only [pow_two] using H.mul H
  exact scalarCDFAverage_eq_actualBrownian_expectation W β hβ α ha h1 hr Hsq

theorem scalarCDFSusceptibilitySquareAverage_eq_actualBrownian
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 0 < β) (α : StieltjesFunction ℝ)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) :
    scalarCDFSusceptibilitySquareAverage β α r = brownianCDFSusceptibilitySquare W β α ha h1 r := by
  have H := scalarCDFHessian_boundedSmooth β hβ.ne' α ha hr
  have Hsq : BoundedSmooth (fun x => (scalarCDFHessian β α r (Real.toNNReal (1-r)) x)^2) := by
    simpa only [pow_two] using H.mul H
  exact scalarCDFAverage_eq_actualBrownian_expectation W β hβ α ha h1 hr Hsq

theorem scalarCDFOverlap_hasDerivAt_actual
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 0 < β) (α : StieltjesFunction ℝ)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (scalarCDFOverlap β α)
      (β^2*scalarCDFSusceptibilitySquareAverage β α r) r := by
  have H := brownianCDFOverlap_hasDerivAt W β α ha h1 hβ.ne' hr
  rw [←scalarCDFSusceptibilitySquareAverage_eq_actualBrownian W β hβ α ha h1 ⟨hr.1.le,hr.2⟩] at H
  apply H.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hr] with q hq
  exact scalarCDFOverlap_eq_actualBrownian W β hβ α ha h1 ⟨hq.1.le,hq.2⟩

end SKConstants.ParisiFullSupport

module

public import SKConstants.GaussianIntegralL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def gaussianCoefficientDifference (H G : GaussianPredictableCoefficient) :
    GaussianPredictableCoefficient := fun k z => H k z - G k z

theorem adaptedGaussianSum_coefficient_difference (H G : GaussianPredictableCoefficient)
    (n : ℕ) (z : GaussianHistory n) :
    adaptedGaussianSum (gaussianCoefficientDifference H G) n z =
      adaptedGaussianSum H n z - adaptedGaussianSum G n z := by
  induction n with
  | zero => simp [adaptedGaussianSum]
  | succ n ih =>
    simp only [adaptedGaussianSum, gaussianCoefficientDifference, ih]
    ring

theorem integrable_gaussianCoefficientDifference_sq (dt : ℕ → ℝ≥0)
    (H G : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (hG : ∀ k, Measurable (G k))
    (hHsq : ∀ k, Integrable (fun z => (H k z) ^ 2) (gaussianHistoryLaw dt k))
    (hGsq : ∀ k, Integrable (fun z => (G k z) ^ 2) (gaussianHistoryLaw dt k)) (k : ℕ) :
    Integrable (fun z => (gaussianCoefficientDifference H G k z) ^ 2)
      (gaussianHistoryLaw dt k) :=
  (((memLp_two_iff_integrable_sq (hH k).aestronglyMeasurable).2 (hHsq k)).sub
    ((memLp_two_iff_integrable_sq (hG k).aestronglyMeasurable).2 (hGsq k))).integrable_sq

theorem brownianAdaptedSum_difference_L2_isometry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H G : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k)) (hG : ∀ k, Measurable (G k))
    (hHsq : ∀ k, Integrable (fun z => (H k z) ^ 2)
      (gaussianHistoryLaw (brownianMeshVariance t) k))
    (hGsq : ∀ k, Integrable (fun z => (G k z) ^ 2)
      (gaussianHistoryLaw (brownianMeshVariance t) k)) (n : ℕ) :
    (∫ ω, (brownianAdaptedSum B t H n ω - brownianAdaptedSum B t G n ω) ^ 2 ∂P) =
      ∫ ω, brownianAdaptedQuadraticVariation B t (gaussianCoefficientDifference H G) n ω ∂P := by
  have hs := brownianAdaptedSum_L2_isometry hB t ht (gaussianCoefficientDifference H G)
    (fun k => (hH k).sub (hG k))
    (integrable_gaussianCoefficientDifference_sq (brownianMeshVariance t) H G hH hG hHsq hGsq) n
  simpa only [brownianAdaptedSum, adaptedGaussianSum_coefficient_difference] using hs

theorem memLp_brownianAdaptedSum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun z => (H k z) ^ 2)
      (gaussianHistoryLaw (brownianMeshVariance t) k)) (n : ℕ) :
    MemLp (brownianAdaptedSum B t H n) 2 P := by
  have hlaw := brownianGaussianHistory_hasLaw hB t ht n
  apply (memLp_two_iff_integrable_sq
    (((measurable_adaptedGaussianSum H hH n).comp_aemeasurable hlaw.aemeasurable).aestronglyMeasurable)).2
  exact hlaw.integrable_comp
    (integrable_adaptedGaussianSum_sq (brownianMeshVariance t) H hH hHsq n)

theorem norm_toLp_sub_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 P) (I : Lp ℝ 2 P) :
    ‖hX.toLp X - I‖ ^ 2 = ∫ ω, (X ω - I ω) ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hX.toLp X) I, hX.coeFn_toLp] with ω hsub hx
  rw [hsub, Pi.sub_apply, hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem norm_toLp_difference_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    ‖hX.toLp X - hY.toLp Y‖ ^ 2 = ∫ ω, (X ω - Y ω) ^ 2 ∂P := by
  rw [norm_toLp_sub_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hY.coeFn_toLp] with ω hω
  exact congrArg (fun r : ℝ => (X ω - r) ^ 2) hω

theorem brownianAdaptedSum_exists_L2_limit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ℕ → GaussianPredictableCoefficient)
    (hH : ∀ m k, Measurable (H m k))
    (hHsq : ∀ m k, Integrable (fun z => (H m k z) ^ 2)
      (gaussianHistoryLaw (brownianMeshVariance t) k)) (n : ℕ)
    (henergy : ∀ eps > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ l ≥ N,
      (∫ ω, brownianAdaptedQuadraticVariation B t
        (gaussianCoefficientDifference (H m) (H l)) n ω ∂P) < eps) :
    ∃ I : Ω → ℝ, MemLp I 2 P ∧
      Tendsto (fun m => ∫ ω, (brownianAdaptedSum B t (H m) n ω - I ω) ^ 2 ∂P)
        atTop (𝓝 0) := by
  let F : ℕ → Lp ℝ 2 P := fun m =>
    (memLp_brownianAdaptedSum hB t ht (H m) (hH m) (hHsq m) n).toLp
      (brownianAdaptedSum B t (H m) n)
  have hcauchy : CauchySeq F := by
    apply Metric.cauchySeq_iff.2
    intro eps heps
    obtain ⟨N, hN⟩ := henergy (eps ^ 2) (sq_pos_of_pos heps)
    refine ⟨N, fun m hm l hl => ?_⟩
    have hdist : dist (F m) (F l) ^ 2 =
        ∫ ω, brownianAdaptedQuadraticVariation B t
          (gaussianCoefficientDifference (H m) (H l)) n ω ∂P := by
      rw [dist_eq_norm]
      exact (norm_toLp_difference_sq_eq_integral
        (memLp_brownianAdaptedSum hB t ht (H m) (hH m) (hHsq m) n)
        (memLp_brownianAdaptedSum hB t ht (H l) (hH l) (hHsq l) n)).trans
        (brownianAdaptedSum_difference_L2_isometry hB t ht (H m) (H l)
          (hH m) (hH l) (hHsq m) (hHsq l) n)
    have hlt := hN m hm l hl
    rw [← hdist] at hlt
    nlinarith [show 0 ≤ dist (F m) (F l) from dist_nonneg]
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨I, Lp.memLp I, ?_⟩
  have hn : Tendsto (fun m => ‖F m - I‖ ^ 2) atTop (𝓝 0) := by
    simpa using ((hI.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => I) atTop (𝓝 I))).norm).pow 2
  have he : (fun m => ∫ ω, (brownianAdaptedSum B t (H m) n ω - I ω) ^ 2 ∂P) =
      fun m => ‖F m - I‖ ^ 2 := by
    funext m
    exact (norm_toLp_sub_sq_eq_integral
      (memLp_brownianAdaptedSum hB t ht (H m) (hH m) (hHsq m) n) I).symm
  rw [he]
  exact hn

end SKConstants

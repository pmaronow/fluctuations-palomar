module

public import SKProof.Port.OriginalQHighOnlyBridge
public import ComparisonNativeActualLocalScalarLimitData
public import ComparisonShiftedQuantileCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}

end ActualThetaZeroOverlapMinimum

structure ActualOriginalQLocalScalarLimitData
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} (hT : 0<T) (S : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) where
  omitted_small : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0)
  beta : boundedMassProfiles
  radiusLimit : boundedMassProfiles
  U : NonnegativeMassProfile
  V : NonnegativeMassProfile
  sigma : ℝ
  ambient_limit : Tendsto (fun n=>(M n).inheritedScalarMassProfileBare hT (htotal n)) atTop (𝓝 beta)
  radius_limit : Tendsto (fun n=>(M n).actualRadiusMassProfile) atTop (𝓝 radiusLimit)
  scalar_cdf_limit : ∀t : ℝ,Tendsto (fun n=>
    ((M n).inheritedScalarMassProfileBare hT (htotal n)).val ((S/T)*((M n).xs*t))/(M n).xs)
      atTop (𝓝 (U.mass t))
  radius_cdf_limit : ∀t : ℝ,Tendsto (fun n=>
    (M n).actualRadiusMassProfile.val ((M n).xs*t)/(M n).xs) atTop (𝓝 (V.mass t))
  limits : ∀R : ℝ,0<R→
    ContinuousOn (comparisonLocalScalarLimitSlope hT S beta U sigma) (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT S
      ((M n).inheritedScalarMassProfileBare hT (htotal n)) (M n).xs)
      (comparisonLocalScalarLimitSlope hT S beta U sigma) atTop (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfileBare hT (htotal n))) S (M n).xs)
      (comparisonLocalScalarLimitResponse hT S beta U sigma) atTop (Icc (0:ℝ) R)
  positive_coefficients : 0<S^3*(scalarTailSpatialJet hT beta 4 0 0)^2 ∧
    0<2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3
  coefficient_ratio : (S^3*(scalarTailSpatialJet hT beta 4 0 0)^2)/
    (2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3)=(S/T)*scalarInitialDensityConstant hT beta
  support_zero : ∀t : ℝ,0<t→(∀e : ℝ,0<e→V.mass (t-e)<V.mass (t+e))→
    comparisonLocalScalarLimitResponse hT S beta U sigma t=0

namespace ActualOriginalQLocalScalarLimitData
variable {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0<T} {dim : ℕ→ℕ}
  {M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
  {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T}

theorem radius_inverse_cdf_limit (d : ActualOriginalQLocalScalarLimitData hT S M htotal) :
    ∀t : ℝ,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*t)/(M n).xs)
      atTop (𝓝 (d.V.mass t)) := by
  intro t
  let A:=ActualThetaZeroOverlapMinimum.originalQShiftedInverseSequence M
  have Hdiff : Tendsto (fun n=>((M n).actualRadiusMassProfile.val ((M n).xs*t)-
      (M n).alpha.val.val ((M n).xs*t))/(M n).xs) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    apply squeeze_zero (fun _=>norm_nonneg _) _ d.omitted_small
    intro n
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (M n).hxs]
    exact div_le_div_of_nonneg_right
      (A.radius_cdf_error_le_omitted_mass (fun n=>(M n).data.hrbounds.1.le) n ((M n).xs*t)) (M n).hxs.le
  have H:=(d.radius_cdf_limit t).sub Hdiff
  simp only [sub_zero] at H
  convert H using 1
  ext n
  ring

theorem radius_negative_axis_zero (d : ActualOriginalQLocalScalarLimitData hT S M htotal) :
    ∀t : ℝ,t<0→d.V.mass t=0 :=
  (ActualThetaZeroOverlapMinimum.originalQShiftedInverseSequence M).rescaled_cdf_negative_axis_zero
    (fun n=>(M n).xs) d.V.mass (fun n=>(M n).hxs) (fun n=>(M n).data.hrbounds.1.le)
    d.omitted_small d.radius_inverse_cdf_limit

end ActualOriginalQLocalScalarLimitData

end OAI.SKFluctuations.LaplaceWindowFormalization

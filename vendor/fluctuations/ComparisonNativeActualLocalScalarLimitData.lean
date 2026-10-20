module

public import ComparisonLocalTemperatureScalarReadout
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open scoped Topology

namespace NativeOverlapMinimum

def actualRadiusMassProfile {m delta cl cu Az C0 Ct D Bclock : ℝ} {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) : boundedMassProfiles :=
  quantileMassProfile M.R (fun u _=>comparisonSweepQuantile_bounds
    M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha u)

end NativeOverlapMinimum

def comparisonLocalScalarLimitFlux {T : ℝ} (hT : 0<T) (S : ℝ)
    (beta : boundedMassProfiles) (U : NonnegativeMassProfile) (t : ℝ) : ℝ :=
  S^3*(scalarTailSpatialJet hT beta 4 0 0)^2*t-
    2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3*U.mass t

def comparisonLocalScalarLimitSlope {T : ℝ} (hT : 0<T) (S : ℝ)
    (beta : boundedMassProfiles) (U : NonnegativeMassProfile) (sigma t : ℝ) : ℝ :=
  sigma+∫s in 0..t,comparisonLocalScalarLimitFlux hT S beta U s

def comparisonLocalScalarLimitResponse {T : ℝ} (hT : 0<T) (S : ℝ)
    (beta : boundedMassProfiles) (U : NonnegativeMassProfile) (sigma t : ℝ) : ℝ :=
  ∫r in 0..t,comparisonLocalScalarLimitSlope hT S beta U sigma r

structure ActualInheritedLocalScalarLimitData
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} (hT : 0<T) (S : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) where
  beta : boundedMassProfiles
  radiusLimit : boundedMassProfiles
  U : NonnegativeMassProfile
  V : NonnegativeMassProfile
  sigma : ℝ
  ambient_limit : Tendsto (fun n=>(M n).inheritedScalarMassProfile hT (htotal n)) atTop (𝓝 beta)
  radius_limit : Tendsto (fun n=>(M n).actualRadiusMassProfile) atTop (𝓝 radiusLimit)
  scalar_cdf_limit : ∀t : ℝ,Tendsto (fun n=>
    ((M n).inheritedScalarMassProfile hT (htotal n)).val ((S/T)*((M n).xs*t))/(M n).xs)
      atTop (𝓝 (U.mass t))
  radius_cdf_limit : ∀t : ℝ,Tendsto (fun n=>
    (M n).actualRadiusMassProfile.val ((M n).xs*t)/(M n).xs) atTop (𝓝 (V.mass t))
  limits : ∀R : ℝ,0<R→
    ContinuousOn (comparisonLocalScalarLimitSlope hT S beta U sigma) (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT S
      ((M n).inheritedScalarMassProfile hT (htotal n)) (M n).xs)
      (comparisonLocalScalarLimitSlope hT S beta U sigma) atTop (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n))) S (M n).xs)
      (comparisonLocalScalarLimitResponse hT S beta U sigma) atTop (Icc (0:ℝ) R)
  positive_coefficients : 0<S^3*(scalarTailSpatialJet hT beta 4 0 0)^2 ∧
    0<2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3
  coefficient_ratio : (S^3*(scalarTailSpatialJet hT beta 4 0 0)^2)/
    (2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3)=(S/T)*scalarInitialDensityConstant hT beta
  support_zero : ∀t : ℝ,0<t→(∀e : ℝ,0<e→V.mass (t-e)<V.mass (t+e))→
    comparisonLocalScalarLimitResponse hT S beta U sigma t=0

end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeActualLocalScalarLimitData
public import ComparisonNativeActualProfileSequence
public import ActualComparisonScalarUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum

theorem actualRadiusMassProfile_eq_inverse
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    M.actualRadiusMassProfile=M.alpha.val :=
  comparisonSweepQuantile_massProfile_eq M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha

end NativeOverlapMinimum

namespace ActualInheritedLocalScalarLimitData

variable {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0<T}
  {dim : ℕ→ℕ}
  {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
  {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T}

theorem radius_inverse_profile_limit (d : ActualInheritedLocalScalarLimitData hT S M htotal) :
    Tendsto (fun n=>(M n).alpha.val) atTop (𝓝 d.radiusLimit) := by
  simpa only [NativeOverlapMinimum.actualRadiusMassProfile_eq_inverse] using d.radius_limit

theorem radius_inverse_cdf_limit (d : ActualInheritedLocalScalarLimitData hT S M htotal) :
    ∀t : ℝ,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*t)/(M n).xs)
      atTop (𝓝 (d.V.mass t)) := by
  intro t
  simpa only [NativeOverlapMinimum.actualRadiusMassProfile_eq_inverse] using d.radius_cdf_limit t

theorem radius_outer_growth (d : ActualInheritedLocalScalarLimitData hT S M htotal)
    (hAz : 0≤Az) (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ∀t : ℝ,Az≤t→cl*t≤d.V.mass t ∧ d.V.mass t≤cu*t :=
  NativeOverlapMinimum.actual_rescaled_cdf_outer_growth M (fun n=>(M n).xs)
    d.V.mass hAz (fun _=>le_rfl) hx d.radius_inverse_cdf_limit

theorem radius_negative_axis_zero (d : ActualInheritedLocalScalarLimitData hT S M htotal) :
    ∀t : ℝ,t<0→d.V.mass t=0 :=
  (NativeOverlapMinimum.actualInverseSequence M).rescaled_cdf_negative_axis_zero
    (fun n=>(M n).xs) d.V.mass (fun n=>(M n).hxs) (fun _=>le_rfl)
    (NativeOverlapMinimum.actualInverseSequence_omitted_small M (fun n=>(M n).xs))
    d.radius_inverse_cdf_limit

end ActualInheritedLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization

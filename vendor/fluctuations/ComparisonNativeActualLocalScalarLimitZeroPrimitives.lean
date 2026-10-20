module

public import ComparisonNativeProfileRigidity
public import ComparisonNativeActualLocalScalarLimitGlobalRigidity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open NativeOverlapMinimum
open scoped Topology
set_option maxHeartbeats 8000000

namespace ActualInheritedLocalScalarLimitData

variable {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0 < T}
  {dim : ℕ → ℕ}
  {M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
  {htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M n).h u+(M n).b u ≤ T}

theorem scalar_primitives_zero_of_linear_profiles
    (d : ActualInheritedLocalScalarLimitData hT S M htotal)
    (hUlinear : ∀t > 0,d.U.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t)
    (hVlinear : ∀t > 0,d.V.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) :
    d.sigma=0 ∧
      (∀t ≥ 0,comparisonLocalScalarLimitSlope hT S d.beta d.U d.sigma t=0) ∧
      (∀t ≥ 0,comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma t=0) := by
  let A := S^3*(scalarTailSpatialJet hT d.beta 4 0 0)^2
  let B := 2*S^2*(scalarTailSpatialJet hT d.beta 2 0 0)^3
  have hratio : A/B=(S/T)*scalarInitialDensityConstant hT d.beta := d.coefficient_ratio
  have hresponse : comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma=
      comparisonGlobalScalarResponse d.U.mass A B d.sigma := rfl
  have hzero : ∀t∈comparisonIncrementSupport d.V.mass,
      comparisonGlobalScalarResponse d.U.mass A B d.sigma t=0 := by
    intro t ht
    rw [←hresponse]
    by_cases htp : 0 < t
    · exact d.support_zero t htp ht
    · have ht0 : t=0 := le_antisymm (not_lt.mp htp)
        (comparison_increment_support_nonnegative d.radius_negative_axis_zero ht)
      simp only [ht0,comparisonLocalScalarLimitResponse,intervalIntegral.integral_same]
  have H := comparison_linear_scalar_primitives_zero (A:=A) (B:=B) d.V.monotone
    d.positive_coefficients.1 d.positive_coefficients.2
    (fun t ht => by simpa only [hratio] using hUlinear t ht)
    (fun t ht => by simpa only [hratio] using hVlinear t ht) hzero
  exact H

theorem compact_scalar_zero_limits_of_linear_profiles
    (d : ActualInheritedLocalScalarLimitData hT S M htotal)
    (hUlinear : ∀t > 0,d.U.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t)
    (hVlinear : ∀t > 0,d.V.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) :
    ∀R : ℝ,0 < R →
      TendstoUniformlyOn (fun n => comparisonLocalScalarSlope hT S
        ((M n).inheritedScalarMassProfile hT (htotal n)) (M n).xs)
        (fun _ => 0) atTop (Icc (0 : ℝ) R) ∧
      TendstoUniformlyOn (fun n => comparisonRescaledScalarResponse
        (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n)))
        S (M n).xs) (fun _ => 0) atTop (Icc (0 : ℝ) R) := by
  have Hzero := d.scalar_primitives_zero_of_linear_profiles hUlinear hVlinear
  intro R hR
  exact ⟨((d.limits R hR).2.1).congr_right (fun t ht => Hzero.2.1 t ht.1),
    ((d.limits R hR).2.2).congr_right (fun t ht => Hzero.2.2 t ht.1)⟩

end ActualInheritedLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization

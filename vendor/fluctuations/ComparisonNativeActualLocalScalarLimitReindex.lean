module

public import ComparisonNativeActualLocalScalarLimitData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology

namespace ActualInheritedLocalScalarLimitData

def comp {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T}
    (d : ActualInheritedLocalScalarLimitData hT S M htotal)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ActualInheritedLocalScalarLimitData hT S (fun n=>M (phi n)) (fun n=>htotal (phi n)) where
  beta := d.beta
  radiusLimit := d.radiusLimit
  U := d.U
  V := d.V
  sigma := d.sigma
  ambient_limit := d.ambient_limit.comp hphi.tendsto_atTop
  radius_limit := d.radius_limit.comp hphi.tendsto_atTop
  scalar_cdf_limit t := (d.scalar_cdf_limit t).comp hphi.tendsto_atTop
  radius_cdf_limit t := (d.radius_cdf_limit t).comp hphi.tendsto_atTop
  limits R hR := ⟨(d.limits R hR).1,
    (d.limits R hR).2.1.seq_tendstoUniformlyOn phi hphi.tendsto_atTop,
    (d.limits R hR).2.2.seq_tendstoUniformlyOn phi hphi.tendsto_atTop⟩
  positive_coefficients := d.positive_coefficients
  coefficient_ratio := d.coefficient_ratio
  support_zero := d.support_zero

end ActualInheritedLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization

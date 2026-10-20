module

public import ComparisonNativeActualLocalScalarLimitRadiusReadout
public import ComparisonNativeActualHighMassSharpScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology
set_option maxHeartbeats 5000000

namespace ActualInheritedLocalScalarLimitData
variable {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0 < T}
  {dim : ℕ→ℕ}
  {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
  {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T}

theorem original_radius_locally_uniform_of_linear_profile
    (d : ActualInheritedLocalScalarLimitData hT S M htotal)
    {kappa : ℝ} (hcl : 0 < cl) (hkappa : cl ≤ kappa)
    (hcanonical : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hlinear : ∀t > 0,d.V.mass t=kappa*t) :
    TendstoLocallyUniformlyOn (fun n v=>(M n).R ((M n).xs*v)/(M n).xs)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n=>(M n).hxs.le)
      (fun n=>(M n).canonical_direct_test_band_ge_scale) hcanonical
  exact actual_radius_locally_uniform_of_linear_cdf M (fun n=>(M n).xs)
    (hcl.trans_le hkappa) (fun n=>(M n).hxs) hx (fun t ht=>by
      simpa only [hlinear t ht] using d.radius_inverse_cdf_limit t)

theorem original_radius_uniform_on_compact_of_linear_profile
    (d : ActualInheritedLocalScalarLimitData hT S M htotal)
    {kappa : ℝ} (hcl : 0 < cl) (hkappa : cl ≤ kappa)
    (hcanonical : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hlinear : ∀t > 0,d.V.mass t=kappa*t)
    {a b : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn (fun n v=>(M n).R ((M n).xs*v)/(M n).xs)
      (fun v=>v/kappa) atTop (Icc a b) := by
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    ((d.original_radius_locally_uniform_of_linear_profile hcl hkappa hcanonical hlinear).mono
      (fun _ hv=>ha.trans_le hv.1))

theorem original_radius_compact_error_of_linear_profile
    (d : ActualInheritedLocalScalarLimitData hT S M htotal)
    {kappa : ℝ} (hcl : 0 < cl) (hkappa : cl ≤ kappa)
    (hcanonical : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hlinear : ∀t > 0,d.V.mass t=kappa*t)
    {a b eta : ℝ} (ha : 0 < a) (heta : 0 < eta) :
    ∀ᶠn in atTop,∀v∈Icc a b,
      |(M n).R ((M n).xs*v)-(M n).xs*(v/kappa)| < eta*(M n).xs := by
  have H := Metric.tendstoUniformlyOn_iff.mp
    (d.original_radius_uniform_on_compact_of_linear_profile (b:=b) hcl hkappa hcanonical hlinear ha)
      eta heta
  filter_upwards [H] with n hn v hv
  have hi : |(M n).R ((M n).xs*v)/(M n).xs-v/kappa| < eta := by
    simpa only [Real.dist_eq,abs_sub_comm] using hn v hv
  have he : (M n).R ((M n).xs*v)/(M n).xs-v/kappa=
      ((M n).R ((M n).xs*v)-(M n).xs*(v/kappa))/(M n).xs := by
    field_simp [(M n).hxs.ne', (hcl.trans_le hkappa).ne']
  rw [he,abs_div,abs_of_pos (M n).hxs] at hi
  exact (div_lt_iff₀ (M n).hxs).mp hi

end ActualInheritedLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization

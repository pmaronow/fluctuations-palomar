module

public import ComparisonActualHighWallThetaZeroMacroscopicEndpoint
public import ComparisonActualHighWallThetaZeroHighOnlySourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ} {dim : ℕ → ℕ}

theorem high_only_root_endpoint_cost_tendsto_zero
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (hs : Tendsto (fun n=>(P n).data.s) atTop (𝓝 0))
    (hunit : ∀ᶠn in atTop,(P n).xs≤1)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).data.d
      (P n).lam (P n).xs/(P n).xs^2) atTop (𝓝 0))
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=(P n).changedBare u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=(P n).changedField u) :
    Tendsto (fun n=>comparisonEndpointL1Cost T (root n).b (root n).h)
      atTop (𝓝 0) := by
  have hlam := actual_comparison_parameter_tendsto_zero_of_weak_bounded_call
    (hunit.mono fun n hn => ⟨(P n).data.hd,(P n).hlam.le,(P n).hxs,hn,(P n).hld⟩)
    hweak
  have Hupper : Tendsto (fun n=>T*(P n).data.s/4+(3/4:ℝ)*(P n).lam)
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div,add_zero] using
      (hs.const_mul T |>.div_const 4).add (hlam.const_mul (3/4:ℝ))
  have Hwall : Tendsto (fun n=>comparisonEndpointL1Cost T
      (P n).changedBare (P n).changedField) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n=>
      actual_high_only_endpoint_l1_cost_nonneg T
        (P n).changedBare (P n).changedField)) ?_ Hupper
    filter_upwards [hT] with n hnT
    have H := (P n).theta_zero_changed_endpoint_cost_le
    have Hs : 0≤(P n).data.s := (P n).data.hs.1.le
    have He := (P n).data.hepsilon.2.le
    rw [hnT] at He H
    have Hmul := mul_le_mul_of_nonneg_left He Hs
    nlinarith only [H,Hmul]
  apply Filter.Tendsto.congr' ?_ Hwall
  filter_upwards [hb,hh] with n hbn hhn
  have Hb : (root n).b=(P n).changedBare := funext hbn
  have Hh : (root n).h=(P n).changedField := funext hhn
  rw [Hb,Hh]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

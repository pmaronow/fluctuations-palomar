module

public import ComparisonActualHighWallThetaZeroErrorTransport
public import ComparisonActualHighWallThetaZeroSelectedAmplitude

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem eventually_theta_zero_near_zero_point
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct) :
    ∃K:ℝ,0<K ∧ ∀ᶠn:ℕ in atTop,
      ∀Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u≤
        Q.lam*(K+(Az+1/cl)^2)*(Q.xs+u)^2 := by
  obtain ⟨K,hK,HB⟩:=eventually_actual_theta_zero_selected_B_normalized
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [HB] with n hnB
  intro Q u hu
  have HB:=hnB Q u hu
  have HR:=Q.inverse_radius_le_source_mass hcl hAz (Ioc_subset_Icc_self hu)
  have hR0:0≤Q.sweepRadius u:=
    Q.data.hrbounds.1.le.trans (Q.shiftedNativeModel.R_bounds u).1
  have HS:0≤orderedPathS (n+1) Q.sweepBf Q.sweepHf u:=by
    exact (orderedPath_SK_bounds (n+1) Q.data.hn Q.sweepBf Q.sweepHf
      Q.sweep_bf_monotone Q.sweep_hf_monotone hu).1
  have hR2:(Q.sweepRadius u)^2≤(Az+1/cl)^2*(Q.xs+u)^2:=by
    have H:=pow_le_pow_left₀ hR0 HR 2
    nlinarith only [H]
  have hquadratic:(orderedPathB (n+1) Q.sweepBf Q.sweepHf u-
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2)+
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-Q.sweepRadius u)^2≤
        (K+(Az+1/cl)^2)*(Q.xs+u)^2:=by
    nlinarith only [HB,hR2,mul_nonneg HS hR0]
  have hcoef:=Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u
  have H1:=mul_le_mul_of_nonneg_left hquadratic hcoef.1
  have H2:=mul_le_mul_of_nonneg_right hcoef.2
    (show 0≤(K+(Az+1/cl)^2)*(Q.xs+u)^2 by positivity)
  change Q.data.thetaZeroErrorDensity Q.lam Q.alpha u≤_ at H1 ⊢
  nlinarith only [H1,H2]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

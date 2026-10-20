module

public import ComparisonActualHighWallThetaZeroSelectedRadius
public import ComparisonSignedCavityInnovationClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem sweep_high_field_clock {u:ℝ} (hu:u∈Icc Q.data.s 1):
    (Q.sweepHf u:ℝ)=
      laplaceComparisonStrength Q.data.d Q.lam (Q.sweepRadius u)*Q.sweepRadius u := by
  have hr:0≤Q.sweepRadius u:=Q.data.hrbounds.1.le.trans
    (omittedSweepQuantile_bounds Q.data.hr ⟨Q.data.hs.1.le,Q.data.hs1⟩
      Q.data.hc Q.data.hk Q.data.hkc Q.data.hm Q.data.hM Q.alpha u).1
  have he:0≤Q.sweepCoefficient u:=by
    simp only [sweepCoefficient,omittedStrengthCoefficient,ite_eq_left hu.1]
    exact (laplaceComparisonStrength_pos Q.data.d Q.hlam _).le
  have hnonneg:0≤Q.data.thetaZeroHighOnlyData.h u+
      Q.sweepCoefficient u*Q.sweepRadius u:=by
    simpa only [show Q.data.thetaZeroHighOnlyData.h u=0 from rfl,zero_add] using
      (mul_nonneg he hr)
  change ((Q.data.thetaZeroHighOnlyData.h u+
    Q.sweepCoefficient u*Q.sweepRadius u).toNNReal:ℝ)=_
  rw [Real.coe_toNNReal _ hnonneg]
  simp only [show Q.data.thetaZeroHighOnlyData.h u=0 from rfl,zero_add,
    sweepCoefficient,omittedStrengthCoefficient,ite_eq_left hu.1]

theorem high_field_radius_gap
    (hN:1≤Q.data.N) (hlog:1≤Real.log Q.data.N) (hnd:1/Q.data.N≤Q.data.d)
    {u v:ℝ} (hu:u∈Icc Q.data.s 1) (hv:v∈Icc Q.data.s 1) (huv:u≤v):
    ((1/3)/Real.log Q.data.N)*
      laplaceComparisonStrength Q.data.d Q.lam (Q.sweepRadius v)*
      (Q.sweepRadius v-Q.sweepRadius u)≤
      (Q.sweepHf v:ℝ)-(Q.sweepHf u:ℝ) := by
  rw [Q.sweep_high_field_clock hv,Q.sweep_high_field_clock hu]
  have HRu:=omittedSweepQuantile_bounds Q.data.hr
    ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
    Q.data.hm Q.data.hM Q.alpha u
  have HRv:=omittedSweepQuantile_bounds Q.data.hr
    ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
    Q.data.hm Q.data.hM Q.alpha v
  have HR:=omittedSweepQuantile_monotone Q.data.hr
    ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
    Q.data.hm Q.data.hM Q.alpha huv
  exact actual_comparison_radius_field_increment_lower hN hlog Q.data.hd hnd
    Q.hlam Q.hld (Q.data.hrbounds.1.le.trans HRu.1) HRv.2 HR

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

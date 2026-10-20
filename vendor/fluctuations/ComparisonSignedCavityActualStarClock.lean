module

public import ComparisonSignedCavityActualStarSelection

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem strength_le_scale_of_radius_lower
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {c W r : ℝ} (hc : 0 < c) (hW : 0 < W) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hr : c*W ≤ r ∧ r ≤ 1)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2) :
    laplaceComparisonStrength M.context.d M.lam r ≤ (1+1/c)*W^2 := by
  have hr0 : 0 < r := (mul_pos hc hW).trans_le hr.1
  have hm:=laplaceComparisonStrength_monotonicities M.context.hd.ne' M.hlam (r₀:=0) le_rfl
  have hg : 0 ≤ laplaceComparisonStrength M.context.d M.lam r :=
    (laplaceComparisonStrength_pos _ M.hlam r).le
  have hcinv : 0 ≤ 1/c := by positivity
  by_cases hxr : M.xs ≤ r
  · have H:=hm.1 ⟨M.hxs.le,hxs.trans hW1⟩ ⟨hr0.le,hr.2⟩ hxr
    have he : W^2 ≤ (1+1/c)*W^2 := by nlinarith [mul_nonneg hcinv (sq_nonneg W)]
    exact (H.trans hscale).trans he
  · have H:=hm.2 ⟨hr0.le,hr.2⟩ ⟨M.hxs.le,hxs.trans hW1⟩ (le_of_not_ge hxr)
    have H2:=mul_le_mul hscale hxs M.hxs.le (sq_nonneg W)
    have H3:=mul_le_mul_of_nonneg_left hr.1 hg
    have hdiv : laplaceComparisonStrength M.context.d M.lam r ≤ W^2/c := by
      apply (le_div_iff₀ hc).mpr
      nlinarith only [H,H2,H3,hW]
    have he : W^2/c ≤ (1+1/c)*W^2 := by
      calc
        _ ≤ W^2+W^2/c := le_add_of_nonneg_left (sq_nonneg W)
        _ = _ := by ring
    exact hdiv.trans he

theorem bare_selected_mass_clock_calibration
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u c W T : ℝ} (hu : u∈Icc (0:ℝ) 1) (hc : 0 < c) (hW : 0 < W)
    (hW1 : W ≤ 1) (hxs : M.xs ≤ W)
    (hr : c*W ≤ M.R u)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmall : (1+1/c)*W^2 ≤ T/2)
    (hb : M.b u=T) (hh : M.h u=0)
    (hmean : (3*c/4)*W ≤ orderedPathS (n+1) M.bf M.hf u)
    (hmismatch : |orderedPathS (n+1) M.bf M.hf u-M.R u| ≤ c*W/4) :
    (3*T*c/8)*W ≤ actualMixedClock (n+1) M.bf M.hf u ∧
    |actualMixedClock (n+1) M.bf M.hf u-T*orderedPathS (n+1) M.bf M.hf u| ≤
      ((c+1)/4)*W^3 := by
  have hR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hg:=M.strength_le_scale_of_radius_lower hc hW hW1 hxs ⟨hr,hR.2⟩ hscale
  have hbmin : T/2 ≤ (M.bf u:ℝ) := by
    change T/2 ≤ ((M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)).toNNReal:ℝ)
    rw [hb]
    exact (by linarith : T/2 ≤ T-laplaceComparisonStrength M.context.d M.lam (M.R u)).trans
      (Real.le_coe_toNNReal _)
  have hS0 : 0 ≤ orderedPathS (n+1) M.bf M.hf u :=
    (by positivity : 0 ≤ (3*c/4)*W).trans hmean
  have hprod:=mul_le_mul hbmin hmean
    (by positivity : 0 ≤ (3*c/4)*W) (M.bf u).coe_nonneg
  refine ⟨?_,?_⟩
  · unfold actualMixedClock
    nlinarith [(M.hf u).coe_nonneg]
  · have haR:=comparisonSweepQuantile_mass_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha hu
    have H:=M.star_mixed_clock_compensation hR T
    simp only [starMean,haR,hb,hh,sub_self,zero_mul,zero_add] at H
    rw [H,abs_mul,abs_of_pos (laplaceComparisonStrength_pos _ M.hlam _),abs_sub_comm]
    have hm:=mul_le_mul hg hmismatch (abs_nonneg _)
      (by positivity : 0 ≤ (1+1/c)*W^2)
    exact hm.trans_eq (by field_simp [hc.ne'])

theorem Potential.exists_bare_thermal_good_star_clock_calibration
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a z c C W T : ℝ}
    (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1) (hc : 0 < c) (hW : 0 < W)
    (hW1 : W ≤ 1) (hxs : M.xs ≤ W)
    (htravelsmall : M.cavityCapTravel ≤ c*W/32)
    (hband : ∀u∈Ioo a z,c*W ≤ M.R u ∧ M.R u ≤ C*W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmallclock : (1+1/c)*W^2 ≤ T/2)
    (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0)
    (hsmallthermal : (∫u in Ioo a z,orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2) <
      ((c*W)^2/64)*((z-a)-M.context.N^(-delta)*M.context.U)) :
    ∃u∈Ioo a z,p.H (M.R u) ≤ 0 ∧
      orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2 ≤ (c*W)^2/64 ∧
      |orderedPathS (n+1) M.bf M.hf u-M.R u| ≤ c*W/4 ∧
      (3*c/4)*W ≤ orderedPathS (n+1) M.bf M.hf u ∧
      orderedPathS (n+1) M.bf M.hf u ≤ (C+c/4)*W ∧
      (3*T*c/8)*W ≤ actualMixedClock (n+1) M.bf M.hf u ∧
      |actualMixedClock (n+1) M.bf M.hf u-T*orderedPathS (n+1) M.bf M.hf u| ≤
        ((c+1)/4)*W^3 := by
  obtain ⟨u,hu,hH,hthermal,hmis,hmeanlo,hmeanhi⟩:=
    p.exists_thermal_good_star_mean_bounds ha haz hz hc hW htravelsmall hband hsmallthermal
  have hui : u∈Icc (0:ℝ) 1 := ⟨ha.trans hu.1.le,hu.2.le.trans hz⟩
  have hclock:=M.bare_selected_mass_clock_calibration hui hc hW hW1 hxs (hband u hu).1
    hscale hsmallclock (hb u) (hh u) hmeanlo hmis
  exact ⟨u,hu,hH,hthermal,hmis,hmeanlo,hmeanhi,hclock.1,hclock.2⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

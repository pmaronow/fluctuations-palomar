module

public import ComparisonSignedCavityActualStarMassBand

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem near_bare_selected_mass_clock_calibration
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u c C W T Cb Ch : ℝ} (hu : u∈Icc (0:ℝ) 1) (hc : 0 < c) (hW : 0 < W)
    (hW1 : W ≤ 1) (hxs : M.xs ≤ W) (hCb : 0 ≤ Cb)
    (hr : c*W ≤ M.R u)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmall : (Cb+1+1/c)*W^2 ≤ T/2)
    (hb : |M.b u-T| ≤ Cb*W^2) (hh : |M.h u| ≤ Ch*W^3)
    (hmeanlo : (3*c/4)*W ≤ orderedPathS (n+1) M.bf M.hf u)
    (hmeanhi : orderedPathS (n+1) M.bf M.hf u ≤ (C+c/4)*W)
    (hmismatch : |orderedPathS (n+1) M.bf M.hf u-M.R u| ≤ c*W/4) :
    (3*T*c/8)*W ≤ actualMixedClock (n+1) M.bf M.hf u ∧
    |actualMixedClock (n+1) M.bf M.hf u-T*orderedPathS (n+1) M.bf M.hf u| ≤
      (Cb*(C+c/4)+Ch+(c+1)/4)*W^3 := by
  have hR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hg:=M.strength_le_scale_of_radius_lower hc hW hW1 hxs ⟨hr,hR.2⟩ hscale
  have hbmin : T/2 ≤ (M.bf u:ℝ) := by
    change T/2 ≤ ((M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)).toNNReal:ℝ)
    exact (by nlinarith [(abs_le.mp hb).1] :
      T/2 ≤ M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)).trans
      (Real.le_coe_toNNReal _)
  have hS0 : 0 ≤ orderedPathS (n+1) M.bf M.hf u :=
    (by positivity : 0 ≤ (3*c/4)*W).trans hmeanlo
  have hprod:=mul_le_mul hbmin hmeanlo
    (by positivity : 0 ≤ (3*c/4)*W) (M.bf u).coe_nonneg
  refine ⟨?_,?_⟩
  · unfold actualMixedClock
    nlinarith [(M.hf u).coe_nonneg]
  · have haR:=comparisonSweepQuantile_mass_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha hu
    have H:=M.star_mixed_clock_compensation hR T
    simp only [starMean,haR] at H
    rw [H]
    have hbb : |(M.b u-T)*orderedPathS (n+1) M.bf M.hf u| ≤
        Cb*(C+c/4)*W^3 := by
      rw [abs_mul,abs_of_nonneg hS0]
      have hm:=mul_le_mul hb hmeanhi hS0 (mul_nonneg hCb (sq_nonneg W))
      exact hm.trans_eq (by ring)
    have hcomp : |laplaceComparisonStrength M.context.d M.lam (M.R u)*
        (M.R u-orderedPathS (n+1) M.bf M.hf u)| ≤ ((c+1)/4)*W^3 := by
      rw [abs_mul,abs_of_pos (laplaceComparisonStrength_pos _ M.hlam _),abs_sub_comm]
      have hm:=mul_le_mul hg hmismatch (abs_nonneg _)
        (by positivity : 0 ≤ (1+1/c)*W^2)
      exact hm.trans_eq (by field_simp [hc.ne'])
    have habs:=((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add hbb hh)) hcomp))
    exact habs.trans_eq (by ring)

theorem Potential.exists_near_bare_thermal_good_star_clock_calibration
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a z c C W T Cb Ch : ℝ}
    (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1) (hc : 0 < c) (hW : 0 < W)
    (hW1 : W ≤ 1) (hxs : M.xs ≤ W) (hCb : 0 ≤ Cb)
    (htravelsmall : M.cavityCapTravel ≤ c*W/32)
    (hband : ∀u∈Ioo a z,c*W ≤ M.R u ∧ M.R u ≤ C*W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmallclock : (Cb+1+1/c)*W^2 ≤ T/2)
    (hb : ∀u∈Ioo a z,|M.b u-T| ≤ Cb*W^2)
    (hh : ∀u∈Ioo a z,|M.h u| ≤ Ch*W^3)
    (hsmallthermal : (∫u in Ioo a z,orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2) <
      ((c*W)^2/64)*((z-a)-M.context.N^(-delta)*M.context.U)) :
    ∃u∈Ioo a z,p.H (M.R u) ≤ 0 ∧
      (3*c/4)*W ≤ orderedPathS (n+1) M.bf M.hf u ∧
      orderedPathS (n+1) M.bf M.hf u ≤ (C+c/4)*W ∧
      (3*T*c/8)*W ≤ actualMixedClock (n+1) M.bf M.hf u ∧
      |actualMixedClock (n+1) M.bf M.hf u-T*orderedPathS (n+1) M.bf M.hf u| ≤
        (Cb*(C+c/4)+Ch+(c+1)/4)*W^3 := by
  obtain ⟨u,hu,hH,_,hmis,hmeanlo,hmeanhi⟩:=
    p.exists_thermal_good_star_mean_bounds ha haz hz hc hW htravelsmall hband hsmallthermal
  have hui : u∈Icc (0:ℝ) 1 := ⟨ha.trans hu.1.le,hu.2.le.trans hz⟩
  have hclock:=M.near_bare_selected_mass_clock_calibration hui hc hW hW1 hxs hCb
    (hband u hu).1 hscale hsmallclock (hb u hu) (hh u hu) hmeanlo hmeanhi hmis
  exact ⟨u,hu,hH,hmeanlo,hmeanhi,hclock.1,hclock.2⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

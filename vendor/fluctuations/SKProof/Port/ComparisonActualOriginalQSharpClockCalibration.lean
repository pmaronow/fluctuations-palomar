module

public import SKProof.Port.ComparisonActualOriginalQClocks
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import ComparisonSignedCavityActualNearBareTightClock

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 8000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem strength_le_scale_of_radius_lower
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {c W r : ℝ} (hc : 0 < c) (hW : 0 < W) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hr : c*W ≤ r ∧ r ≤ 1)
    (hscale : laplaceComparisonStrength M.data.d M.lam M.xs ≤ W^2) :
    laplaceComparisonStrength M.data.d M.lam r ≤ (1+1/c)*W^2 := by
  have hr0 : 0 < r := (mul_pos hc hW).trans_le hr.1
  have hm:=laplaceComparisonStrength_monotonicities M.data.hd.ne' M.hlam (r₀:=0) le_rfl
  have hg : 0 ≤ laplaceComparisonStrength M.data.d M.lam r :=
    (laplaceComparisonStrength_pos _ M.hlam r).le
  have hcinv : 0 ≤ 1/c := by positivity
  by_cases hxr : M.xs ≤ r
  · have H:=hm.1 ⟨M.hxs.le,hxs.trans hW1⟩ ⟨hr0.le,hr.2⟩ hxr
    have he : W^2 ≤ (1+1/c)*W^2 := by nlinarith [mul_nonneg hcinv (sq_nonneg W)]
    exact (H.trans hscale).trans he
  · have H:=hm.2 ⟨hr0.le,hr.2⟩ ⟨M.hxs.le,hxs.trans hW1⟩ (le_of_not_ge hxr)
    have H2:=mul_le_mul hscale hxs M.hxs.le (sq_nonneg W)
    have H3:=mul_le_mul_of_nonneg_left hr.1 hg
    have hdiv : laplaceComparisonStrength M.data.d M.lam r ≤ W^2/c := by
      apply (le_div_iff₀ hc).mpr
      nlinarith only [H,H2,H3,hW]
    have he : W^2/c ≤ (1+1/c)*W^2 := by
      calc
        _ ≤ W^2+W^2/c := le_add_of_nonneg_left (sq_nonneg W)
        _ = _ := by ring
    exact hdiv.trans he

theorem near_bare_selected_mass_tight_clock_calibration
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u c Cs W T Cb Ch : ℝ} (hu : u∈Icc (0:ℝ) 1) (hs : M.data.s ≤ u) (hc : 0 < c) (hW : 0 < W)
    (hW1 : W ≤ 1) (hxs : M.xs ≤ W) (hCb : 0 ≤ Cb)
    (hr : c*W ≤ M.sweepRadius u)
    (hscale : laplaceComparisonStrength M.data.d M.lam M.xs ≤ W^2)
    (hsmall : (Cb+1+1/c)*W^2 ≤ T/2)
    (hb : |M.b u-T| ≤ Cb*W^2) (hh : |M.h u| ≤ Ch*W^3)
    (hmeanlo : (3*c/4)*W ≤ orderedPathS (n+1) M.sweepBf M.sweepHf u)
    (hmeanhi : orderedPathS (n+1) M.sweepBf M.sweepHf u ≤ Cs*W)
    (hmismatch : |orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u| ≤ c*W/8)
    (hbudget : Cb*Cs+Ch ≤ (c+1)/8) :
    (3*T*c/8)*W ≤ actualMixedClock (n+1) M.sweepBf M.sweepHf u ∧
    |actualMixedClock (n+1) M.sweepBf M.sweepHf u-T*orderedPathS (n+1) M.sweepBf M.sweepHf u| ≤
      ((c+1)/4)*W^3 := by
  have hR:=M.shiftedNativeModel.R_bounds u
  have hcoe:=M.inherited_clock_coe hu
  have hcEq : M.sweepCoefficient u=laplaceComparisonStrength M.data.d M.lam (M.sweepRadius u):=by
    unfold sweepCoefficient omittedStrengthCoefficient
    rw [ite_eq_left hs]
  have hg:=M.strength_le_scale_of_radius_lower hc hW hW1 hxs ⟨hr,hR.2⟩ hscale
  have hbmin : T/2 ≤ (M.sweepBf u:ℝ) := by
    rw [hcoe.1,hcEq]
    nlinarith only [(abs_le.mp hb).1,hg,hsmall]
  have hS0 : 0 ≤ orderedPathS (n+1) M.sweepBf M.sweepHf u :=
    (by positivity : 0 ≤ (3*c/4)*W).trans hmeanlo
  have hprod:=mul_le_mul hbmin hmeanlo
    (by positivity : 0 ≤ (3*c/4)*W) (M.sweepBf u).coe_nonneg
  refine ⟨?_,?_⟩
  · unfold actualMixedClock
    nlinarith [(M.sweepHf u).coe_nonneg]
  · have H : actualMixedClock (n+1) M.sweepBf M.sweepHf u-T*orderedPathS (n+1) M.sweepBf M.sweepHf u=
        (M.b u-T)*orderedPathS (n+1) M.sweepBf M.sweepHf u+M.h u+
          laplaceComparisonStrength M.data.d M.lam (M.sweepRadius u)*
            (M.sweepRadius u-orderedPathS (n+1) M.sweepBf M.sweepHf u):=by
      unfold actualMixedClock
      rw [hcoe.1,hcoe.2,hcEq]
      ring
    rw [H]
    have hbb : |(M.b u-T)*orderedPathS (n+1) M.sweepBf M.sweepHf u| ≤ Cb*Cs*W^3 := by
      rw [abs_mul,abs_of_nonneg hS0]
      have hm:=mul_le_mul hb hmeanhi hS0 (mul_nonneg hCb (sq_nonneg W))
      exact hm.trans_eq (by ring)
    have hcomp : |laplaceComparisonStrength M.data.d M.lam (M.sweepRadius u)*
        (M.sweepRadius u-orderedPathS (n+1) M.sweepBf M.sweepHf u)| ≤ ((c+1)/8)*W^3 := by
      rw [abs_mul,abs_of_pos (laplaceComparisonStrength_pos _ M.hlam _),abs_sub_comm]
      have hm:=mul_le_mul hg hmismatch (abs_nonneg _)
        (by positivity : 0 ≤ (1+1/c)*W^2)
      exact hm.trans_eq (by field_simp [hc.ne'])
    have Hbound:=(abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add hbb hh)) hcomp)
    have Hbudget:=mul_le_mul_of_nonneg_right hbudget (pow_nonneg hW.le 3)
    nlinarith only [Hbound,Hbudget]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

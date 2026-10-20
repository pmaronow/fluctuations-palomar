module

public import SKProof.Port.ComparisonActualOriginalQAllCapMismatch
public import ComparisonScalarWeightedCapTravel
public import ComparisonStrengthRescaling
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.flat_left_contact_mean_ge
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a r : ℝ} (ha : M.data.rmin ≤ a) (har : a < r) (hr : r  ≤  1)
    (hleft : p.H a=0) (hneg : p.H r<0)
    (hflat : ∀t∈Icc (0:ℝ) r,comparisonLogSlope (laplaceComparisonStrength M.data.d M.lam) t=0) :
    a  ≤  M.radiusS r := by
  let g:=laplaceComparisonStrength M.data.d M.lam
  let slope:=comparisonLogSlope g
  let S:=M.radiusS
  let B:=fun t=> orderedPathB (n+1) M.sweepBf M.sweepHf (M.alpha.val.val t)
  let J:=fun t=> M.controlFactor t*g t
  have hsub:Icc a r⊆Icc M.data.rmin 1:=Icc_subset_Icc ha hr
  have hJ t (_ht:t∈Icc a r):0< J t:=
    mul_pos (M.controlFactor_pos t) (laplaceComparisonStrength_pos _ M.hlam _)
  have hDp:∀ᵐ t, t∈Icc a r → HasDerivAt p.H
      (J t*comparisonBracket (slope t) t (S t) (B t)) t:=by
    filter_upwards [p.hD] with t ht hti
    have hp:0< t:=M.data.hrbounds.1.trans_le (hsub hti).1
    have H:=ht (hsub hti)
    rw [comparison_gradient_slope hp.ne' (laplaceComparisonStrength_pos _ M.hlam _).ne'] at H
    convert H using 1
    dsimp only [J,S,B,slope,g,radiusS,comparisonBracket]
    ring
  obtain ⟨l,hl,hgl⟩:=potential_negative_left_witness har
    (p.hH.mono (by simpa only [uIcc_of_le M.data.hr,uIcc_of_le har.le] using hsub))
    hJ hDp (by simpa only [hleft] using hneg)
  have hlf:slope l=0:=hflat l ⟨M.data.rmin_nonneg.trans (ha.trans hl.1.le),hl.2.le⟩
  rw [hlf] at hgl
  simp only [comparisonBracket,zero_mul,sub_zero,zero_div,mul_one] at hgl
  have hmom:=M.radius_moments
  have Hmono:=hmom.1 ⟨ha.trans hl.1.le,hl.2.le.trans hr⟩ ⟨ha.trans har.le,hr⟩ hl.2.le
  change S l ≤  S r at Hmono
  change a ≤  S r
  linarith only [hl.1,hgl,Hmono]

theorem Potential.flat_negative_point_abs_mismatch_le
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {r : ℝ} (hr : r∈Ioo M.data.rmin 1) (hneg : p.H r<0)
    (hflat : ∀t∈Icc (0:ℝ) r,comparisonLogSlope (laplaceComparisonStrength M.data.d M.lam) t=0) :
    |M.radiusS r-r| ≤ M.data.rmin + M.cavityCapTravel := by
  have hrneg:r∈p.negativeSet:=⟨hr,hneg⟩
  obtain ⟨hl,hlr,hrz,hz,heq,_,_⟩:=wholeCap_component_endpoints p.negativeSet_open
    p.negativeSet_subset hrneg
  have hinterval:∀t∈Ioo (sInf (ordConnectedComponent p.negativeSet r))
      (sSup (ordConnectedComponent p.negativeSet r)),p.H t<0:=by
    intro t ht
    exact (ordConnectedComponent_subset (heq.symm ▸ ht)).2
  have hwidth:=(p.cap_interval_travel M hl (hlr.trans hrz).le hz hinterval).2.1
  have hend:=p.component_endpoint_alternatives hrneg
  have hmom:=M.radius_moments
  have Hleft:sInf (ordConnectedComponent p.negativeSet r) ≤ M.radiusS r+M.data.rmin:=by
    rcases hend.1 with hc|hwall
    · exact (p.flat_left_contact_mean_ge hl hlr hr.2.le hc hneg hflat).trans
        (le_add_of_nonneg_right M.data.rmin_nonneg)
    · rw [hwall]
      exact le_add_of_nonneg_left (hmom.2.2 r (Ioo_subset_Icc_self hr)).1.1
  have Hright:M.radiusS r ≤  sSup (ordConnectedComponent p.negativeSet r):=by
    rcases hend.2 with hc|hwall
    · exact p.cap_point_mean_le_right hl hz ⟨hlr,hrz⟩ hc hneg
    · rw [hwall]
      exact (hmom.2.2 r (Ioo_subset_Icc_self hr)).1.2
  have Hcharge:|M.radiusS r-r| ≤ M.data.rmin+
      (sSup (ordConnectedComponent p.negativeSet r)-
        sInf (ordConnectedComponent p.negativeSet r)):=by
    exact abs_le.mpr ⟨by linarith only [Hleft,hrz],
      by linarith only [Hright,hlr,M.data.rmin_nonneg]⟩
  exact Hcharge.trans (add_le_add le_rfl hwidth)

theorem Potential.flat_nonpositive_abs_mismatch_ae
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {R : ℝ}
    (hflat : ∀t∈Icc (0:ℝ) R,comparisonLogSlope (laplaceComparisonStrength M.data.d M.lam) t=0) :
    ∀ᵐ r, r∈Icc M.data.rmin 1 → r ≤  R → p.H r ≤ 0 → |M.radiusS r-r| ≤ M.data.rmin + M.cavityCapTravel := by
  filter_upwards [p.hzero,volume.ae_ne M.data.rmin,volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri hrR hnonpos
  have hro:r∈Ioo M.data.rmin 1:=⟨lt_of_le_of_ne hri.1 hr0.symm,lt_of_le_of_ne hri.2 hr1⟩
  have HF:∀t∈Icc (0:ℝ) r,comparisonLogSlope (laplaceComparisonStrength M.data.d M.lam) t=0:=
    fun t ht=> hflat t ⟨ht.1,ht.2.trans hrR⟩
  rcases hnonpos.eq_or_lt with hz|hneg
  · have H:=(hrzero hri hz).1
    have he:=laplaceComparisonStrength_pos M.data.d M.hlam r
    rw [comparison_gradient_slope (M.data.hrbounds.1.trans hro.1).ne' he.ne',HF r ⟨M.data.rmin_nonneg.trans hri.1,le_rfl⟩] at H
    simp only [sub_zero,zero_mul,zero_div,mul_one] at H
    have HH:(2*r-2*M.radiusS r)=0:=by
      apply (mul_eq_zero.mp H).resolve_left he.ne'
    have HS:M.radiusS r=r:=by linarith only [HH]
    rw [HS,sub_self,abs_zero]
    exact add_nonneg M.data.rmin_nonneg M.cavityCapTravel_nonneg
  · exact p.flat_negative_point_abs_mismatch_le hro hneg HF

theorem Potential.flat_nonpositive_abs_mismatch_ae_high_mass
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {R : ℝ}
    (hflat : ∀t∈Icc (0:ℝ) R,comparisonLogSlope (laplaceComparisonStrength M.data.d M.lam) t=0) :
    ∀ᵐu,u∈Icc M.data.s 1 → M.sweepRadius u ≤ R → p.H (M.sweepRadius u) ≤ 0 →
      |orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u| ≤ M.data.rmin + M.cavityCapTravel := by
  have H:=ae_inverse_pullback
    (inverseIntegralConstraints_lipschitz M.data.hm M.data.hM M.alpha.property)
    (fun u (_ : u∈Icc M.data.s 1)=>M.sweepRadius_bounds u)

    (fun u hu=>M.sweepRadius_spec hu)

    (p.flat_nonpositive_abs_mismatch_ae hflat)
  filter_upwards [H] with u hu hui hrR hnonpos
  have HH:=hu hui hrR hnonpos
  simpa only [radiusS,M.sweepRadius_spec hui] using HH

theorem weighted_cap_travel_normalized_le
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (r : ℝ) :
    laplaceComparisonStrength M.data.d M.lam r*M.cavityCapTravel/M.xs^3 ≤
      Real.log ((1+M.data.U)/M.data.U)/M.data.N^delta :=
  comparison_scalar_native_cap_calibration M.data.hN M.data.hE M.data.hd
    M.hlam.le M.hld M.hxs M.hscale r

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeActualAllCapMismatch
public import ComparisonScalarWeightedCapTravel
public import ComparisonStrengthRescaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 15000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.flat_left_contact_mean_ge
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a r : ℝ} (ha : 0  ≤  a) (har : a < r) (hr : r  ≤  1)
    (hleft : p.H a=0) (hneg : p.H r<0)
    (hflat : ∀t∈Icc (0:ℝ) r,comparisonLogSlope (laplaceComparisonStrength M.context.d M.lam) t=0) :
    a  ≤  M.starMean r := by
  let g:=laplaceComparisonStrength M.context.d M.lam
  let slope:=comparisonLogSlope g
  let S:=M.starMean
  let B:=fun t=> orderedPathB (n+1) M.bf M.hf (M.alpha.val.val t)
  let J:=fun t=> M.controlFactor t*g t
  have hsub:Icc a r⊆Icc (0:ℝ) 1:=Icc_subset_Icc ha hr
  have hJ t (_ht:t∈Icc a r):0< J t:=
    mul_pos (M.controlFactor_pos t) (laplaceComparisonStrength_pos _ M.hlam _)
  have hDp:∀ᵐ t, t∈Icc a r → HasDerivAt p.H
      (J t*comparisonBracket (slope t) t (S t) (B t)) t:=by
    filter_upwards [p.hD,volume.ae_ne (0:ℝ)] with t ht ht0 hti
    have hp:0< t:=lt_of_le_of_ne (hsub hti).1 ht0.symm
    have H:=ht (hsub hti)
    rw [comparison_gradient_slope hp.ne' (laplaceComparisonStrength_pos _ M.hlam _).ne'] at H
    convert H using 1
    dsimp only [J,S,B,slope,g,starMean,comparisonBracket]
    ring
  obtain ⟨l,hl,hgl⟩:=potential_negative_left_witness har
    (p.hH.mono (by simpa only [uIcc_of_le zero_le_one,uIcc_of_le har.le] using hsub))
    hJ hDp (by simpa only [hleft] using hneg)
  have hlf:slope l=0:=hflat l ⟨ha.trans hl.1.le,hl.2.le⟩
  rw [hlf] at hgl
  simp only [comparisonBracket,zero_mul,sub_zero,zero_div,mul_one] at hgl
  have hmom:=comparisonVariableEndpoint_radius_moments M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM (n+1) (by omega)
    M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have Hmono:=hmom.1 ⟨ha.trans hl.1.le,hl.2.le.trans hr⟩ ⟨ha.trans har.le,hr⟩ hl.2.le
  change S l ≤  S r at Hmono
  change a ≤  S r
  linarith only [hl.1,hgl,Hmono]

theorem Potential.flat_negative_point_abs_mismatch_le
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hneg : p.H r<0)
    (hflat : ∀t∈Icc (0:ℝ) r,comparisonLogSlope (laplaceComparisonStrength M.context.d M.lam) t=0) :
    |M.starMean r-r| ≤  M.cavityCapTravel := by
  have hrneg:r∈p.negativeSet:=⟨hr,hneg⟩
  obtain ⟨hl,hlr,hrz,hz,heq,_,_⟩:=wholeCap_component_endpoints p.negativeSet_open
    (inter_subset_left.trans Ioo_subset_Icc_self) hrneg
  have hinterval:∀t∈Ioo (sInf (ordConnectedComponent p.negativeSet r))
      (sSup (ordConnectedComponent p.negativeSet r)),p.H t<0:=by
    intro t ht
    exact (ordConnectedComponent_subset (heq.symm ▸ ht)).2
  have hwidth:=p.cap_interval_travel hl (hlr.trans hrz) hz hinterval
  have hend:=p.negative_component_endpoints hrneg
  have hmom:=comparisonVariableEndpoint_radius_moments M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM (n+1) (by omega)
    M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have Hleft:sInf (ordConnectedComponent p.negativeSet r) ≤  M.starMean r:=by
    rcases hend.1 with hc|hwall
    · exact p.flat_left_contact_mean_ge hl hlr hr.2.le hc hneg hflat
    · rw [hwall]
      exact (hmom.2.2 r (Ioo_subset_Icc_self hr)).1.1
  have Hright:M.starMean r ≤  sSup (ordConnectedComponent p.negativeSet r):=by
    rcases hend.2 with hc|hwall
    · exact p.cap_point_mean_le_right hl hz ⟨hlr,hrz⟩ hc hneg
    · rw [hwall]
      exact (hmom.2.2 r (Ioo_subset_Icc_self hr)).1.2
  exact (abs_le.mpr ⟨by linarith only [Hleft,hrz],by linarith only [Hright,hlr]⟩).trans hwidth

theorem Potential.flat_nonpositive_abs_mismatch_ae
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {R : ℝ}
    (hflat : ∀t∈Icc (0:ℝ) R,comparisonLogSlope (laplaceComparisonStrength M.context.d M.lam) t=0) :
    ∀ᵐ r, r∈Icc (0:ℝ) 1 → r ≤  R → p.H r ≤ 0 → |M.starMean r-r| ≤  M.cavityCapTravel := by
  filter_upwards [p.hzero,volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri hrR hnonpos
  have hro:r∈Ioo (0:ℝ) 1:=⟨lt_of_le_of_ne hri.1 hr0.symm,lt_of_le_of_ne hri.2 hr1⟩
  have HF:∀t∈Icc (0:ℝ) r,comparisonLogSlope (laplaceComparisonStrength M.context.d M.lam) t=0:=
    fun t ht=> hflat t ⟨ht.1,ht.2.trans hrR⟩
  rcases hnonpos.eq_or_lt with hz|hneg
  · have H:=hrzero hri hz
    have he:=laplaceComparisonStrength_pos M.context.d M.hlam r
    rw [comparison_gradient_slope hro.1.ne' he.ne',HF r ⟨hri.1,le_rfl⟩] at H
    simp only [sub_zero,zero_mul,zero_div,mul_one] at H
    have HH:(2*r-2*M.starMean r)=0:=by
      apply (mul_eq_zero.mp H).resolve_left he.ne'
    have HS:M.starMean r=r:=by linarith only [HH]
    rw [HS,sub_self,abs_zero]
    exact M.cavityCapTravel_nonneg
  · exact p.flat_negative_point_abs_mismatch_le hro hneg HF

theorem Potential.flat_nonpositive_abs_mismatch_ae_mass
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {R : ℝ}
    (hflat : ∀t∈Icc (0:ℝ) R,comparisonLogSlope (laplaceComparisonStrength M.context.d M.lam) t=0) :
    ∀ᵐ u, u∈Icc (0:ℝ) 1 → M.R u ≤  R → p.H (M.R u) ≤ 0 → 
      |orderedPathS (n+1) M.bf M.hf u-M.R u| ≤  M.cavityCapTravel := by
  have H:=ae_inverse_pullback (inverseIntegralConstraints_lipschitz M.context.hm M.context.hM M.alpha.property)
    (fun u (_:u∈Icc (0:ℝ) 1)=> comparisonSweepQuantile_bounds M.context.hc M.context.hk
      M.context.hkc M.context.hm M.context.hM M.alpha u)
    (fun u hu=> comparisonSweepQuantile_mass_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha hu) (p.flat_nonpositive_abs_mismatch_ae hflat)
  filter_upwards [H] with u hu hui hrR hnonpos
  simpa only [starMean,comparisonSweepQuantile_mass_spec M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.alpha hui] using hu hui hrR hnonpos

theorem weighted_cap_travel_normalized_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (r : ℝ) :
    laplaceComparisonStrength M.context.d M.lam r*M.cavityCapTravel/M.xs^3  ≤ 
      Real.log ((1+M.context.U)/M.context.U)/M.context.N^delta := by
  exact comparison_scalar_native_cap_calibration M.context.hN M.context.hE M.context.hd
    M.hlam.le M.hld M.hxs M.hscale r

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

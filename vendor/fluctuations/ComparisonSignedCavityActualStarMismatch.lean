module

public import ComparisonNativeActualMinimumCapTravel
public import ComparisonNativeCapMismatch
public import ComparisonSignedCavityStarClockCalibration

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy GaussianCalculus Scalar WholeUnitSideKernel
set_option maxHeartbeats 5500000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.cap_point_squared_mismatch
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {l z r : ℝ} (hl : 0≤l) (hz : z≤1) (hr : r∈Ioo l z)
    (hleft : p.H l=0) (hright : p.H z=0 ∨ z=1) (hneg : p.H r<0) :
    (M.starMean r-r)^2≤16*(z-l)^2+2*M.cavityRadiusPointDefect r := by
  let g:=laplaceComparisonStrength M.context.d M.lam
  let slope:=comparisonLogSlope g
  let S:=M.starMean
  let B:=fun t=>orderedPathB (n+1) M.bf M.hf (M.alpha.val.val t)
  let J:=fun t=>M.controlFactor t*g t
  have hmom:=comparisonVariableEndpoint_radius_moments M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM (n+1) (by omega)
    M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hsub : Icc l z⊆Icc (0:ℝ) 1 := Icc_subset_Icc hl hz
  have hsubo : Ioo l z⊆Ioc (0:ℝ) 1 := fun t ht=>⟨hl.trans_lt ht.1,ht.2.le.trans hz⟩
  have hJ t (_ht : t∈Icc (0:ℝ) 1) : 0<J t :=
    mul_pos (M.controlFactor_pos t) (laplaceComparisonStrength_pos _ M.hlam _)
  have hDp : ∀ᵐt,t∈Icc (0:ℝ) 1→HasDerivAt p.H
      (J t*comparisonBracket (slope t) t (S t) (B t)) t := by
    filter_upwards [p.hD,volume.ae_ne (0:ℝ)] with t ht ht0 hti
    have hp : 0<t := lt_of_le_of_ne hti.1 ht0.symm
    have H:=ht hti
    rw [comparison_gradient_slope hp.ne' (laplaceComparisonStrength_pos _ M.hlam _).ne'] at H
    convert H using 1
    dsimp [J,S,B,slope,g,starMean,comparisonBracket]
    ring
  have hpm : MonotoneOn slope (Ioc (0:ℝ) 1) := by
    intro s hs t ht hst
    dsimp [slope,g]
    rw [laplaceComparisonStrength_logSlope M.context.hd.ne' M.hlam.ne',
      laplaceComparisonStrength_logSlope M.context.hd.ne' M.hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hst M.hlam.le) (pow_nonneg M.context.hd.le _))
  have hpb t (_ht : t∈Ioc (0:ℝ) 1) : slope t∈Icc (0:ℝ) 1 := by
    have H:=laplaceComparisonStrength_logSlope_mem M.context.hd.ne' M.hlam.ne' t
    exact ⟨H.1,H.2.le⟩
  have hSr : MonotoneOn S (Ioc (0:ℝ) 1) := hmom.1.mono Ioc_subset_Icc_self
  have hBr : MonotoneOn B (Ioc (0:ℝ) 1) := hmom.2.1.mono Ioc_subset_Icc_self
  have hS0 t (ht : t∈Ioc (0:ℝ) 1) : 0≤S t := (hmom.2.2 t (Ioc_subset_Icc_self ht)).1.1
  have hB2 t (ht : t∈Ioc (0:ℝ) 1) : (S t)^2≤B t := (hmom.2.2 t (Ioc_subset_Icc_self ht)).2.1
  have hac : AbsolutelyContinuousOnInterval p.H l z := p.hH.mono (by
    simpa only [uIcc_of_le zero_le_one,uIcc_of_le (hr.1.trans hr.2).le] using hsub)
  have hDsub := hDp.mono (fun t ht hti=>ht (hsub hti))
  rcases hright with hc|hterminal
  · exact cap_interior_mismatch hl hr hac (fun t ht=>hJ t (hsub ht)) hDsub hleft hc hneg
      (hpm.mono hsubo) (fun t ht=>hpb t (hsubo ht)) (hSr.mono hsubo) (hBr.mono hsubo)
      (fun t ht=>hS0 t (hsubo ht)) (fun t ht=>hB2 t (hsubo ht))
  · have hri : r∈Ioc (0:ℝ) 1 := hsubo hr
    have hSr1 : S r≤z := by
      rw [hterminal]
      exact (hmom.2.2 r (Ioc_subset_Icc_self hri)).1.2
    exact potential_left_contact_cap_mismatch hl hz hr p.hH hJ hDp hleft hneg hpm hpb
      hSr hBr (hS0 r hri) hSr1 hB2

theorem Potential.negative_point_squared_mismatch
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hneg : p.H r<0)
    (haway : M.cavityCapTravel<r) :
    (M.starMean r-r)^2≤16*M.cavityCapTravel^2+2*M.cavityRadiusPointDefect r := by
  have hrneg : r∈p.negativeSet := ⟨hr,hneg⟩
  obtain ⟨hl,hlr,hrz,hz,heq,_,_⟩:=wholeCap_component_endpoints p.negativeSet_open
    (inter_subset_left.trans Ioo_subset_Icc_self) hrneg
  have hinterval : ∀t∈Ioo (sInf (ordConnectedComponent p.negativeSet r))
      (sSup (ordConnectedComponent p.negativeSet r)),p.H t<0 := by
    intro t ht
    exact (ordConnectedComponent_subset (heq.symm ▸ ht)).2
  have hwidth:=p.cap_interval_travel hl (hlr.trans hrz) hz hinterval
  have hend:=p.negative_component_endpoints hrneg
  have hleft : p.H (sInf (ordConnectedComponent p.negativeSet r))=0 := by
    rcases hend.1 with H|H
    · exact H
    · rw [H,sub_zero] at hwidth
      exact False.elim ((not_lt_of_ge (hrz.le.trans hwidth)) haway)
  have H:=p.cap_point_squared_mismatch hl hz ⟨hlr,hrz⟩ hleft hend.2 hneg
  have hs:=pow_le_pow_left₀ (sub_nonneg.mpr (hlr.trans hrz).le) hwidth 2
  nlinarith

theorem Potential.nonpositive_squared_mismatch_ae
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    ∀ᵐr,r∈Icc (0:ℝ) 1→M.cavityCapTravel<r→p.H r≤0→
      (M.starMean r-r)^2≤16*M.cavityCapTravel^2+2*M.cavityRadiusPointDefect r := by
  have hmom:=comparisonVariableEndpoint_radius_moments M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM (n+1) (by omega)
    M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  filter_upwards [p.hzero,volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri haway hnonpos
  have hro : r∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hri.1 hr0.symm,lt_of_le_of_ne hri.2 hr1⟩
  rcases hnonpos.eq_or_lt with hz|hneg
  · have Hp:=laplaceComparisonStrength_logSlope_mem M.context.hd.ne' M.hlam.ne' r
    have H:=(comparison_gradient_contact_mismatch hro.1 (laplaceComparisonStrength_pos _ M.hlam r)
      ⟨Hp.1,Hp.2.le⟩ (hmom.2.2 r hri).1.1 (hmom.2.2 r hri).2.1 (hrzero hri hz)).2
    change (M.starMean r-r)^2≤M.cavityRadiusPointDefect r at H
    have hdef := M.cavityRadiusPointDefect_nonneg hri
    nlinarith [sq_nonneg M.cavityCapTravel]
  · exact p.negative_point_squared_mismatch hro hneg haway

theorem Potential.nonpositive_squared_mismatch_ae_mass
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    ∀ᵐu,u∈Icc (0:ℝ) 1→M.cavityCapTravel<M.R u→p.H (M.R u)≤0→
      (orderedPathS (n+1) M.bf M.hf u-M.R u)^2≤16*M.cavityCapTravel^2+
        2*(orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2) := by
  have H:=ae_inverse_pullback (inverseIntegralConstraints_lipschitz M.context.hm M.context.hM M.alpha.property)
    (fun u (_ : u∈Icc (0:ℝ) 1)=>comparisonSweepQuantile_bounds M.context.hc M.context.hk
      M.context.hkc M.context.hm M.context.hM M.alpha u)
    (fun u hu=>comparisonSweepQuantile_mass_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha hu) p.nonpositive_squared_mismatch_ae
  filter_upwards [H] with u hu hui haway hnonpos
  have H':=hu hui haway hnonpos
  simpa only [starMean,cavityRadiusPointDefect,
    comparisonSweepQuantile_mass_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha hui] using H'

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonActualHighWallThetaZeroOriginAbsorption
public import ComparisonActualHighWallAllCapMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  {Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.cap_point_mean_le_right (P:Q.Potential)
    {l z r:ℝ} (hl:Q.data.rmin≤l) (hz:z≤1) (hr:r∈Ioo l z)
    (hright:P.H z=0) (hneg:P.H r<0):Q.radiusS r≤z := by
  let g:=laplaceComparisonStrength Q.data.d Q.lam
  let slope:=comparisonLogSlope g
  let S:=Q.radiusS
  let B:=Q.radiusB
  let J:=fun t=>Q.controlFactor t*g t
  have hmom:=Q.radius_moments
  have hsub:Icc l z⊆Icc Q.data.rmin 1:=Icc_subset_Icc hl hz
  have hsubo:Ioo l z⊆Ioc Q.data.rmin 1:=
    fun t ht=>⟨hl.trans_lt ht.1,ht.2.le.trans hz⟩
  have hJ t (_ht:t∈Icc Q.data.rmin 1):0<J t:=
    mul_pos (inverseControlFactor_pos _ _ t)
      (laplaceComparisonStrength_pos Q.data.d Q.hlam _)
  have hDp:∀ᵐt,t∈Icc Q.data.rmin 1→HasDerivAt P.H
      (J t*comparisonBracket (slope t) t (S t) (B t)) t:=by
    filter_upwards [P.hD] with t ht hti
    have hp:0<t:=Q.data.hrbounds.1.trans_le hti.1
    have H:=ht hti
    rw [comparison_gradient_slope hp.ne'
      (laplaceComparisonStrength_pos Q.data.d Q.hlam t).ne'] at H
    convert H using 1
    dsimp [J,S,B,slope,g,radiusS,radiusB,comparisonBracket]
    ring
  have hpm:MonotoneOn slope (Ioc Q.data.rmin 1):=by
    intro s hs t ht hst
    dsimp [slope,g]
    rw [laplaceComparisonStrength_logSlope Q.data.hd.ne' Q.hlam.ne',
      laplaceComparisonStrength_logSlope Q.data.hd.ne' Q.hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hst Q.hlam.le) (pow_nonneg Q.data.hd.le _))
  have hpb t (_ht:t∈Ioc Q.data.rmin 1):slope t∈Icc (0:ℝ) 1:=by
    have H:=laplaceComparisonStrength_logSlope_mem Q.data.hd.ne' Q.hlam.ne' t
    exact ⟨H.1,H.2.le⟩
  have hSr:MonotoneOn S (Ioc Q.data.rmin 1):=hmom.1.mono Ioc_subset_Icc_self
  have hS0 t (ht:t∈Ioc Q.data.rmin 1):0≤S t:=
    (hmom.2.2 t (Ioc_subset_Icc_self ht)).1.1
  have hB2 t (ht:t∈Ioc Q.data.rmin 1):(S t)^2≤B t:=
    (hmom.2.2 t (Ioc_subset_Icc_self ht)).2.1
  have hac:AbsolutelyContinuousOnInterval P.H l z:=P.hH.mono (by
    simpa only [uIcc_of_le Q.data.hr,uIcc_of_le (hr.1.trans hr.2).le] using hsub)
  have hDsub:=hDp.mono (fun t ht hti=>ht (hsub hti))
  exact cap_S_le_right (S:=S) (B:=B) (Q.data.hrbounds.1.le.trans hl)
    hr hac (fun t ht=>hJ t (hsub ht)) hDsub hright hneg
    (fun t ht=>hpb t (hsubo ht)) (hSr.mono hsubo)
    (fun t ht=>hS0 t (hsubo ht)) (fun t ht=>hB2 t (hsubo ht))

theorem Potential.initial_cap_point_squared_mismatch (P:Q.Potential)
    {z r v:ℝ} (hz:z≤1) (hr:r∈Ioo Q.data.rmin z)
    (hnegative:P.H r<0) (hright:P.H z=0 ∨ z=1)
    (hwidth:z-Q.data.rmin≤v) (hv:0≤v):
    (Q.radiusS r-r)^2≤(Q.data.rmin+v)^2 := by
  have hri:r∈Icc Q.data.rmin 1:=
    ⟨hr.1.le,hr.2.le.trans hz⟩
  have hS0:= (Q.radius_moments.2.2 r hri).1.1
  have hSr:Q.radiusS r≤z:=by
    rcases hright with hc|he
    · exact P.cap_point_mean_le_right le_rfl hz hr hc hnegative
    · rw [he]
      exact (Q.radius_moments.2.2 r hri).1.2
  have hr0:=Q.data.hrbounds.1.le
  have hupper:z≤Q.data.rmin+v:=by linarith only [hwidth]
  have habs:|Q.radiusS r-r|≤Q.data.rmin+v:=
    abs_le.mpr ⟨by linarith only [hS0,hr.2,hupper],
      by linarith only [hSr,hr.1,hr0,hupper]⟩
  have H:=pow_le_pow_left₀ (abs_nonneg (Q.radiusS r-r)) habs 2
  simpa only [sq_abs] using H

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonActualHighWallThetaZeroCapCoverGeometry
public import ComparisonActualHighWallThetaZeroInitialCapOscillation
public import ComparisonActualHighOnlyCapOscillation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  {Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
  {P:Q.Potential} (c:ShiftedCapInterval Q P)

theorem interior_radiusS_increment
    (hN:1≤Q.data.N) (hlog:1≤Real.log Q.data.N) (hnd:1/Q.data.N≤Q.data.d)
    (hleft:P.H c.left=0) (hright:P.H c.right=0 ∨ c.right=1)
    {s t:ℝ} (hs:s∈Ioo c.left c.right) (ht:t∈Ioo c.left c.right)
    (hst:s≤t):
    Q.radiusS t-Q.radiusS s≤9*Real.log Q.data.N*(c.right-c.left) := by
  let w:=Q.data
  let g:=laplaceComparisonStrength w.d Q.lam
  let p:=comparisonLogSlope g
  let κ:=((1:ℝ)/3)/Real.log w.N
  let J:=fun r=>Q.controlFactor r*g r
  have hκ:0<κ:=div_pos (by norm_num) (by linarith)
  have hsub:Icc c.left c.right⊆Icc w.rmin 1:=Icc_subset_Icc c.hleft c.hright
  have hJ (r:ℝ) (_hr:r∈Icc c.left c.right):0<J r:=
    mul_pos (inverseControlFactor_pos _ _ r) (laplaceComparisonStrength_pos w.d Q.hlam r)
  have hDp:∀ᵐr,r∈Icc c.left c.right→HasDerivAt P.H
      (J r*comparisonBracket (p r) r (Q.radiusS r) (Q.radiusB r)) r:=by
    filter_upwards [P.hD] with r hdr hr
    have hrpos:0<r:=w.hrbounds.1.trans_le (hsub hr).1
    have hh:=hdr (hsub hr)
    rw [comparison_gradient_slope hrpos.ne'
      (laplaceComparisonStrength_pos w.d Q.hlam r).ne'] at hh
    convert hh using 1
    dsimp only [J,p,radiusS,radiusB,comparisonBracket]
    ring
  have hpm:MonotoneOn p (Icc w.rmin 1):=by
    intro r hr t ht hrt
    dsimp only [p,g]
    rw [laplaceComparisonStrength_logSlope w.hd.ne' Q.hlam.ne',
      laplaceComparisonStrength_logSlope w.hd.ne' Q.hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt Q.hlam.le) (pow_nonneg w.hd.le _))
  have hpb (r:ℝ) (hr:r∈Icc w.rmin 1):p r∈Icc (0:ℝ) (1-κ):=by
    refine ⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' Q.hlam.ne' r).1,?_⟩
    have HH:=laplaceComparisonStrength_uniform_slope hN hlog w.hd hnd
      Q.hlam Q.hld ⟨w.hrbounds.1.le.trans hr.1,hr.2⟩
    dsimp only [κ,p,g]
    linarith
  have hmom:=Q.radius_moments
  have hac:AbsolutelyContinuousOnInterval P.H c.left c.right:=P.hH.mono (by
    simpa only [uIcc_of_le Q.data.hr,uIcc_of_le c.hlt.le] using hsub)
  have hconstant:3/κ=9*Real.log w.N:=by dsimp only [κ];field_simp;ring
  rcases hright with hzH|hz1
  · have hi:=cap_interior_increment (w.hrbounds.1.le.trans c.hleft)
      hs ht hst hκ hac hJ hDp hleft hzH (c.negative s hs) (c.negative t ht)
      (hpm.mono (Ioo_subset_Icc_self.trans hsub))
      (fun r hr=>hpb r (hsub (Ioo_subset_Icc_self hr)))
      (hmom.1.mono (Ioo_subset_Icc_self.trans hsub))
      (hmom.2.1.mono (Ioo_subset_Icc_self.trans hsub))
      (fun r hr=>(hmom.2.2 r (hsub (Ioo_subset_Icc_self hr))).1.1)
      (fun r hr=>(hmom.2.2 r (hsub (Ioo_subset_Icc_self hr))).2.1)
    have HH:=(le_div_iff₀ hκ).mpr
      (by nlinarith [hi]:(Q.radiusS t-Q.radiusS s)*κ≤3*(c.right-c.left))
    rw [←div_mul_eq_mul_div,hconstant] at HH
    exact HH
  · obtain ⟨l,hl,hgl⟩:=potential_negative_left_witness hs.1
      (hac.mono (by
        simp only [uIcc_of_le c.hlt.le,uIcc_of_le hs.1.le]
        exact Icc_subset_Icc le_rfl hs.2.le))
      (fun r hr=>hJ r ⟨hr.1,hr.2.trans hs.2.le⟩)
      (hDp.mono (fun r hr hri=>hr ⟨hri.1,hri.2.trans hs.2.le⟩))
      (by simpa only [hleft] using c.negative s hs)
    have hlI:l∈Icc w.rmin 1:=⟨c.hleft.trans hl.1.le,hl.2.le.trans (hs.2.le.trans c.hright)⟩
    have hsI:s∈Icc w.rmin 1:=⟨c.hleft.trans hs.1.le,hs.2.le.trans c.hright⟩
    have htI:t∈Icc w.rmin 1:=⟨c.hleft.trans ht.1.le,ht.2.le.trans c.hright⟩
    have h1I:(1:ℝ)∈Icc w.rmin 1:=⟨w.hr,le_rfl⟩
    have hp1:=hpb 1 h1I
    have hrightBracket:0≤comparisonBracket (p 1) 1 (Q.radiusS 1) (Q.radiusB 1):=by
      have hS1:=(hmom.2.2 1 h1I).1.2
      have hB1:=(hmom.2.2 1 h1I).2.2
      have he:comparisonBracket (p 1) 1 (Q.radiusS 1) (Q.radiusB 1)=
          2*(1-p 1)*(1-Q.radiusS 1)+(p 1)*(1-Q.radiusB 1):=by
        unfold comparisonBracket
        ring
      rw [he]
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hp1.2])) (by linarith))
        (mul_nonneg hp1.1 (by linarith))
    have hinc:=comparisonBracket_endpoint_increment_uniform
      (w.hrbounds.1.trans_le hlI.1) hlI.2 hκ (hpm hlI h1I hlI.2) hp1
      (hmom.2.2 l hlI).1.1 (hmom.2.2 1 h1I).1.1
      (hmom.2.2 l hlI).2.1 (hmom.2.2 1 h1I).2.1
      (hmom.2.1 hlI h1I hlI.2) hgl.le hrightBracket
    have hSl:=hmom.1 hlI hsI hl.2.le
    have hSt:=hmom.1 htI h1I htI.2
    have hcomp:κ*(Q.radiusS t-Q.radiusS s)≤3*(1-c.left):=by
      have HH:=mul_le_mul_of_nonneg_left
        (show Q.radiusS t-Q.radiusS s≤Q.radiusS 1-Q.radiusS l by linarith) hκ.le
      linarith [hl.1]
    have HH:=(le_div_iff₀ hκ).mpr
      (by nlinarith [hcomp]:(Q.radiusS t-Q.radiusS s)*κ≤3*(1-c.left))
    rw [←div_mul_eq_mul_div,hconstant,←hz1] at HH
    exact HH

theorem radiusS_increment_with_origin
    (hN:1≤Q.data.N) (hlog:1≤Real.log Q.data.N) (hnd:1/Q.data.N≤Q.data.d)
    (hleft:P.H c.left=0 ∨ c.left=Q.data.rmin)
    (hright:P.H c.right=0 ∨ c.right=1)
    {s t:ℝ} (hs:s∈Ioo c.left c.right) (ht:t∈Ioo c.left c.right) (hst:s≤t):
    Q.radiusS t-Q.radiusS s≤
      9*Real.log Q.data.N*(c.right-c.left)+
      (if c.left=Q.data.rmin then Q.data.rmin else 0) := by
  rcases hleft with hc|h0
  · have HH:=c.interior_radiusS_increment hN hlog hnd hc hright hs ht hst
    have hcharge:0≤(if c.left=Q.data.rmin then Q.data.rmin else 0):=by
      split_ifs
      · exact Q.data.hrbounds.1.le
      · exact le_rfl
    exact HH.trans (le_add_of_nonneg_right hcharge)
  · have HH:=c.initial_radiusS_increment h0 hright hs ht
    have hW:0≤c.right-c.left:=sub_nonneg.mpr c.hlt.le
    have H:=mul_le_mul_of_nonneg_right (show 1≤9*Real.log Q.data.N by linarith) hW
    rw [ite_eq_left h0]
    linarith only [HH,H]

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonActualHighWallCapCoverGeometry
public import ComparisonShiftedNativePhysicalConcentration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem controlFactor_pos
    (a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock) (r : ℝ) :
    0< a.controlFactor r := inverseControlFactor_pos _ _ _

namespace ShiftedCapInterval
variable {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)

theorem radiusS_increment
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (hleft : P.H c.left=0) (hright : P.H c.right=0 ∨ c.right=1)
    {s t : ℝ} (hs : s∈Ioo c.left c.right) (ht : t∈Ioo c.left c.right) (hst : s≤ t) :
    a.radiusS t-a.radiusS s≤9*Real.log a.data.N*(c.right-c.left) := by
  let w:=a.data
  let p:=comparisonLogSlope w.g
  let κ:=((1:ℝ)/3)/Real.log w.N
  let J:=fun r=>a.controlFactor r*w.g r
  have hκ : 0<κ:=div_pos (by norm_num) (by linarith)
  have hsub : Icc c.left c.right⊆Icc w.rmin 1:=Icc_subset_Icc c.hleft c.hright
  have hJ (r : ℝ) (_hr : r∈Icc c.left c.right) : 0< J r:=
    mul_pos (a.controlFactor_pos r) (laplaceComparisonStrength_pos w.d (sq_pos_of_pos w.hd) r)
  have hDp : ∀ᵐ r,r∈Icc c.left c.right→HasDerivAt P.H
      (J r*comparisonBracket (p r) r (a.radiusS r) (a.radiusB r)) r:=by
    filter_upwards [P.hD] with r hdr hr
    have hrpos : 0< r:=w.hrbounds.1.trans_le (hsub hr).1
    have hh:=hdr (hsub hr)
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos w.d
      (sq_pos_of_pos w.hd) r).ne'] at hh
    convert hh using 1
    dsimp only [J,p,radiusS,radiusB,comparisonBracket]
    ring
  have hpm : MonotoneOn p (Icc w.rmin 1):=by
    intro r hr t ht hrt
    dsimp only [p,ActualHighWallData.g]
    rw [laplaceComparisonStrength_logSlope w.hd.ne' (sq_pos_of_pos w.hd).ne',
      laplaceComparisonStrength_logSlope w.hd.ne' (sq_pos_of_pos w.hd).ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt (sq_nonneg _)) (pow_nonneg w.hd.le _))
  have hpb (r : ℝ) (hr : r∈Icc w.rmin 1) : p r∈Icc (0:ℝ) (1-κ):=by
    refine ⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' (sq_pos_of_pos w.hd).ne' r).1,?_⟩
    have HH:=laplaceComparisonStrength_uniform_slope hN hlog w.hd hnd
      (sq_pos_of_pos w.hd) le_rfl ⟨w.hrbounds.1.le.trans hr.1,hr.2⟩
    dsimp only [κ,p,ActualHighWallData.g]
    linarith
  have hmom:=a.radius_moments
  have hac : AbsolutelyContinuousOnInterval P.H c.left c.right:=P.hH.mono (by
    have H : Icc c.left c.right⊆Icc a.data.rmin 1:=hsub
    simpa only [uIcc_of_le a.data.hr,uIcc_of_le c.hlt.le] using H)
  have hconstant : 3/κ=9*Real.log w.N:=by dsimp only [κ];field_simp;ring
  rcases hright with hzH|hz1
  · have hi:=cap_interior_increment (w.hrbounds.1.le.trans c.hleft) hs ht hst hκ hac hJ hDp
      hleft hzH (c.negative s hs) (c.negative t ht)
      (hpm.mono (Ioo_subset_Icc_self.trans hsub))
      (fun r hr=>hpb r (hsub (Ioo_subset_Icc_self hr)))
      (hmom.1.mono (Ioo_subset_Icc_self.trans hsub))
      (hmom.2.1.mono (Ioo_subset_Icc_self.trans hsub))
      (fun r hr=>(hmom.2.2 r (hsub (Ioo_subset_Icc_self hr))).1.1)
      (fun r hr=>(hmom.2.2 r (hsub (Ioo_subset_Icc_self hr))).2.1)
    have HH:=(le_div_iff₀ hκ).mpr
      (by nlinarith [hi] : (a.radiusS t-a.radiusS s)*κ≤3*(c.right-c.left))
    rw [←div_mul_eq_mul_div,hconstant] at HH
    exact HH
  · obtain ⟨l,hl,hgl⟩:=potential_negative_left_witness hs.1
      (hac.mono (by
        simp only [uIcc_of_le c.hlt.le,uIcc_of_le hs.1.le]
        exact Icc_subset_Icc le_rfl hs.2.le))
      (fun r hr=>hJ r ⟨hr.1,hr.2.trans hs.2.le⟩)
      (hDp.mono (fun r hr hri=>hr ⟨hri.1,hri.2.trans hs.2.le⟩))
      (by simpa only [hleft] using c.negative s hs)
    have hlI : l∈Icc w.rmin 1:=⟨c.hleft.trans hl.1.le,hl.2.le.trans (hs.2.le.trans c.hright)⟩
    have hsI : s∈Icc w.rmin 1:=⟨c.hleft.trans hs.1.le,hs.2.le.trans c.hright⟩
    have htI : t∈Icc w.rmin 1:=⟨c.hleft.trans ht.1.le,ht.2.le.trans c.hright⟩
    have h1I : (1:ℝ)∈Icc w.rmin 1:=⟨w.hr,le_rfl⟩
    have hp1:=hpb 1 h1I
    have hrightBracket : 0≤ comparisonBracket (p 1) 1 (a.radiusS 1) (a.radiusB 1):=by
      have hS1:=(hmom.2.2 1 h1I).1.2
      have hB1:=(hmom.2.2 1 h1I).2.2
      have he : comparisonBracket (p 1) 1 (a.radiusS 1) (a.radiusB 1)=
          2*(1-p 1)*(1-a.radiusS 1)+(p 1)*(1-a.radiusB 1):=by
        unfold comparisonBracket
        ring
      rw [he]
      exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hp1.2])) (by linarith))
        (mul_nonneg hp1.1 (by linarith))
    have hinc:=comparisonBracket_endpoint_increment_uniform
      (w.hrbounds.1.trans_le hlI.1) hlI.2 hκ (hpm hlI h1I hlI.2) hp1
      (hmom.2.2 l hlI).1.1 (hmom.2.2 1 h1I).1.1
      (hmom.2.2 l hlI).2.1 (hmom.2.2 1 h1I).2.1
      (hmom.2.1 hlI h1I hlI.2) hgl.le hrightBracket
    have hSl:=hmom.1 hlI hsI hl.2.le
    have hSt:=hmom.1 htI h1I htI.2
    have hcomp : κ*(a.radiusS t-a.radiusS s)≤3*(1-c.left):=by
      have HH:=mul_le_mul_of_nonneg_left
        (show a.radiusS t-a.radiusS s≤ a.radiusS 1-a.radiusS l by linarith) hκ.le
      linarith [hl.1]
    have HH:=(le_div_iff₀ hκ).mpr
      (by nlinarith [hcomp] : (a.radiusS t-a.radiusS s)*κ≤3*(1-c.left))
    rw [←div_mul_eq_mul_div,hconstant,←hz1] at HH
    exact HH

end ShiftedCapInterval
end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

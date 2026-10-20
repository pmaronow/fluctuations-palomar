module

public import ComparisonActualHighOnlyCanonicalMassBudgets
public import ComparisonShiftedNativePhysicalConcentration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

namespace ShiftedCapInterval
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)

theorem radiusS_increment
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (hleft : P.H c.left=0) (hright : P.H c.right=0 ∨ c.right=1)
    {s t : ℝ} (hs : s∈Ioo c.left c.right) (ht : t∈Ioo c.left c.right) (hst : s≤ t) :
    a.radiusS t-a.radiusS s≤9*Real.log a.data.N*(c.right-c.left) := by
  let w:=a.data
  let g:=laplaceComparisonStrength w.d a.lam
  let p:=comparisonLogSlope g
  let κ:=((1:ℝ)/3)/Real.log w.N
  let J:=fun r=>a.controlFactor r*g r
  have hκ : 0<κ:=div_pos (by norm_num) (by linarith)
  have hsub : Icc c.left c.right⊆Icc (0:ℝ) 1:=Icc_subset_Icc c.hleft c.hright
  have hJ (r : ℝ) (_hr : r∈Icc c.left c.right) : 0< J r:=
    mul_pos (a.controlFactor_pos r) (laplaceComparisonStrength_pos w.d a.hlam r)
  have hDp : ∀ᵐ r,r∈Icc c.left c.right→HasDerivAt P.H
      (J r*comparisonBracket (p r) r (a.radiusS r) (a.radiusB r)) r:=by
    filter_upwards [P.hD,volume.ae_ne (0:ℝ)] with r hdr hr0 hr
    have hrpos : 0< r:=lt_of_le_of_ne (hsub hr).1 hr0.symm
    have hh:=hdr (hsub hr)
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos w.d
      a.hlam r).ne'] at hh
    convert hh using 1
    dsimp only [J,p,radiusS,radiusB,comparisonBracket]
    ring
  have hpm : MonotoneOn p (Icc (0:ℝ) 1):=by
    intro r hr t ht hrt
    dsimp only [p,g]
    rw [laplaceComparisonStrength_logSlope w.hd.ne' a.hlam.ne',
      laplaceComparisonStrength_logSlope w.hd.ne' a.hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt a.hlam.le) (pow_nonneg w.hd.le _))
  have hpb (r : ℝ) (hr : r∈Icc (0:ℝ) 1) : p r∈Icc (0:ℝ) (1-κ):=by
    refine ⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' a.hlam.ne' r).1,?_⟩
    have HH:=laplaceComparisonStrength_uniform_slope hN hlog w.hd hnd
      a.hlam a.hld ⟨hr.1,hr.2⟩
    dsimp only [κ,p,g]
    linarith
  have hmom:=a.radius_moments
  have hac : AbsolutelyContinuousOnInterval P.H c.left c.right:=P.hH.mono (by
    have H : Icc c.left c.right⊆Icc (0:ℝ) 1:=hsub
    simpa only [uIcc_of_le zero_le_one,uIcc_of_le c.hlt.le] using H)
  have hconstant : 3/κ=9*Real.log w.N:=by dsimp only [κ];field_simp;ring
  rcases hright with hzH|hz1
  · have hi:=cap_interior_increment c.hleft hs ht hst hκ hac hJ hDp
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
    have hlI : l∈Icc (0:ℝ) 1:=⟨c.hleft.trans hl.1.le,hl.2.le.trans (hs.2.le.trans c.hright)⟩
    have hsI : s∈Icc (0:ℝ) 1:=⟨c.hleft.trans hs.1.le,hs.2.le.trans c.hright⟩
    have htI : t∈Icc (0:ℝ) 1:=⟨c.hleft.trans ht.1.le,ht.2.le.trans c.hright⟩
    have h1I : (1:ℝ)∈Icc (0:ℝ) 1:=⟨zero_le_one,le_rfl⟩
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
      (c.hleft.trans_lt hl.1) hlI.2 hκ (hpm hlI h1I hlI.2) hp1
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

theorem radiusS_increment_all
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (hleft : P.H c.left=0 ∨ c.left=0) (hright : P.H c.right=0 ∨ c.right=1)
    {s t : ℝ} (hs : s∈Ioo c.left c.right) (ht : t∈Ioo c.left c.right) (hst : s≤t) :
    a.radiusS t-a.radiusS s≤9*Real.log a.data.N*(c.right-c.left) := by
  rcases hleft with hc|hz
  · exact c.radiusS_increment hN hlog hnd hc hright hs ht hst
  · have hS0 := (a.radius_moments.2.2 s ⟨c.hleft.trans hs.1.le,hs.2.le.trans c.hright⟩).1.1
    have hSt : a.radiusS t≤c.right := by
      rcases hright with hc|h1
      · exact P.cap_point_mean_le_right c.hleft c.hright ht hc (c.negative t ht)
      · rw [h1]
        exact (a.radius_moments.2.2 t ⟨c.hleft.trans ht.1.le,ht.2.le.trans c.hright⟩).1.2
    have hlen : 0≤c.right-c.left := sub_nonneg.mpr c.hlt.le
    have H:=mul_le_mul_of_nonneg_right (show 1≤9*Real.log a.data.N by linarith) hlen
    rw [hz,sub_zero] at *
    linarith

theorem radiusS_increment_canonical
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (hleft : P.H c.left=0 ∨ c.left=0) (hright : P.H c.right=0 ∨ c.right=1)
    {s t : ℝ} (hs : s∈Ioo c.left c.right) (ht : t∈Ioo c.left c.right) (hst : s≤t) :
    a.radiusS t-a.radiusS s≤a.canonicalMassDiameter := by
  have H:=c.radiusS_increment_all hN hlog hnd hleft hright hs ht hst
  have htvl:=(P.cap_interval_travel c.hleft c.hlt.le c.hright c.negative).2.1
  exact H.trans (mul_le_mul_of_nonneg_left htvl (show 0≤9*Real.log a.data.N by linarith))

end ShiftedCapInterval
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

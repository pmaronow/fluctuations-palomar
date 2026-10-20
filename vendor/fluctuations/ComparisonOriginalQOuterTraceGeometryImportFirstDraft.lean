module

public import ComparisonActualHighWallThetaZeroSelectedRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem outer_trace_import_first_carrier_le_group_draft
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {lo v : ℝ} (houter : 2*cu*(Az+1)*Q.xs ≤ lo)
    (hgroup : (cl/(4*cu))*lo ≤ v) :
    Q.xs ≤ (2/cl)*v := by
  have hratio : 0 ≤ cl/(4*cu) := by positivity
  have H := mul_le_mul_of_nonneg_left houter hratio
  have hAz1 : 1 ≤ Az+1 := by linarith
  have hxs : 0 ≤ Q.xs := Q.hxs.le
  have hbound : (cl/2)*Q.xs ≤ v := by
    have HH : (cl/2)*Q.xs ≤ (cl/(4*cu))*(2*cu*(Az+1)*Q.xs) := by
      have Hfac := mul_le_mul_of_nonneg_left hAz1
        (show 0 ≤ (cl/2)*Q.xs by positivity)
      have Heq : (cl/(4*cu))*(2*cu*(Az+1)*Q.xs) =
          (cl/2)*((Az+1)*Q.xs) := by
        field_simp [hcu.ne']
        ring
      rw [Heq]
      nlinarith only [Hfac]
    exact HH.trans (H.trans hgroup)
  have htwo : 0 < 2/cl := by positivity
  have Hmul := mul_le_mul_of_nonneg_left hbound htwo.le
  have Heq : (2/cl)*((cl/2)*Q.xs)=Q.xs := by
    field_simp [hcl.ne']
  rw [Heq] at Hmul
  exact Hmul

theorem outer_trace_import_first_endpoint_strength_le_draft
    (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {K H v : ℝ} (hK : 1 ≤ K) (hH : 0 ≤ H)
    (hv : v ∈ Ioc (0:ℝ) 1)
    (hxs : Q.xs ≤ H*v) :
    let z := min (K*v) 1
    let J := max 1 ((Az+1/cl)*(H+K))
    laplaceComparisonStrength Q.data.d Q.lam v ≤
      J*laplaceComparisonStrength Q.data.d Q.lam
        (Q.shiftedNativeModel.R z) := by
  let z := min (K*v) 1
  let r := Q.shiftedNativeModel.R z
  let J := max 1 ((Az+1/cl)*(H+K))
  have hvKv : v ≤ K*v := by nlinarith [hv.1,hK]
  have hz : z ∈ Ioc (0:ℝ) 1 :=
    ⟨hv.1.trans_le (le_min hvKv hv.2),min_le_right _ _⟩
  have hzKv : z ≤ K*v := min_le_left _ _
  have hC : 0 ≤ Az+1/cl := by positivity
  have hJ : 1 ≤ J := le_max_left _ _
  have hr : 0 < r :=
    Q.data.hrbounds.1.trans_le (Q.shiftedNativeModel.R_bounds z).1
  have hrI : r ∈ Icc (0:ℝ) 1 :=
    ⟨hr.le,(Q.shiftedNativeModel.R_bounds z).2⟩
  have hsource := Q.inverse_radius_le_source_mass hcl hAz
    ⟨hz.1.le,hz.2⟩
  have hrv : r ≤ J*v := by
    have hmass : Q.xs+z ≤ (H+K)*v := by
      linarith only [hxs,hzKv]
    have hbase := mul_le_mul_of_nonneg_left hmass hC
    have hfactor := mul_le_mul_of_nonneg_right
      (le_max_right (1:ℝ) ((Az+1/cl)*(H+K))) hv.1.le
    calc
      r = Q.sweepRadius z := Q.shiftedNativeModel_radius z
      _ ≤ (Az+1/cl)*(Q.xs+z) := hsource
      _ ≤ (Az+1/cl)*((H+K)*v) := hbase
      _ = ((Az+1/cl)*(H+K))*v := by ring
      _ ≤ J*v := hfactor
  have hshape := laplaceComparisonStrength_monotonicities
    Q.data.hd.ne' Q.hlam (show (0:ℝ) ≤ 0 by norm_num)
  have her : 0 ≤ laplaceComparisonStrength Q.data.d Q.lam r :=
    (laplaceComparisonStrength_pos Q.data.d Q.hlam r).le
  by_cases hvr : v ≤ r
  · have Hshape := hshape.2 ⟨hv.1.le,hv.2⟩ hrI hvr
    apply le_of_mul_le_mul_right (a:=v) _ hv.1
    calc
      laplaceComparisonStrength Q.data.d Q.lam v*v ≤
          laplaceComparisonStrength Q.data.d Q.lam r*r := Hshape
      _ ≤ laplaceComparisonStrength Q.data.d Q.lam r*(J*v) :=
        mul_le_mul_of_nonneg_left hrv her
      _ = (J*laplaceComparisonStrength Q.data.d Q.lam r)*v := by ring
  · have Hshape := hshape.1 hrI ⟨hv.1.le,hv.2⟩ (le_of_not_ge hvr)
    exact Hshape.trans (by
      calc
        laplaceComparisonStrength Q.data.d Q.lam r =
            1*laplaceComparisonStrength Q.data.d Q.lam r := by ring
        _ ≤ J*laplaceComparisonStrength Q.data.d Q.lam r :=
          mul_le_mul_of_nonneg_right hJ her)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

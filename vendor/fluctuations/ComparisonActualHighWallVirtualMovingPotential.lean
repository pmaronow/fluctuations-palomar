module

public import ComparisonActualHighWallVirtualFactor
public import ComparisonActualHighWallVirtualContactData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.actual_virtual_moving_lipschitz
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (hcu : 0 ≤ cu) (hAz : 0 ≤ Az)
    {B ref c KG : ℝ} (hB : 0 ≤ B) (hc : 0 < c)
    (href : ref∈Icc M.data.rmin (M.xs*B)) (hphysical : M.xs*B ≤ 1)
    (hmass : c*M.xs ≤ M.alpha.val.val ref) (hKG : 0 ≤ KG)
    (hgradient : ∀t∈Icc (ref/M.xs) B,|M.actualVirtualScaledGradient t| ≤ KG) :
    LipschitzOnWith ((((c+cu*(B+Az)+1)/c)^2*KG).toNNReal)
      (p.actualVirtualScaledPotential ref) (Icc (ref/M.xs) B) := by
  let K := (c+cu*(B+Az)+1)/c
  have Hfactor := M.actual_virtual_moving_factor_data hcu hAz hB hc href hphysical hmass
  have hleft : ref/M.xs ≤ B := (div_le_iff₀ M.hxs).mpr
    (by simpa only [mul_comm] using href.2)
  have hcancel : M.xs*(ref/M.xs)=ref := by field_simp [M.hxs.ne']
  have hsub : Icc (M.xs*(ref/M.xs)) (M.xs*B) ⊆ Icc M.data.rmin 1 := by
    rw [hcancel]
    exact Icc_subset_Icc href.1 hphysical
  have hAC : AbsolutelyContinuousOnInterval p.H (M.xs*(ref/M.xs)) (M.xs*B) :=
    p.hH.mono (by
      simpa only [uIcc_of_le (mul_le_mul_of_nonneg_left hleft M.hxs.le),
        uIcc_of_le M.data.hr] using hsub)
  apply comparison_virtual_scaled_potential_lipschitz M.hxs
    (M.actual_controlFactor_pos ref)
    hleft (sq_nonneg K) hKG p.H M.controlFactor
    (radiusComparisonGradient M.data.g M.alpha.val.val
      (orderedPathS (n+1) M.bf M.hf) (orderedPathB (n+1) M.bf M.hf)) hAC
  · filter_upwards [p.hD] with r hr hri
    exact hr (hsub hri)
  · intro r hr
    have hleftR : ref ≤ r := by simpa only [hcancel] using hr.1
    have ht : r/M.xs∈Icc (ref/M.xs) B :=
      ⟨div_le_div_of_nonneg_right hleftR M.hxs.le,
        (div_le_iff₀ M.hxs).mpr (by simpa only [mul_comm] using hr.2)⟩
    have H := (Hfactor.2.2.2 (r/M.xs) ht.2).2
    rw [M.actual_virtual_moving_factor_eq_scaled ref ht.1] at H
    have hcancelR : M.xs*(r/M.xs)=r := by field_simp [M.hxs.ne']
    change |M.controlFactor r/M.controlFactor ref| ≤ K^2
    rw [abs_of_pos (div_pos (M.actual_controlFactor_pos r)
      (M.actual_controlFactor_pos ref))]
    simpa only [actualVirtualScaledFactor,hcancelR] using H
  · intro r hr
    have hleftR : ref ≤ r := by simpa only [hcancel] using hr.1
    have ht : r/M.xs∈Icc (ref/M.xs) B :=
      ⟨div_le_div_of_nonneg_right hleftR M.hxs.le,
        (div_le_iff₀ M.hxs).mpr (by simpa only [mul_comm] using hr.2)⟩
    have hcancelR : M.xs*(r/M.xs)=r := by field_simp [M.hxs.ne']
    simpa only [actualVirtualScaledGradient,hcancelR] using hgradient (r/M.xs) ht

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

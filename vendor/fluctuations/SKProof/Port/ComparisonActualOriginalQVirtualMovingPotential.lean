module

public import SKProof.Port.ComparisonActualOriginalQVirtualControl
public import SKProof.Port.ComparisonActualOriginalQVirtualContactData
public import SKProof.Port.ComparisonActualOriginalQAllCapMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.actual_virtual_moving_lipschitz
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (hcu : 0 ≤ cu) (hAz : 0 ≤ Az)
    {B ref c KG : ℝ} (hB : 0 ≤ B) (hc : 0 < c)
    (href : ref∈Icc M.data.rmin (M.xs*B)) (hphysical : M.xs*B ≤ 1)
    (hmass : c*M.xs ≤ M.alpha.val.val ref) (hKG : 0 ≤ KG)
    (hgradient : ∀t∈Icc (ref/M.xs) B,|M.actualVirtualScaledGradient t| ≤ KG) :
    LipschitzOnWith ((((c+cu*(B+Az)+1)/c)^2*KG).toNNReal)
      (p.actualVirtualScaledPotential ref) (Icc (ref/M.xs) B) := by
  let K := (c+cu*(B+Az)+1)/c
  have Hfactor := M.actual_virtual_moving_factor_data hcu hAz hB hc href hphysical hmass
  have hleft : ref/M.xs ≤ B := (div_le_iff₀ M.hxs).mpr (by simpa only [mul_comm] using href.2)
  have hcancel : M.xs*(ref/M.xs)=ref := by field_simp [M.hxs.ne']
  have hsub : Icc (M.xs*(ref/M.xs)) (M.xs*B) ⊆ Icc M.data.rmin 1 := by
    rw [hcancel]
    exact Icc_subset_Icc href.1 hphysical
  have hAC : AbsolutelyContinuousOnInterval p.H (M.xs*(ref/M.xs)) (M.xs*B) :=
    p.hH.mono (by
      simpa only [uIcc_of_le (mul_le_mul_of_nonneg_left hleft M.hxs.le), uIcc_of_le M.data.hr] using hsub)
  apply comparison_virtual_scaled_potential_lipschitz M.hxs (M.actual_control_factor_pos ref)
    hleft (sq_nonneg K) hKG p.H M.controlFactor
    (radiusComparisonGradient (laplaceComparisonStrength M.data.d M.lam)
      M.alpha.val.val (orderedPathS (n+1) M.sweepBf M.sweepHf) (orderedPathB (n+1) M.sweepBf M.sweepHf)) hAC
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
    rw [abs_of_pos (div_pos (M.actual_control_factor_pos r) (M.actual_control_factor_pos ref))]
    simpa only [actualVirtualScaledFactor,hcancelR] using H
  · intro r hr
    have hleftR : ref ≤ r := by simpa only [hcancel] using hr.1
    have ht : r/M.xs∈Icc (ref/M.xs) B :=
      ⟨div_le_div_of_nonneg_right hleftR M.hxs.le,
        (div_le_iff₀ M.hxs).mpr (by simpa only [mul_comm] using hr.2)⟩
    have hcancelR : M.xs*(r/M.xs)=r := by field_simp [M.hxs.ne']
    simpa only [actualVirtualScaledGradient,hcancelR] using hgradient (r/M.xs) ht

theorem Potential.actual_virtual_scaled_lower_of_lipschitz
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {ref B t : ℝ} {L : ℝ≥0} (href : M.data.rmin ≤ ref)
    (hphysical : M.xs*B ≤ 1)
    (hLip : LipschitzOnWith L (p.actualVirtualScaledPotential ref) (Icc (ref/M.xs) B))
    (ht : t∈Icc (ref/M.xs) B) (hroom : t+2*M.cavityCapTravel/M.xs ≤ B) :
    -((L:ℝ)*(2*M.cavityCapTravel/M.xs)) ≤ p.actualVirtualScaledPotential ref t := by
  have hden : 0 < M.xs^4*M.controlFactor ref := mul_pos (pow_pos M.hxs 4) (M.actual_control_factor_pos ref)
  have herror : 0 ≤ (L:ℝ)*(2*M.cavityCapTravel/M.xs) := by
    have H : 0 ≤ M.cavityCapTravel := p.toVirtualContactData.travel_pos.le
    exact mul_nonneg L.coe_nonneg (div_nonneg (mul_nonneg (by norm_num) H) M.hxs.le)
  by_cases hneg : p.H (M.xs*t) < 0
  · have htr : M.data.rmin ≤ M.xs*t := href.trans (by
      have H := mul_le_mul_of_nonneg_left ht.1 M.hxs.le
      simpa only [mul_div_cancel₀ _ M.hxs.ne'] using H)
    have hroomR : M.xs*t+2*M.cavityCapTravel ≤ M.xs*B := by
      have H := mul_le_mul_of_nonneg_left hroom M.hxs.le
      have he : M.xs*(t+2*M.cavityCapTravel/M.xs)=M.xs*t+2*M.cavityCapTravel := by
        field_simp [M.hxs.ne']
      rwa [he] at H
    obtain ⟨z,hz,hzero⟩ := p.toVirtualContactData.negative_point_near_contact
      htr (hroomR.trans hphysical) hneg
    change z∈Icc (M.xs*t) (M.xs*t+2*M.cavityCapTravel) at hz
    change p.H z=0 at hzero
    have hzt : t ≤ z/M.xs := (le_div_iff₀ M.hxs).mpr (by simpa only [mul_comm] using hz.1)
    have hzB : z/M.xs ≤ B := (div_le_iff₀ M.hxs).mpr
      (by simpa only [mul_comm] using hz.2.trans hroomR)
    have hzupper : z/M.xs ≤ t+2*M.cavityCapTravel/M.xs :=
      (div_le_div_of_nonneg_right hz.2 M.hxs.le).trans_eq (by field_simp [M.hxs.ne'])
    have hcancel : M.xs*(z/M.xs)=z := by field_simp [M.hxs.ne']
    have hzeroScaled : p.actualVirtualScaledPotential ref (z/M.xs)=0 := by
      simp only [Potential.actualVirtualScaledPotential,hcancel,hzero,zero_div]
    have H := hLip.dist_le_mul t ht (z/M.xs) ⟨ht.1.trans hzt,hzB⟩
    rw [hzeroScaled,Real.dist_eq,sub_zero,Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hzt)] at H
    have Hdist : -(t-z/M.xs) ≤ 2*M.cavityCapTravel/M.xs := by linarith only [hzupper]
    exact (abs_le.mp (H.trans (mul_le_mul_of_nonneg_left Hdist L.coe_nonneg))).1
  · exact (neg_nonpos.mpr herror).trans (div_nonneg (le_of_not_gt hneg) hden.le)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonActualHighWallVirtualMovingPotential
public import ComparisonActualHighWallContactGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.actual_virtual_scaled_lower_of_lipschitz
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {ref B t : ℝ} {L : ℝ≥0}
    (href : M.data.rmin ≤ ref)
    (hphysical : M.xs*B ≤ 1)
    (hLip : LipschitzOnWith L (p.actualVirtualScaledPotential ref)
      (Icc (ref/M.xs) B))
    (ht : t∈Icc (ref/M.xs) B)
    (hroom : t+2*M.cavityCapTravel/M.xs ≤ B) :
    -((L:ℝ)*(2*M.cavityCapTravel/M.xs)) ≤
      p.actualVirtualScaledPotential ref t := by
  have hden : 0 < M.xs^4*M.controlFactor ref :=
    mul_pos (pow_pos M.hxs 4) (M.actual_controlFactor_pos ref)
  have herror : 0 ≤ (L:ℝ)*(2*M.cavityCapTravel/M.xs) := by
    have H : 0 ≤ M.cavityCapTravel := (p.toVirtualContactData).travel_pos.le
    exact mul_nonneg L.coe_nonneg (div_nonneg (mul_nonneg (by norm_num) H) M.hxs.le)
  by_cases hneg : p.H (M.xs*t) < 0
  · have ht0 : 0 ≤ t := (div_nonneg (M.data.hrbounds.1.le.trans href) M.hxs.le).trans ht.1
    have hroomR : M.xs*t+2*M.cavityCapTravel ≤ M.xs*B := by
      have H := mul_le_mul_of_nonneg_left hroom M.hxs.le
      have he : M.xs*(t+2*M.cavityCapTravel/M.xs)=M.xs*t+2*M.cavityCapTravel := by
        field_simp [M.hxs.ne']
      rwa [he] at H
    have hrefT : ref ≤ M.xs*t := by
      have H := mul_le_mul_of_nonneg_left ht.1 M.hxs.le
      simpa only [mul_div_cancel₀ _ M.hxs.ne'] using H
    have hwork : M.data.rmin ≤ M.xs*t := href.trans hrefT
    obtain ⟨z,hz,hzero⟩ := (p.toVirtualContactData).negative_point_near_contact
      hwork (hroomR.trans hphysical) hneg
    change z∈Icc (M.xs*t) (M.xs*t+2*M.cavityCapTravel) at hz
    change p.H z=0 at hzero
    have hzt : t ≤ z/M.xs := (le_div_iff₀ M.hxs).mpr
      (by simpa only [mul_comm] using hz.1)
    have hzB : z/M.xs ≤ B := (div_le_iff₀ M.hxs).mpr
      (by simpa only [mul_comm] using hz.2.trans hroomR)
    have hzupper : z/M.xs ≤ t+2*M.cavityCapTravel/M.xs :=
      (div_le_div_of_nonneg_right hz.2 M.hxs.le).trans_eq
        (by field_simp [M.hxs.ne'])
    have hcancel : M.xs*(z/M.xs)=z := by field_simp [M.hxs.ne']
    have hzeroScaled : p.actualVirtualScaledPotential ref (z/M.xs)=0 := by
      simp only [Potential.actualVirtualScaledPotential,hcancel,hzero,zero_div]
    have H := hLip.dist_le_mul t ht (z/M.xs) ⟨ht.1.trans hzt,hzB⟩
    rw [hzeroScaled,Real.dist_eq,sub_zero,Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hzt)] at H
    have Hdist : -(t-z/M.xs) ≤ 2*M.cavityCapTravel/M.xs := by linarith only [hzupper]
    exact (abs_le.mp (H.trans (mul_le_mul_of_nonneg_left Hdist L.coe_nonneg))).1
  · exact (neg_nonpos.mpr herror).trans (div_nonneg (le_of_not_gt hneg) hden.le)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

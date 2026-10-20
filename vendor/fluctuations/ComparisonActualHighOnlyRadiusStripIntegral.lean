module

public import ComparisonActualHighOnlyRadiusStripGeometry
public import ComparisonActualHighOnlyRadiusSingleCutIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_radius_target_strip_finite_measure
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (c C : ℝ) :
    IsFiniteMeasure (volume.restrict (M.actualRadiusTargetStrip c C)) := by
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  exact (measure_mono (show M.actualRadiusTargetStrip c C ⊆ Icc (0:ℝ) 1 from
    fun _ hr=>⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)).trans_lt
    (isCompact_Icc.measure_lt_top (μ:=volume))

theorem actual_radius_target_strip_measure_le
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (c C : ℝ) (hC : 0 ≤ C) :
    volume.real (M.actualRadiusTargetStrip c C) ≤ C*M.xs := by
  have H := measureReal_mono (μ:=volume)
    (show M.actualRadiusTargetStrip c C ⊆ Icc (0:ℝ) (C*M.xs) from
      fun _ hr=>⟨hr.1.1,hr.1.2.trans (min_le_left _ _)⟩)
    (isCompact_Icc.measure_lt_top (μ:=volume)).ne
  simpa only [Real.volume_real_Icc_of_le (mul_nonneg hC M.hxs.le),sub_zero] using H

theorem actual_radius_target_strip_integrable
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (c C : ℝ) :
    IntegrableOn M.cavityRadiusPointDefect (M.actualRadiusTargetStrip c C) := by
  have hi : IntegrableOn M.cavityRadiusPointDefect (Icc (0:ℝ) 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact M.cavityRadiusPointDefect_integrableOn le_rfl le_rfl
  exact hi.mono_set (fun r hr=>⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)

theorem actual_radius_target_strip_integral_nonneg
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (c C : ℝ) :
    0 ≤ ∫r in M.actualRadiusTargetStrip c C,M.cavityRadiusPointDefect r := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (M.actual_radius_target_strip_measurable c C)] with r hr
  exact M.cavityRadiusPointDefect_nonneg ⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩

theorem actual_radius_target_strip_integral_le
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (c C : ℝ)
    (ha : 0 ≤ M.actualRadiusStripLower c) (hz : M.actualRadiusStripUpper c C ≤ 1) :
    (∫r in M.actualRadiusTargetStrip c C,M.cavityRadiusPointDefect r) ≤
      M.cavityRadiusDefect (M.actualRadiusStripLower c) (M.actualRadiusStripUpper c C) := by
  have hi : IntegrableOn M.cavityRadiusPointDefect
      (Icc (M.actualRadiusStripLower c) (M.actualRadiusStripUpper c C)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact M.cavityRadiusPointDefect_integrableOn ha hz
  have H := setIntegral_mono_set hi (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact M.cavityRadiusPointDefect_nonneg ⟨ha.trans hr.1,hr.2.trans hz⟩)
    (Eventually.of_forall (M.actual_radius_target_strip_subset c C))
  rw [integral_Icc_eq_integral_Ioo] at H
  exact H

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeLocalMassBandAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

theorem native_actual_quantile_mem_interior (m : NativeBandModel) {u : ℝ}
    (hu : u∈Ioo (0:ℝ) 1) : m.R u∈Ioo (0:ℝ) 1 := by
  have hR0 : m.R 0=0 := by
    simpa only [m.alpha.property.1] using comparisonSweepQuantile_inverse m.hc m.hk m.hkc m.hm m.hM
      m.alpha (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
  have hR1 : m.R 1=1 := by
    simpa only [m.alpha.property.2.1] using comparisonSweepQuantile_inverse m.hc m.hk m.hkc m.hm m.hM
      m.alpha (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num)
  have hm := native_mass_slice_quantile_mem m (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
    (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num) (Ioo_subset_Icc_self hu)
  change (m.R u∈Ioo (m.R 0) (m.R 1)) ↔ u∈Ioo (0:ℝ) 1 at hm
  rw [hR0,hR1] at hm
  exact hm.mpr hu

theorem native_actual_local_thermal_sign_partition (m : NativeBandModel)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫u in 0..1,A.indicator (fun _=>1) (m.R u)*m.thermal u) =
      (∫u in 0..1,(A∩(nativeNegativeSet m∪nativeActualContactSet m)).indicator
        (fun _=>1) (m.R u)*m.thermal u)+
      (∫u in 0..1,(A∩nativeActualPositiveSet m).indicator (fun _=>1) (m.R u)*m.thermal u) := by
  have hn := nativeActualThermal_mask_integrable m _
    (hA.inter ((nativeNegativeSet_open m).measurableSet.union (nativeActualContactSet_measurable m)))
  have hp := nativeActualThermal_mask_integrable m _ (hA.inter (nativeActualPositiveSet_measurable m))
  rw [←intervalIntegral.integral_add hn hp]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (1:ℝ)] with u hune hu
  have hu : u∈Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hu
  have hr := native_actual_quantile_mem_interior m ⟨hu.1,lt_of_le_of_ne hu.2 hune⟩
  have hri : m.R u∈Icc (0:ℝ) 1 := Ioo_subset_Icc_self hr
  have hnon : (m.R u∈nativeNegativeSet m∪nativeActualContactSet m) ↔ m.H (m.R u)≤0 := by
    constructor
    · rintro (h|h)
      · exact h.2.le
      · exact h.2.le
    · intro h
      rcases lt_or_eq_of_le h with hneg|hz
      · exact Or.inl ⟨hr,hneg⟩
      · exact Or.inr ⟨hri,hz⟩
  have hpos : (m.R u∈nativeActualPositiveSet m) ↔ 0 < m.H (m.R u) :=
    ⟨fun h=>h.2,fun h=>⟨hri,h⟩⟩
  by_cases ha : m.R u∈A
  · by_cases hH : 0 < m.H (m.R u)
    · have hp : m.R u∈A∩nativeActualPositiveSet m := ⟨ha,hpos.mpr hH⟩
      have hn : m.R u∉A∩(nativeNegativeSet m∪nativeActualContactSet m) :=
        fun h=>not_le_of_gt hH (hnon.mp h.2)
      simp only [indicator_of_mem ha,indicator_of_mem hp,indicator_of_notMem hn,
        one_mul,zero_mul,zero_add]
    · have hn : m.R u∈A∩(nativeNegativeSet m∪nativeActualContactSet m) :=
        ⟨ha,hnon.mpr (le_of_not_gt hH)⟩
      have hp : m.R u∉A∩nativeActualPositiveSet m := fun h=>hH (hpos.mp h.2)
      simp only [indicator_of_mem ha,indicator_of_mem hn,indicator_of_notMem hp,
        one_mul,zero_mul,add_zero]
  · have hn : m.R u∉A∩(nativeNegativeSet m∪nativeActualContactSet m) := fun h=>ha h.1
    have hp : m.R u∉A∩nativeActualPositiveSet m := fun h=>ha h.1
    simp only [indicator_of_notMem ha,indicator_of_notMem hn,indicator_of_notMem hp,zero_mul,add_zero]

end OAI.SKFluctuations.LaplaceWindowFormalization

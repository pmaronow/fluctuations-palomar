module

public import ComparisonNativeActualFloorThermalMass
public import ComparisonNativeLocalDyadicThermalDomination

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000

theorem native_actual_mass_slice_thermal_integral (m : NativeBandModel)
    {lo hi : ℝ} (hlo : lo∈Icc (0:ℝ) 1) (hhi : hi∈Icc (0:ℝ) 1) (hlh : lo ≤ hi) :
    (∫u in 0..1,(nativeBroadMassSlice m.hc m.hk m.hkc m.hm m.hM m.alpha lo hi).indicator
      (fun _=>1) (m.R u)*m.thermal u) = ∫u in lo..hi,m.thermal u := by
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  have he : (∫u in Icc (0:ℝ) 1,
      (nativeBroadMassSlice m.hc m.hk m.hkc m.hm m.hM m.alpha lo hi).indicator
        (fun _=>1) (m.R u)*m.thermal u) =
      ∫u in Icc (0:ℝ) 1,(Ioo lo hi).indicator m.thermal u := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    change (nativeBroadMassSlice m.hc m.hk m.hkc m.hm m.hM m.alpha lo hi).indicator
      (fun _=>1) (m.R u)*m.thermal u = (Ioo lo hi).indicator m.thermal u
    have hm := native_mass_slice_quantile_mem m hlo hhi hu
    by_cases hp : u∈Ioo lo hi
    · rw [indicator_of_mem (hm.mpr hp),indicator_of_mem hp,one_mul]
    · rw [indicator_of_notMem (fun h=>hp (hm.mp h)),indicator_of_notMem hp,zero_mul]
  rw [he,setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr (Ioo_subset_Icc_self.trans (Icc_subset_Icc hlo.1 hhi.2)),
    ←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hlh]

end OAI.SKFluctuations.LaplaceWindowFormalization

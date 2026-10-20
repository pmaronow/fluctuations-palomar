module

public import ComparisonActualHighOnlyConditionalErrorTransport
public import ComparisonActualHighOnlyCapThermalGeometry

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
theorem massSlice_error_integral_high_only {lo hi : ℝ}
    (hlo : lo∈Icc a.data.s 1) (hhi : hi∈Icc a.data.s 1) (hlh : lo≤ hi) :
    (∫u in 0..1,(a.shiftedNativeModel.massSlice lo hi).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u)=
      ∫u in lo..hi,a.comparisonErrorDensity u := by
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  have he : (∫u in Icc (0:ℝ) 1,(a.shiftedNativeModel.massSlice lo hi).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u)=
      ∫u in Icc (0:ℝ) 1,(Ioo lo hi).indicator a.comparisonErrorDensity u := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only
    have hm:=a.shiftedNativeModel.massSlice_quantile_mem hlo hhi hu
    change (a.R u∈a.shiftedNativeModel.massSlice lo hi)↔u∈Ioo lo hi at hm
    by_cases hp:u∈Ioo lo hi
    · rw [indicator_of_mem (hm.mpr hp),indicator_of_mem hp,one_mul]
    · rw [indicator_of_notMem (fun H=>hp (hm.mp H)),indicator_of_notMem hp,zero_mul]
  rw [he,setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr (Ioo_subset_Icc_self.trans (Icc_subset_Icc (a.data.hs.1.trans hlo.1) hhi.2)),
    ←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hlh]

theorem cap_error_integral_high_only (P:a.Potential) (cap:ShiftedCapInterval a P) :
    (∫u in 0..1,(Ioo cap.left cap.right).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)=
      ∫u in a.alpha.val.val cap.left..a.alpha.val.val cap.right,a.comparisonErrorDensity u := by
  have hleft:a.alpha.val.val cap.left∈Icc a.data.s 1:=
    inverseConstraint_mass_mem zero_le_one a.data.hc a.data.hk a.data.hkc a.alpha
      ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩
  have hright:a.alpha.val.val cap.right∈Icc a.data.s 1:=
    inverseConstraint_mass_mem zero_le_one a.data.hc a.data.hk a.data.hkc a.alpha
      ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩
  have H:=a.massSlice_error_integral_high_only hleft hright (a.alpha.val.property.2 cap.hlt.le)
  dsimp only [ShiftedNativeBandModel.massSlice] at H
  rw [a.shiftedNativeModel.R_inverse ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩,
    a.shiftedNativeModel.R_inverse ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩] at H
  exact H

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

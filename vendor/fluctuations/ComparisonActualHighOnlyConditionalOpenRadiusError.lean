module

public import ComparisonActualHighOnlyConditionalErrorDecomposition
public import ComparisonActualHighOnlyWholeCapCover

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

theorem error_mask_eq_open_radius_high_only
    (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (S:Set ℝ) :
    (∫u in 0..1,S.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)=
      ∫u in 0..1,(Ioo (0:ℝ) 1∩S).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne a.data.s,volume.ae_ne (1:ℝ)] with u hus hu1 hu
  have hui:u∈Ioc (0:ℝ) 1:=by simpa only [uIoc_of_le zero_le_one] using hu
  by_cases hlow:u < a.data.s
  · rw [a.comparisonErrorDensity_low_zero hlow,mul_zero,mul_zero]
  · have hhigh:a.data.s < u:=lt_of_le_of_ne (le_of_not_gt hlow) hus.symm
    have hspec:a.alpha.val.val (a.R u)=u:=a.shiftedNativeModel.R_spec ⟨hhigh.le,hui.2⟩
    have hr0:0 < a.R u:=by
      by_contra H
      have HR:a.R u=0:=le_antisymm (le_of_not_gt H) (a.shiftedNativeModel.R_bounds _).1
      rw [HR,a.alpha.property.1] at hspec
      exact hhigh.ne hspec
    have hr1:a.R u < 1:=by
      by_contra H
      have HR:a.R u=1:=le_antisymm (a.shiftedNativeModel.R_bounds _).2 (le_of_not_gt H)
      rw [HR,a.alpha.property.2.1] at hspec
      exact hu1 hspec.symm
    by_cases hs:a.R u∈S
    · rw [indicator_of_mem hs,indicator_of_mem (show a.R u∈Ioo (0:ℝ) 1∩S from ⟨⟨hr0,hr1⟩,hs⟩)]
    · rw [indicator_of_notMem hs,indicator_of_notMem (show a.R u∉Ioo (0:ℝ) 1∩S from fun H=>hs H.2)]

theorem original_error_base_prefix_zero_of_U_le_s_high_only
    (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hUs:a.data.U ≤ a.data.s) :
    (∫u in 0..min a.massCoverBase 1,a.comparisonErrorDensity u)=0 := by
  rw [massCoverBase,max_eq_right hUs,min_eq_left a.data.hs1]
  exact a.original_error_low_prefix_zero_high_only

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

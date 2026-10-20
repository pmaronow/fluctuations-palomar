module

public import ComparisonActualHighOnlyConditionalErrorSliceIdentity

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem error_mask_integral_nonneg_high_only (S:Set ℝ) :
    0 ≤ ∫u in 0..1,S.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro u hu
  exact mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) (a.comparisonErrorDensity_nonneg hu)

theorem error_mask_integral_mono_high_only (S T:Set ℝ)
    (hS:MeasurableSet S) (hT:MeasurableSet T) (hsub:S⊆T) :
    (∫u in 0..1,S.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤
      ∫u in 0..1,T.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u := by
  apply intervalIntegral.integral_mono_on zero_le_one (a.error_mask_intervalIntegrable S hS)
    (a.error_mask_intervalIntegrable T hT)
  intro u hu
  by_cases HS:a.R u∈S
  · rw [indicator_of_mem HS,indicator_of_mem (hsub HS)]
  · rw [indicator_of_notMem HS,zero_mul]
    exact mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) (a.comparisonErrorDensity_nonneg hu)

theorem error_mask_integral_union_le_high_only (S T:Set ℝ)
    (hS:MeasurableSet S) (hT:MeasurableSet T) :
    (∫u in 0..1,(S∪T).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤
      (∫u in 0..1,S.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)+
      (∫u in 0..1,T.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) := by
  have hiS:=a.error_mask_intervalIntegrable S hS
  have hiT:=a.error_mask_intervalIntegrable T hT
  rw [←intervalIntegral.integral_add hiS hiT]
  apply intervalIntegral.integral_mono_on zero_le_one (a.error_mask_intervalIntegrable _ (hS.union hT)) (hiS.add hiT)
  intro u hu
  have HE:=a.comparisonErrorDensity_nonneg hu
  by_cases HS:a.R u∈S <;> by_cases HT:a.R u∈T <;> simp [HS,HT,HE]

theorem error_mask_integral_iUnion_le_high_only {ι:Type*} [Fintype ι]
    (S:ι→Set ℝ) (hS:∀i,MeasurableSet (S i)) :
    (∫u in 0..1,(⋃i,S i).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤
      ∑i:ι,∫u in 0..1,(S i).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u := by
  let f:=fun i:ι=>fun u=>(S i).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u
  have hi i:IntervalIntegrable (f i) volume 0 1:=a.error_mask_intervalIntegrable _ (hS i)
  have hiSum:IntervalIntegrable (fun u=>∑i:ι,f i u) volume 0 1:=by
    have he:(fun u=>∑i:ι,f i u)=∑i:ι,f i:=by funext u;simp only [Finset.sum_apply]
    rw [he]
    exact IntervalIntegrable.sum Finset.univ (fun i _=>hi i)
  have H:(∫u in 0..1,(⋃i,S i).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤
      ∫u in 0..1,∑i:ι,f i u:=by
    apply intervalIntegral.integral_mono_on zero_le_one
      (a.error_mask_intervalIntegrable _ (MeasurableSet.iUnion hS)) hiSum
    intro u hu
    have HE:=a.comparisonErrorDensity_nonneg hu
    have hn i:0 ≤ f i u:=mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) HE
    by_cases HS:a.R u∈⋃i,S i
    · obtain ⟨i,hiS⟩:=mem_iUnion.mp HS
      rw [indicator_of_mem HS,one_mul]
      have HH:=Finset.single_le_sum (s:=Finset.univ) (f:=fun i=>f i u) (fun i _=>hn i) (Finset.mem_univ i)
      simpa only [f,indicator_of_mem hiS,one_mul] using HH
    · rw [indicator_of_notMem HS,zero_mul]
      exact Finset.sum_nonneg (fun i _=>hn i)
  rw [intervalIntegral.integral_finsetSum (fun i _=>hi i)] at H
  exact H

theorem error_mask_integral_le_mass_prefix_high_only (S:Set ℝ) (hS:MeasurableSet S)
    {V:ℝ} (hV:V∈Icc (0:ℝ) 1)
    (hupper:∀u∈Icc (0:ℝ) 1,a.R u∈S → u ≤ V) :
    (∫u in 0..1,S.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤
      ∫u in 0..V,a.comparisonErrorDensity u := by
  let L:Set ℝ:={u|u ≤ V}
  have hiL:IntervalIntegrable (fun u=>L.indicator (fun _=>(1:ℝ)) u*a.comparisonErrorDensity u) volume 0 1:=
    intervalIntegrable_bounded_measurable_mul (measurable_const.indicator measurableSet_Iic) zero_le_one
      (fun u _=>by by_cases H:u∈L <;> simp [H]) a.comparisonErrorDensity_intervalIntegrable
  have H:(∫u in 0..1,S.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤
      ∫u in 0..1,L.indicator (fun _=>(1:ℝ)) u*a.comparisonErrorDensity u:=by
    apply intervalIntegral.integral_mono_on zero_le_one (a.error_mask_intervalIntegrable _ hS) hiL
    intro u hu
    by_cases HS:a.R u∈S
    · rw [indicator_of_mem HS,indicator_of_mem (show u∈L from hupper u hu HS)]
    · rw [indicator_of_notMem HS,zero_mul]
      exact mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) (a.comparisonErrorDensity_nonneg hu)
  have he:(fun u=>L.indicator (fun _=>(1:ℝ)) u*a.comparisonErrorDensity u)=L.indicator a.comparisonErrorDensity:=by
    funext u
    by_cases HL:u∈L <;> simp only [indicator_apply,HL,ite_true,ite_false,one_mul,zero_mul]
  rw [he,intervalIntegral.integral_indicator hV] at H
  exact H

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

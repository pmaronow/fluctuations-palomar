module

public import ComparisonActualHighOnlyConditionalFloorError
public import ComparisonActualHighOnlyCapThermalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem original_error_low_prefix_zero_high_only
    (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    (∫u in 0..a.data.s,a.comparisonErrorDensity u)=0 := by
  apply Eq.trans ?_ (intervalIntegral.integral_zero : (∫u in (0:ℝ)..a.data.s,(0:ℝ))=0)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne a.data.s] with u hus hu
  have huu:u∈Ioc (0:ℝ) a.data.s:=by simpa only [uIoc_of_le a.data.hs.1] using hu
  exact a.comparisonErrorDensity_low_zero (lt_of_le_of_ne huu.2 hus)

theorem Potential.original_error_eq_nonpositive_add_positive_high_only
    {a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (P:a.Potential) :
    (∫u in 0..1,a.comparisonErrorDensity u)=
      (∫u in 0..1,(P.negativeSet∪P.contactSet).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)+
      (∫u in 0..1,P.positiveRadiusSet.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) := by
  have hnp:MeasurableSet (P.negativeSet∪P.contactSet):=P.negativeSet_open.measurableSet.union P.contactSet_measurable
  have hiNP:=a.error_mask_intervalIntegrable _ hnp
  have hiP:=a.error_mask_intervalIntegrable _ P.positiveRadiusSet_measurable
  rw [←intervalIntegral.integral_add hiNP hiP]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne a.data.s,volume.ae_ne (1:ℝ)] with u hus hu1 hu
  have hui:u∈Ioc (0:ℝ) 1:=by simpa only [uIoc_of_le zero_le_one] using hu
  by_cases hlow:u < a.data.s
  · rw [a.comparisonErrorDensity_low_zero hlow,mul_zero,mul_zero,add_zero]
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
    by_cases hp:0 < P.H (a.R u)
    · have hpos:a.R u∈P.positiveRadiusSet:=⟨⟨hr0.le,hr1.le⟩,hp⟩
      have hnot:a.R u∉P.negativeSet∪P.contactSet:=by
        intro H
        rcases H with H|H
        · exact hp.not_ge H.2.le
        · exact hp.ne' H.2
      rw [indicator_of_notMem hnot,indicator_of_mem hpos,zero_mul,one_mul,zero_add]
    · have hnot:a.R u∉P.positiveRadiusSet:=fun H=>hp H.2
      have hnp:a.R u∈P.negativeSet∪P.contactSet:=by
        rcases (le_of_not_gt hp).eq_or_lt with H|H
        · exact Or.inr ⟨⟨hr0.le,hr1.le⟩,H⟩
        · exact Or.inl ⟨⟨hr0,hr1⟩,H⟩
      rw [indicator_of_mem hnp,indicator_of_notMem hnot,one_mul,zero_mul,add_zero]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

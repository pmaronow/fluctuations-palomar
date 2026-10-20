module

public import ComparisonNativeRadiusMeanSquareAssembly
public import ComparisonNativeWeightedDefectLimit
public import ComparisonNativeMaskMassTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

namespace MassCellAveraging

theorem weighted_step_intervalIntegrable (f : ℝ→ℝ) (as : List PositiveMass)
    (D : ℕ→ℝ) (hD : ∀i,D i∈Icc (0:ℝ) 1) {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun u=>f u*massStepFunction as D u) volume a b := by
  apply IntervalIntegrable.mono_fun' hf.norm
    (hf.aestronglyMeasurable_restrict_uIoc.mul (massStepFunction_measurable_native as D).aestronglyMeasurable.restrict)
  filter_upwards [] with u
  change ‖f u*massStepFunction as D u‖ ≤ ‖f u‖
  rw [norm_mul]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (massStepFunction_mem_Icc_native as D hD u).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (massStepFunction_mem_Icc_native as D hD u).2

theorem weighted_step_integral (f : ℝ→ℝ) {a : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (D : ℕ→ℝ) (hD : ∀i,D i∈Icc (0:ℝ) 1)
    (hf : IntervalIntegrable f volume a (partitionEnd a as)) :
    massCellSum as a (fun i=>originalCoefficient f a as i*D i)=
      ∫u in a..partitionEnd a as,f u*massStepFunction as D u := by
  induction as generalizing a D with
  | nil=>simp [massCellSum,partitionEnd]
  | cons b bs ih=>
    have hbe := massOrdered_start_le_end bs ho.2.2
    have hae := ho.2.1.trans hbe
    have hIab : uIcc a b.val⊆uIcc a (partitionEnd b.val bs) := by
      rw [uIcc_of_le ho.2.1,uIcc_of_le hae]
      exact Icc_subset_Icc le_rfl hbe
    have hIbe : uIcc b.val (partitionEnd b.val bs)⊆uIcc a (partitionEnd b.val bs) := by
      rw [uIcc_of_le hbe,uIcc_of_le hae]
      exact Icc_subset_Icc ho.2.1 le_rfl
    have hf1 := hf.mono_set hIab
    have hf2 := hf.mono_set hIbe
    have hfirst : (∫u in a..b.val,f u*massStepFunction (b::bs) D u)=
        (b.val-a)*(average f a b.val*D 0) := by
      have heq : (∫u in a..b.val,f u*massStepFunction (b::bs) D u)=∫u in a..b.val,f u*D 0 :=
        intervalIntegral.integral_congr_Ioo_of_le ho.2.1
          (fun u hu=>by simp only [massStepFunction,ite_true,hu.2])
      rw [heq,intervalIntegral.integral_mul_const]
      have he : (b.val-a)*average f a b.val=∫u in a..b.val,f u := by
        by_cases hab : a=b.val
        · subst a;simp
        · unfold average;field_simp
      rw [←he];ring
    have hrest : (∫u in b.val..partitionEnd b.val bs,f u*massStepFunction (b::bs) D u)=
        ∫u in b.val..partitionEnd b.val bs,f u*massStepFunction bs (fun j=>D (j+1)) u :=
      intervalIntegral.integral_congr_Ioo_of_le hbe
        (fun u hu=>by simp only [massStepFunction,ite_false,not_lt.mpr hu.1.le])
    have hcoef0 : originalCoefficient f a (b::bs) 0=average f a b.val := by
      simp only [originalCoefficient,partitionPoint,partitionValues,partitionValues_zero,id_eq]
    have hcoefS j : originalCoefficient f a (b::bs) (j+1)=originalCoefficient f b.val bs j := by
      simp only [originalCoefficient,partitionPoint,partitionValues]
    rw [massCellSum,hcoef0]
    simp_rw [hcoefS]
    rw [ih ho.2.2 (fun j=>D (j+1)) (fun j=>hD (j+1)) hf2]
    simp only [partitionEnd]
    rw [←intervalIntegral.integral_add_adjacent_intervals
      (weighted_step_intervalIntegrable f (b::bs) D hD hf1)
      (weighted_step_intervalIntegrable f (b::bs) D hD hf2),hfirst,hrest]

end MassCellAveraging
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_native_radius_defect_eq_weighted_thermal
    (n : ℕ) (b h : ℝ→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {a z kmin : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1)
    (hkmin : 0<kmin) (hfloor : ∀r∈Ioo a z,kmin ≤ k r) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    let f := comparisonRadiusMassWeight (comparisonSweepQuantile hc hk hkc hm hM α)
      α.val.val (Ioo a z) 1 kmin
    (∑i,comparisonNativeRadiusRowMass hc hk hkc hm hM q α as Finset.univ a z i*
      actualCutReplicaDefect (n+1) steps (q 0) i.val
        (physicalPathSecondMoment (n+1) steps (q 0) i.val))=
      ∫u in 0..1,f u*physicalSampledThermal n b h as ho u := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let steps := sampleClockSteps q 0 as
  let f := comparisonRadiusMassWeight (comparisonSweepQuantile hc hk hkc hm hM α)
    α.val.val (Ioo a z) 1 kmin
  let D := fun j:ℕ=>if hj:j ≤ steps.length then
    actualCutReplicaDefect (n+1) steps (q 0) j (physicalPathSecondMoment (n+1) steps (q 0) j) else 0
  have hs := sampleClockSteps_ordered q as ho
  have hD j : D j∈Icc (0:ℝ) 1 := by
    dsimp only [D]
    split_ifs with hj
    · exact actualCenteredCutReplicaDefect_mem_unit_interval (n+1) steps hs (q 0) j hj
    · norm_num
  have hDj (i : Fin (steps.length+1)) : D i.val=
      actualCutReplicaDefect (n+1) steps (q 0) i.val (physicalPathSecondMoment (n+1) steps (q 0) i.val) := by
    dsimp only [D]
    rw [dite_eq_left (by omega)]
  have hthermal : physicalSampledThermal n b h as ho=massStepFunction as D := by
    rw [physicalSampledThermal_eq_rooted_massStepFunction]
    apply massStepFunction_congr_upto
    intro j hj
    have hj' : j ≤ steps.length := by simpa only [steps,sampleClockSteps_length] using hj
    simp only [D,dite_eq_left hj']
    exact (actualCenteredCutReplicaDefect_eq_thermal_defect (n+1) steps hs (q 0) j hj').symm
  have hf := comparisonRadiusMassWeight_memLp_two (A:=Ioo a z)
    (comparisonSweepQuantile hc hk hkc hm hM α) α.val.val
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α).measurable measurableSet_Ioo (by norm_num : (0:ℝ)<1) hkmin
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hf.integrable (by norm_num))
  have hsum := sampled_mass_weight_sum q as 0
    (fun j=>MassCellAveraging.originalCoefficient f 0 as j*D j)
  rw [he,sub_self,zero_mul,add_zero] at hsum
  calc
    _ = ∑i,pathMassDifferences steps 0 i*(MassCellAveraging.originalCoefficient f 0 as i.val*D i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [comparisonNativeRadiusRowMass_eq_duration_weight hc hk hkc hm hM q α as ho he
        ha haz hz (by norm_num : (0:ℝ)<1) hkmin hfloor i,hDj]
      change 1*pathMassDifferences steps 0 i*MassCellAveraging.originalCoefficient f 0 as i.val*
        actualCutReplicaDefect (n+1) steps (q 0) i.val (physicalPathSecondMoment (n+1) steps (q 0) i.val)=_
      ring
    _ = massCellSum as 0 (fun j=>MassCellAveraging.originalCoefficient f 0 as j*D j) := hsum
    _ = _ := by rw [MassCellAveraging.weighted_step_integral f as ho D hD (by simpa only [he] using hfi),he,←hthermal]

theorem comparison_native_radius_thermal_pullback (α : inverseIntegralConstraints 0 0 k M)
    {a z kmin : ℝ} (ha : 0 ≤ a) (hz : z ≤ 1)
    (hkmin : 0<kmin) (hfloor : ∀r∈Ioo a z,kmin ≤ k r) (G : ℝ→ℝ) :
    (∫u in 0..1,comparisonRadiusMassWeight (comparisonSweepQuantile hc hk hkc hm hM α)
      α.val.val (Ioo a z) 1 kmin u*G u)=∫r in Ioo a z,G (α.val.val r) := by
  rw [comparisonSweep_mass_substitution hc hk hkc hm hM α]
  have hAD : Ioo a z⊆Icc (0:ℝ) 1 := Ioo_subset_Icc_self.trans (Icc_subset_Icc ha hz)
  have hpull := comparisonRadiusMassWeight_linear_pullback hc hk hkc hm hM α measurableSet_Ioo hAD
    (by norm_num : (0:ℝ)<1) hkmin hfloor
  have heq : (∫r in Icc (0:ℝ) 1,deriv α.val.val r*
      (comparisonRadiusMassWeight (comparisonSweepQuantile hc hk hkc hm hM α)
        α.val.val (Ioo a z) 1 kmin (α.val.val r)*G (α.val.val r)))=
      ∫r in Icc (0:ℝ) 1,(Ioo a z).indicator (fun r=>G (α.val.val r)) r := by
    apply integral_congr_ae
    filter_upwards [hpull] with r hr
    rw [←mul_assoc,hr]
    by_cases hmem : r∈Ioo a z <;> simp [hmem]
  rw [heq,integral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hAD]

theorem comparison_native_radius_defect_tendsto
    (n : ℕ) (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmsh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    {a z kmin : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1)
    (hkmin : 0<kmin) (hfloor : ∀r∈Ioo a z,kmin ≤ k r) :
    let q := completedPathClock (n+1) b h
    Tendsto (fun j=>∑i,comparisonNativeRadiusRowMass hc hk hkc hm hM q α (as j) Finset.univ a z i*
      actualCutReplicaDefect (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val
        (physicalPathSecondMoment (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val)) atTop
      (𝓝 (∫r in Ioo a z,orderedPathB (n+1) b h (α.val.val r)-
        (orderedPathS (n+1) b h (α.val.val r))^2)) := by
  dsimp only
  simp_rw [comparison_native_radius_defect_eq_weighted_thermal hc hk hkc hm hM n b h α _ (ho _) (he _)
    ha haz hz hkmin hfloor]
  have hw := comparisonRadiusMassWeight_measurable (comparisonSweepQuantile hc hk hkc hm hM α)
    α.val.val (comparisonSweepQuantile_monotone hc hk hkc hm hM α).measurable (A:=Ioo a z) measurableSet_Ioo 1 kmin
  have ht := physicalSampledThermal_weighted_integral_tendsto n b h hb hh as mesh ho he hmsh hlim
    (comparisonRadiusMassWeight (comparisonSweepQuantile hc hk hkc hm hM α) α.val.val (Ioo a z) 1 kmin)
    hw (by positivity : 0 ≤ 1/(1*kmin))
    (fun u _=>comparisonRadiusMassWeight_bounds _ _ _ (by norm_num : (0:ℝ)<1) hkmin u)
  rw [comparison_native_radius_thermal_pullback hc hk hkc hm hM α ha hz hkmin hfloor] at ht
  exact ht

end
end OAI.SKFluctuations.LaplaceWindowFormalization

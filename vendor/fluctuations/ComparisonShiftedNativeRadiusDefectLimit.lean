module

public import ComparisonShiftedNativeRadiusWeights
public import ComparisonNativeRadiusDefectLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

def radiusDefect (as : List PositiveMass) (f : ℝ→ℝ) : ℝ :=
  let steps:=sampleClockSteps m.q 0 as
  ∑i,pathMassDifferences steps 0 i*comparisonOriginalRadiusWeights m.q as f i*
    actualCutReplicaDefect (m.n+1) steps (m.q 0) i.val
      (physicalPathSecondMoment (m.n+1) steps (m.q 0) i.val)

theorem radiusDefect_eq_weighted_thermal
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {A : Set ℝ} (hA : MeasurableSet A) {x kmin : ℝ} (hx : 0 < x) (hkmin : 0 < kmin) :
    let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
    m.radiusDefect as f=∫u in 0..1,f u*physicalSampledThermal m.n m.bf m.hf as ho u := by
  dsimp only
  let steps:=sampleClockSteps m.q 0 as
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
  let D:=fun j:ℕ=>if hj:j ≤ steps.length then
    actualCutReplicaDefect (m.n+1) steps (m.q 0) j
      (physicalPathSecondMoment (m.n+1) steps (m.q 0) j) else 0
  have hs:=sampleClockSteps_ordered m.q as ho
  have hD j : D j∈Icc (0:ℝ) 1 := by
    dsimp only [D]
    split_ifs with hj
    · exact actualCenteredCutReplicaDefect_mem_unit_interval (m.n+1) steps hs (m.q 0) j hj
    · norm_num
  have hDj (i : Fin (steps.length+1)) : D i.val=
      actualCutReplicaDefect (m.n+1) steps (m.q 0) i.val
        (physicalPathSecondMoment (m.n+1) steps (m.q 0) i.val) := by
    dsimp only [D]
    rw [dite_eq_left (by omega)]
  have hthermal : physicalSampledThermal m.n m.bf m.hf as ho=massStepFunction as D := by
    rw [physicalSampledThermal_eq_rooted_massStepFunction]
    apply massStepFunction_congr_upto
    intro j hj
    have hj' : j ≤ steps.length := by simpa only [steps,sampleClockSteps_length] using hj
    simp only [D,dite_eq_left hj']
    exact (actualCenteredCutReplicaDefect_eq_thermal_defect (m.n+1) steps hs (m.q 0) j hj').symm
  have hf:=comparisonRadiusMassWeight_memLp_two m.R m.alpha.val.val
    m.R_monotone.measurable hA hx hkmin
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hf.integrable (by norm_num))
  have hsum:=sampled_mass_weight_sum m.q as 0
    (fun j=>MassCellAveraging.originalCoefficient f 0 as j*D j)
  rw [he,sub_self,zero_mul,add_zero] at hsum
  calc
    m.radiusDefect as f = ∑i,pathMassDifferences steps 0 i*
        (MassCellAveraging.originalCoefficient f 0 as i.val*D i.val) := by
      unfold radiusDefect
      apply Finset.sum_congr rfl
      intro i _
      rw [hDj]
      unfold comparisonOriginalRadiusWeights
      ring
    _ = massCellSum as 0 (fun j=>MassCellAveraging.originalCoefficient f 0 as j*D j) := hsum
    _ = _ := by
      rw [MassCellAveraging.weighted_step_integral f as ho D hD
        (by simpa only [he] using hfi),he,←hthermal]

theorem radius_thermal_pullback
    {lo z kmin : ℝ} (hlo : m.rmin ≤ lo) (hz : z ≤ 1)
    (hkmin : 0 < kmin) (hfloor : ∀r∈Ioo lo z,kmin ≤ m.k r)
    (G : ℝ→ℝ)
    (hGi : IntervalIntegrable
      (fun u=>comparisonRadiusMassWeight m.R m.alpha.val.val (Ioo lo z) 1 kmin u*G u)
      volume 0 1) :
    (∫u in 0..1,comparisonRadiusMassWeight m.R m.alpha.val.val (Ioo lo z) 1 kmin u*G u)=
      ∫r in Ioo lo z,G (m.alpha.val.val r) := by
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val (Ioo lo z) 1 kmin
  have hz0 : 0 ≤ m.u0 := m.hu.1
  have hz1 : m.u0 ≤ 1 := m.hu.2
  have hi0 : IntervalIntegrable (fun u=>f u*G u) volume 0 m.u0 := hGi.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le hz0]
    exact Icc_subset_Icc le_rfl hz1)
  have hi1 : IntervalIntegrable (fun u=>f u*G u) volume m.u0 1 := hGi.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le hz1]
    exact Icc_subset_Icc hz0 le_rfl)
  have hlow : (∫u in (0:ℝ)..m.u0,f u*G u)=0 := by
    have heq : (∫u in (0:ℝ)..m.u0,f u*G u)=∫u in (0:ℝ)..m.u0,(0:ℝ) :=
      intervalIntegral.integral_congr_Ioo_of_le hz0 (fun u hu=>by
        dsimp only [f,comparisonRadiusMassWeight]
        rw [m.R_before hu.2.le]
        have hn : m.rmin∉Ioo lo z := fun h=>not_lt_of_ge hlo h.1
        simp only [hn,ite_false,zero_mul])
    rw [heq]
    simp
  rw [←intervalIntegral.integral_add_adjacent_intervals hi0 hi1,hlow,zero_add,
    m.mass_radius_substitution]
  have hAD : Ioo lo z⊆Icc m.rmin 1 :=
    Ioo_subset_Icc_self.trans (Icc_subset_Icc hlo hz)
  have hpull:=m.radiusMassWeight_linear_pullback (A:=Ioo lo z)
    (by norm_num : (0:ℝ) < 1) hkmin hfloor
  have heq : (∫r in Icc m.rmin 1,deriv m.alpha.val.val r*
      (f (m.alpha.val.val r)*G (m.alpha.val.val r)))=
      ∫r in Icc m.rmin 1,(Ioo lo z).indicator (fun r=>G (m.alpha.val.val r)) r := by
    apply integral_congr_ae
    filter_upwards [hpull] with r hr
    change deriv m.alpha.val.val r*(f (m.alpha.val.val r)*G (m.alpha.val.val r))=_
    rw [←mul_assoc,hr]
    by_cases hmem : r∈Ioo lo z <;> simp [hmem]
  rw [heq,integral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hAD]

theorem radiusDefect_tendsto
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z kmin : ℝ} (hlo : m.rmin ≤ lo) (hz : z ≤ 1)
    (hkmin : 0 < kmin) (hfloor : ∀r∈Ioo lo z,kmin ≤ m.k r) :
    let f:=comparisonRadiusMassWeight m.R m.alpha.val.val (Ioo lo z) 1 kmin
    Tendsto (fun j=>m.radiusDefect (as j) f) atTop
      (𝓝 (∫r in Ioo lo z,m.thermal (m.alpha.val.val r))) := by
  dsimp only
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val (Ioo lo z) 1 kmin
  simp_rw [m.radiusDefect_eq_weighted_thermal _ (ho _) (he _) measurableSet_Ioo
    (by norm_num : (0:ℝ) < 1) hkmin]
  have hw:=comparisonRadiusMassWeight_measurable m.R m.alpha.val.val
    m.R_monotone.measurable (A:=Ioo lo z) measurableSet_Ioo 1 kmin
  have hb u (_hu : u∈Ioc (0:ℝ) 1) : f u∈Icc (0:ℝ) (1/(1*kmin)) :=
    comparisonRadiusMassWeight_bounds _ _ _ (by norm_num : (0:ℝ) < 1) hkmin u
  have ht:=physicalSampledThermal_weighted_integral_tendsto m.n m.bf m.hf m.hbf m.hhf
    as mesh ho he hmesh hlim f hw (by positivity : 0 ≤ 1/(1*kmin)) hb
  have hGi:=intervalIntegrable_bounded_measurable_mul hw
    (by positivity : 0 ≤ 1/(1*kmin)) hb
    (physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf m.hbf m.hhf)
  rw [m.radius_thermal_pullback hlo hz hkmin hfloor _ hGi] at ht
  exact ht

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeConditionalAssembly
public import ComparisonWeightedThermalPathLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000

def nativeSelectedMassMask {ι : Type} (q : ℝ→ι→ℝ≥0) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) : ℝ→ℝ :=
  massStepFunction as (nativeSelectedColumn J (fun _=>(0:Fin 1)) (fun _=>1))

theorem massStepFunction_measurable_native (as : List PositiveMass) (f : ℕ→ℝ) :
    Measurable (massStepFunction as f) := by
  induction as generalizing f with
  | nil=>exact measurable_const
  | cons a as ih=>
    exact measurable_const.ite measurableSet_Iio (ih (fun i=>f (i+1)))

theorem massStepFunction_mem_Icc_native (as : List PositiveMass) (f : ℕ→ℝ)
    {a b : ℝ} (hf : ∀i,f i∈Icc a b) (u : ℝ) : massStepFunction as f u∈Icc a b := by
  induction as generalizing f with
  | nil=>exact hf 0
  | cons c cs ih=>
    simp only [massStepFunction]
    split_ifs
    · exact hf 0
    · exact ih (fun i=>f (i+1)) (fun i=>hf (i+1))

theorem nativeSelectedMassMask_measurable {ι : Type} (q : ℝ→ι→ℝ≥0)
    (as : List PositiveMass) (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) :
    Measurable (nativeSelectedMassMask q as J) :=
  massStepFunction_measurable_native as _

theorem nativeSelectedMassMask_mem_unit_interval {ι : Type} (q : ℝ→ι→ℝ≥0)
    (as : List PositiveMass) (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) (u : ℝ) :
    nativeSelectedMassMask q as J u∈Icc (0:ℝ) 1 := by
  apply massStepFunction_mem_Icc_native
  intro i
  unfold nativeSelectedColumn
  split_ifs <;> norm_num

theorem actual_selected_centered_defect_eq_native_mask_integral
    (n : ℕ) (b h : ℝ→ℝ≥0) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps (completedPathClock (n+1) b h) 0 as).length+1))) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    (∑i,physicalSelectedCellMass steps J i*
      actualCutReplicaDefect (n+1) steps (q 0) i.val
        (physicalPathSecondMoment (n+1) steps (q 0) i.val))=
      ∫u in 0..1,nativeSelectedMassMask q as J u*physicalSampledThermal n b h as ho u := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let steps := sampleClockSteps q 0 as
  let f := fun j=>actualCutReplicaDefect (n+1) steps (q 0) j
    (physicalPathSecondMoment (n+1) steps (q 0) j)
  let C := nativeSelectedColumn J (fun _=>(0:Fin 1)) (fun _=>1)
  have hthermal : physicalSampledThermal n b h as ho=massStepFunction as f := by
    rw [physicalSampledThermal_eq_rooted_massStepFunction]
    apply massStepFunction_congr_upto
    intro j hj
    exact (actualCenteredCutReplicaDefect_eq_thermal_defect (n+1) steps
      (sampleClockSteps_ordered q as ho) (q 0) j
      (by simpa only [steps,sampleClockSteps_length] using hj)).symm
  rw [hthermal]
  change (∑i,physicalSelectedCellMass steps J i*f i.val)=
    ∫u in 0..1,massStepFunction as C u*massStepFunction as f u
  simp_rw [←massStepFunction_mul]
  have hsum := sampled_mass_weight_sum q as 0 (fun i=>C i*f i)
  rw [he,sub_self,zero_mul,add_zero] at hsum
  rw [←he,←massCellSum_eq_integral as ho,←hsum]
  apply Finset.sum_congr rfl
  intro i _
  change physicalSelectedCellMass steps J i*f i.val=
    pathMassDifferences steps 0 i*(C i.val*f i.val)
  have hC : C i.val=(if i∈J then (1:ℝ) else 0) := by
    exact nativeSelectedColumn_atIndex J (fun _=>(0:Fin 1)) (fun _=>1) i
  rw [hC]
  by_cases hi : i∈J <;> simp [physicalSelectedCellMass,hi]

theorem physicalSampledThermal_changing_mask_error
    (n : ℕ) (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as)
    (v w : ℝ→ℝ) (hv : Measurable v) (hw : Measurable w)
    (hvbound : ∀u∈Ioc (0:ℝ) 1,v u∈Icc (0:ℝ) 1)
    (hwbound : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) 1) :
    |(∫u in 0..1,v u*physicalSampledThermal n b h as ho u)-
      (∫u in 0..1,w u*(orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))|≤
      3*mesh*physicalBApproximationConstant n b h+(∫u in 0..1,|v u-w u|) := by
  let G := fun u=>orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2
  have hG := physicalOrderedThermal_intervalIntegrable n b h hb hh
  have hvG := intervalIntegrable_bounded_measurable_mul hv (show (0:ℝ)≤1 by norm_num) hvbound hG
  have hwG := intervalIntegrable_bounded_measurable_mul hw (show (0:ℝ)≤1 by norm_num) hwbound hG
  have hdiff : IntervalIntegrable (fun u=>|v u-w u|) volume 0 1 := by
    apply IntervalIntegrable.mono_fun' (intervalIntegrable_const (c:=(1:ℝ)))
      ((hv.sub hw).abs.aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    rw [uIoc_of_le zero_le_one] at hu
    have hvu := hvbound u hu
    have hwu := hwbound u hu
    rw [Real.norm_eq_abs,abs_abs]
    change |v u-w u|≤(1:ℝ)
    exact abs_le.mpr ⟨by linarith [hvu.1,hvu.2,hwu.1,hwu.2],
      by linarith [hvu.1,hvu.2,hwu.1,hwu.2]⟩
  have hprod : IntervalIntegrable (fun u=>(v u-w u)*G u) volume 0 1 := by
    convert hvG.sub hwG using 1
    funext u
    ring
  have hchange : |(∫u in 0..1,v u*G u)-(∫u in 0..1,w u*G u)|≤
      ∫u in 0..1,|v u-w u| := by
    rw [←intervalIntegral.integral_sub hvG hwG]
    have heq : (fun u=>v u*G u-w u*G u)=(fun u=>(v u-w u)*G u) := by
      funext u
      ring
    change |∫u in 0..1,v u*G u-w u*G u|≤_
    rw [heq]
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
      hprod.abs hdiff (fun u hu=>by
        have hp := orderedPath_SK_bounds (n+1) (by omega) b h hb hh ⟨hu.1,hu.2.le⟩
        have hGu : G u∈Icc (0:ℝ) 1 := by
          dsimp [G]
          constructor <;> nlinarith [hp.2.2.1,hp.2.2.2,sq_nonneg (orderedPathS (n+1) b h u)]
        rw [abs_mul,abs_of_nonneg hGu.1]
        exact mul_le_of_le_one_right (abs_nonneg _) hGu.2)
    exact (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans hmono
  have hsample := physicalSampledThermal_weighted_integral_error n b h hb hh
    as ho he hm v hv (show (0:ℝ)≤1 by norm_num) hvbound
  have htriangle := abs_sub_le
    (∫u in 0..1,v u*physicalSampledThermal n b h as ho u)
    (∫u in 0..1,v u*G u) (∫u in 0..1,w u*G u)
  simpa only [one_mul] using htriangle.trans (add_le_add hsample hchange)

theorem actual_selected_centered_defect_tendsto_native_path
    (n : ℕ) (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh : Tendsto mesh atTop (𝓝 0))
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps (completedPathClock (n+1) b h) 0 (as j)).length+1)))
    (w : ℝ→ℝ) (hw : Measurable w) (hwb : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) 1)
    (hmasks : Tendsto (fun j=>∫u in 0..1,
      |nativeSelectedMassMask (completedPathClock (n+1) b h) (as j) (J j) u-w u|) atTop (𝓝 0)) :
    Tendsto (fun j=>∑i,physicalSelectedCellMass
      (sampleClockSteps (completedPathClock (n+1) b h) 0 (as j)) (J j) i*
      actualCutReplicaDefect (n+1)
        (sampleClockSteps (completedPathClock (n+1) b h) 0 (as j))
        (completedPathClock (n+1) b h 0) i.val
        (physicalPathSecondMoment (n+1)
          (sampleClockSteps (completedPathClock (n+1) b h) 0 (as j))
          (completedPathClock (n+1) b h 0) i.val)) atTop
      (𝓝 (∫u in 0..1,w u*(orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))) := by
  simp_rw [actual_selected_centered_defect_eq_native_mask_integral n b h _ (ho _) (he _)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun _=>abs_nonneg _) (fun j=>
    physicalSampledThermal_changing_mask_error n b h hb hh (as j) (ho j) (he j) (hm j)
      _ w (nativeSelectedMassMask_measurable _ _ _) hw
      (fun u _=>nativeSelectedMassMask_mem_unit_interval _ _ _ u) hwb)
    (by simpa only [mul_zero,zero_mul,zero_add] using
      ((hmesh.const_mul 3).mul_const (physicalBApproximationConstant n b h)).add hmasks)

theorem actual_selected_centered_defect_mass_exhaustion
    (n : ℕ) (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) (J K : Finset (Fin (steps.length+1))) (hJK : J⊆K) :
    let f := fun i : Fin (steps.length+1)=>actualCutReplicaDefect n steps q0 i.val
      (physicalPathSecondMoment n steps q0 i.val)
    ((∑i,physicalSelectedCellMass steps K i*f i)-(∑i,physicalSelectedCellMass steps J i*f i))∈
      Icc (0:ℝ) ((∑i,physicalSelectedCellMass steps K i)-(∑i,physicalSelectedCellMass steps J i)) := by
  dsimp only
  let f := fun i : Fin (steps.length+1)=>actualCutReplicaDefect n steps q0 i.val
    (physicalPathSecondMoment n steps q0 i.val)
  have hf i : f i∈Icc (0:ℝ) 1 :=
    actualCenteredCutReplicaDefect_mem_unit_interval n steps ha q0 i.val (by omega)
  have hm i : 0≤physicalSelectedCellMass steps K i-physicalSelectedCellMass steps J i := by
    by_cases hiJ : i∈J
    · have hiK := hJK hiJ
      simp [physicalSelectedCellMass,hiJ,hiK]
    · by_cases hiK : i∈K
      · simpa [physicalSelectedCellMass,hiJ,hiK] using pathMassDifferences_nonneg steps ha i
      · simp [physicalSelectedCellMass,hiJ,hiK]
  have heq : (∑i,physicalSelectedCellMass steps K i*f i)-(∑i,physicalSelectedCellMass steps J i*f i)=
      ∑i,(physicalSelectedCellMass steps K i-physicalSelectedCellMass steps J i)*f i := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (_-_)∈Icc (0:ℝ) (_-_)
  rw [heq,←Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun i _=>mul_nonneg (hm i) (hf i).1)
  · exact Finset.sum_le_sum (fun i _=>mul_le_of_le_one_right (hm i) (hf i).2)

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem actual_comparison_native_selected_defect_tendsto
    (n : ℕ) {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam)
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmsh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh : Tendsto mesh atTop (𝓝 0))
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 (as j)).length+1)))
    (w : ℝ→ℝ) (hw : Measurable w) (hwb : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) 1)
    (hmasks : Tendsto (fun j=>∫u in 0..1,
      |nativeSelectedMassMask (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α)
        (as j) (J j) u-w u|) atTop (𝓝 0)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    Tendsto (fun j=>∑i,physicalSelectedCellMass (sampleClockSteps q 0 (as j)) (J j) i*
      actualCutReplicaDefect (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val
        (physicalPathSecondMoment (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val)) atTop
      (𝓝 (∫u in 0..1,w u*(orderedPathB (n+1) bf hf u-(orderedPathS (n+1) bf hf u)^2))) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd hlam hlb hb hh hh0 α
  exact actual_selected_centered_defect_tendsto_native_path n bf hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) as mesh ho he hmsh
    hmesh J w hw hwb hmasks

end
end OAI.SKFluctuations.LaplaceWindowFormalization

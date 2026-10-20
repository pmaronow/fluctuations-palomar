module

public import ComparisonShiftedNativeRadiusHeightBins
public import ComparisonNativeRadiusSideDominance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem radiusRowMass_eq_duration_weight {ι : Type}
    (q : ℝ→ι→ℝ≥0) 
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {a z x kmin : ℝ} (ha : m.rmin < a) (haz : a ≤ z) (hz : z ≤ 1)
    (hx : 0<x) (hkmin : 0<kmin) (hfloor : ∀r∈Ioo a z,kmin ≤ m.k r)
    (i : Fin ((sampleClockSteps q 0 as).length+1)) :
    radiusRowMass m q as Finset.univ a z i=
      x*pathMassDifferences (sampleClockSteps q 0 as) 0 i*
      comparisonOriginalRadiusWeights q as
        (comparisonRadiusMassWeight (m.R)
          m.alpha.val.val (Ioo a z) x kmin) i := by
  let steps := sampleClockSteps q 0 as
  let dm := pathMassDifferences steps 0
  let R := m.R
  let f := comparisonRadiusMassWeight R m.alpha.val.val (Ioo a z) x kmin
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered q as ho
  by_cases hi0 : dm i=0
  · rw [radiusRowMass_zero_of_zero_mass m q as Finset.univ a z i hi0]
    simp only [dm,steps] at hi0
    rw [hi0]
    simp
  have hd : 0<dm i := lt_of_le_of_ne (pathMassDifferences_nonneg steps hs i) (Ne.symm hi0)
  have hi : i.val<as.length := by
    have hib : i.val ≤ as.length := by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt
    by_contra hn
    have hie : i.val=as.length := le_antisymm hib (le_of_not_gt hn)
    have hilast : i=Fin.last steps.length := Fin.ext (by simpa only [Fin.val_last,steps,sampleClockSteps_length] using hie)
    exact hi0 (by rw [hilast];exact sampled_terminal_mass_zero q as he)
  have h0 : physicalCutMass 0 steps i.val=partitionPoint 0 as i.val :=
    physicalCutMass_sampleClockSteps q 0 as i.val hi.le
  have h1 : physicalCutMass 0 steps (i.val+1)=partitionPoint 0 as (i.val+1) :=
    physicalCutMass_sampleClockSteps q 0 as (i.val+1) (by omega)
  have hdm : dm i=partitionPoint 0 as (i.val+1)-partitionPoint 0 as i.val := by
    dsimp only [dm]
    rw [pathMassDifferences_eq_cutMass,h0,h1]
  have hu := partitionPoint_mem as ho i.val
  have hv := partitionPoint_mem as ho (i.val+1)
  have huv : partitionPoint 0 as i.val<partitionPoint 0 as (i.val+1) := by
    rw [hdm] at hd
    exact sub_pos.mp hd
  have havg:=m.radiusMassWeight_cell_average_eq_radius_length ha hz measurableSet_Ioo
    (Subset.refl _) hx hkmin hfloor hu hv huv
  change radiusRowMass m q as Finset.univ a z i=
    x*dm i*MassCellAveraging.average f (partitionPoint 0 as i.val) (partitionPoint 0 as (i.val+1))
  rw [havg]
  simp only [radiusRowMass,Finset.mem_univ,ite_true]
  change volume.real (Ioo a z ∩ Ioc (R (physicalCutMass 0 steps i.val))
    (R (physicalCutMass 0 steps (i.val+1))))=_
  rw [h0,h1]
  rw [←hdm]
  field_simp [hx.ne',hi0]
  rfl

theorem radiusRowMass_le_full {ι : Type}
    (q : ℝ→ι→ℝ≥0) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) (a z : ℝ)
    (i : Fin ((sampleClockSteps q 0 as).length+1)) :
    radiusRowMass m q as J a z i ≤
      radiusRowMass m q as Finset.univ a z i := by
  unfold radiusRowMass
  simp only [Finset.mem_univ,ite_true]
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

theorem radiusSideCoefficients_le_full {ι : Type}
    (q : ℝ→ι→ℝ≥0) 
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    {a z delta kmin : ℝ} (ha : m.rmin < a) (haz : a ≤ z) (hz : z ≤ 1)
    (hd : 0<delta) (hkmin : 0<kmin) (hfloor : ∀r∈Ioo a z,kmin ≤ m.k r)
    (i : Fin ((sampleClockSteps q 0 as).length+1))
    (hl : delta ≤ NativeRadiusSide.before
      (radiusRowMass m q as J a z) i)
    (hr : delta ≤ NativeRadiusSide.after
      (radiusRowMass m q as J a z) i) :
    let mass := radiusRowMass m q as J a z
    let duration := pathMassDifferences (sampleClockSteps q 0 as) 0
    let W := comparisonOriginalRadiusWeights q as
      (comparisonRadiusMassWeight (m.R)
        m.alpha.val.val (Ioo a z) delta kmin)
    (∀j,NativeRadiusSide.leftCoefficient duration mass i j∈Icc (0:ℝ) (W j)) ∧
      (∀j,NativeRadiusSide.rightCoefficient duration mass i j∈Icc (0:ℝ) (W j)) := by
  dsimp only
  let steps := sampleClockSteps q 0 as
  let dm := pathMassDifferences steps 0
  let mass := radiusRowMass m q as J a z
  let full := radiusRowMass m q as Finset.univ a z
  let W := comparisonOriginalRadiusWeights q as
    (comparisonRadiusMassWeight (m.R)
      m.alpha.val.val (Ioo a z) delta kmin)
  have hs := sampleClockSteps_ordered q as ho
  have hdm j : 0 ≤ dm j := pathMassDifferences_nonneg steps hs j
  have hmass j : 0 ≤ mass j := radiusRowMass_nonneg m q as J a z j
  have hdom j : mass j ≤ full j := radiusRowMass_le_full m q as J a z j
  have heq j : full j=delta*dm j*W j :=
    radiusRowMass_eq_duration_weight m q as ho he ha haz hz hd hkmin hfloor j
  have hW0 j : 0 ≤ W j := by
    have hf := comparisonRadiusMassWeight_memLp_two (A:=Ioo a z) (m.R)
      m.alpha.val.val (m.R_monotone).measurable measurableSet_Ioo hd hkmin
    have hiF := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hf.integrable (by norm_num))
    exact (MassCellAveraging.originalCoefficient_mem_Icc _ as ho (by positivity : 0 ≤ 1/(delta*kmin)) hiF
      (fun u _=>comparisonRadiusMassWeight_bounds _ _ _ hd hkmin u) j.val).1
  have hbLeft j : NativeRadiusSide.leftProbability mass i j ≤ mass j/delta := by
    unfold NativeRadiusSide.leftProbability
    split_ifs
    · exact div_le_div_of_nonneg_left (hmass j) hd hl
    · simpa only [zero_div] using div_nonneg (hmass j) hd.le
  have hbRight j : NativeRadiusSide.rightProbability mass i j ≤ mass j/delta := by
    unfold NativeRadiusSide.rightProbability
    split_ifs
    · exact div_le_div_of_nonneg_left (hmass j) hd hr
    · simpa only [zero_div] using div_nonneg (hmass j) hd.le
  have hratio j (hnz : mass j≠0) : (mass j/delta)/dm j ≤ W j := by
    have hdj : dm j≠0 := by
      intro h
      exact hnz (radiusRowMass_zero_of_zero_mass m q as J a z j h)
    have hbound := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (hdom j) hd.le) (hdm j)
    rw [heq j] at hbound
    have hcanc : (delta*dm j*W j/delta)/dm j=W j := by field_simp [hd.ne',hdj]
    exact hbound.trans_eq hcanc
  constructor
  · intro j
    refine ⟨NativeRadiusSide.leftCoefficient_nonneg dm mass hdm hmass i j,?_⟩
    change NativeRadiusSide.leftCoefficient dm mass i j ≤ W j
    by_cases hmj : mass j=0
    · simpa only [NativeRadiusSide.leftCoefficient,hmj,ite_true] using hW0 j
    · simp only [NativeRadiusSide.leftCoefficient,hmj,ite_false]
      exact (div_le_div_of_nonneg_right (hbLeft j) (hdm j)).trans (hratio j hmj)
  · intro j
    refine ⟨NativeRadiusSide.rightCoefficient_nonneg dm mass hdm hmass i j,?_⟩
    change NativeRadiusSide.rightCoefficient dm mass i j ≤ W j
    by_cases hmj : mass j=0
    · simpa only [NativeRadiusSide.rightCoefficient,hmj,ite_true] using hW0 j
    · simp only [NativeRadiusSide.rightCoefficient,hmj,ite_false]
      exact (div_le_div_of_nonneg_right (hbRight j) (hdm j)).trans (hratio j hmj)

theorem radiusCovariance_eq_original_weight (n : ℕ)
    (q : ℝ→FeatureIndex n→ℝ≥0) 
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {a z kmin : ℝ} (ha : m.rmin < a) (haz : a ≤ z) (hz : z ≤ 1)
    (hkmin : 0<kmin) (hfloor : ∀r∈Ioo a z,kmin ≤ m.k r) :
    let steps := sampleClockSteps q 0 as
    (∑i,radiusRowMass m q as Finset.univ a z i*
      actualCutCovarianceEnergy n steps (q 0) i.val)=
      nativeWeightedCovarianceEnergy n steps (q 0) Finset.univ id
        (comparisonOriginalRadiusWeights q as
          (comparisonRadiusMassWeight (m.R)
            m.alpha.val.val (Ioo a z) 1 kmin)) := by
  dsimp only
  unfold nativeWeightedCovarianceEnergy
  simp only [nativeSelectedColumn_atIndex,Finset.mem_univ,ite_true,id_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [radiusRowMass_eq_duration_weight m q as ho he
    ha haz hz (by norm_num : (0:ℝ)<1) hkmin hfloor i,one_mul]

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization

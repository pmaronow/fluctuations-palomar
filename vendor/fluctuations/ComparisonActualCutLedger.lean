module

public import ComparisonPhysicalScoreLedger
public import PhysicalCutCovarianceTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal
open LaplaceWindowFormalization

def actualCutReplicaDefect (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (k : ℕ) (c : ℝ) : ℝ :=
  rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
    (fun sigma tau=>(orderedOverlap n sigma tau-c)^2) steps k

def actualCutCovarianceEnergy (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) (k : ℕ) : ℝ :=
  ∫z,physicalCutSpinTraceCovSq n steps id k z
    ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps

theorem physicalCutPairDefectSecond_eq_actualCutReplicaDefect (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0) (c : ℝ) :
    physicalCutPairDefectSecond n pre tail q0 c=
      actualCutReplicaDefect n (pre++tail) q0 pre.length c := by
  unfold actualCutReplicaDefect rootLevelPairMean
  rw [levelPairMean_prefix]
  symm
  exact physicalPrefixTest_eq_rootedCutExpectation n pre tail ha q0 _
    (hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n)
      (fun sigma tau=>(orderedOverlap n sigma tau-c)^2) tail (ha.suffix pre tail) 0)

theorem actualCutReplicaDefect_nonneg (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : ℕ) (c : ℝ) :
    0 ≤ actualCutReplicaDefect n steps q0 k c := by
  have h := rootLevelPairMean_mono (uniformWeight_pos n) (finiteFeature n) q0
    (K:=fun _ _=>0) (L:=fun sigma tau=>(orderedOverlap n sigma tau-c)^2)
    (fun _ _=>sq_nonneg _) steps ha k
  rw [rootLevelPairMean_const (uniformWeight_pos n) (finiteFeature n) q0 steps ha k 0] at h
  exact h

theorem actualCutCovarianceEnergy_nonneg (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : ℕ) : 0 ≤ actualCutCovarianceEnergy n steps q0 k :=
  integral_nonneg (fun z=>(physicalCutSpinTraceCovSq_mem_Icc n steps ha id k z).1)

theorem actualCutCovarianceEnergy_at_prefix (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (q0 : FeatureIndex n → ℝ≥0) :
    actualCutCovarianceEnergy n (pre++tail) q0 pre.length=
      ∫z,physicalSpinTraceCovSq n tail (actualCutField pre tail z.1 z.2)
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail) := by
  unfold actualCutCovarianceEnergy
  congr 1
  funext z
  exact physicalCutSpinTraceCovSq_eq_actualCut n pre tail id z

theorem physicalSideNoiseMoment_le_actual_cut_defects (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {i j : ℕ} (hi : i ≤ steps.length) (hj : j ≤ steps.length)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hS : |physicalPathSecondMoment n steps q0 j-physicalPathSecondMoment n steps q0 i| ≤ eta) :
    physicalSideNoiseMoment n steps q0 i j ≤
      Real.sqrt (actualCutCovarianceEnergy n steps q0 i+actualCutCovarianceEnergy n steps q0 j)*
        (eta+4*Real.sqrt
          (actualCutReplicaDefect n steps q0 i (physicalPathSecondMoment n steps q0 i)+
           actualCutReplicaDefect n steps q0 j (physicalPathSecondMoment n steps q0 j))) := by
  have hordered {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps.length)
      (hS : |physicalPathSecondMoment n steps q0 j-physicalPathSecondMoment n steps q0 i| ≤ eta) :
      physicalSideNoiseMoment n steps q0 i j ≤
        Real.sqrt (actualCutCovarianceEnergy n steps q0 i+actualCutCovarianceEnergy n steps q0 j)*
          (eta+4*Real.sqrt
            (actualCutReplicaDefect n steps q0 i (physicalPathSecondMoment n steps q0 i)+
             actualCutReplicaDefect n steps q0 j (physicalPathSecondMoment n steps q0 j))) := by
    let pre := steps.take i
    let mid := (steps.drop i).take (j-i)
    let tail := steps.drop j
    have hpre : pre.length=i := by simp [pre,min_eq_left (hij.trans hj)]
    have hpremid : pre++mid=steps.take j := by
      dsimp only [pre,mid]
      rw [List.take_drop,show i+(j-i)=j by omega]
      have he := List.take_append_drop i (steps.take j)
      simpa only [List.take_take,min_eq_left hij] using he
    have hfull : (pre++mid)++tail=steps := by rw [hpremid]; exact List.take_append_drop j steps
    have hpm : (pre++mid).length=j := by rw [hpremid]; simp [min_eq_left hj]
    have ho : OrderedSteps 0 ((pre++mid)++tail) := by simpa only [hfull] using ha
    have h := physicalSideNoiseMoment_le_two_defects n pre mid tail ho q0
      (Ci:=actualCutCovarianceEnergy n steps q0 i)
      (Si:=physicalPathSecondMoment n steps q0 i) (Sj:=physicalPathSecondMoment n steps q0 j)
      (actualCutCovarianceEnergy_nonneg n steps ha q0 i) heta hS
    dsimp only at h
    rw [← actualCutCovarianceEnergy_at_prefix] at h
    have ho' : OrderedSteps 0 (pre++(mid++tail)) := by simpa only [List.append_assoc] using ho
    rw [physicalCutPairDefectSecond_eq_actualCutReplicaDefect n pre (mid++tail) ho' q0,
      physicalCutPairDefectSecond_eq_actualCutReplicaDefect n (pre++mid) tail ho q0] at h
    rw [← List.append_assoc,hfull,hpre,hpm] at h
    exact h
  by_cases hij : i ≤ j
  · exact hordered hij hj hS
  · have hji : j ≤ i := le_of_not_ge hij
    rw [physicalSideNoiseMoment_comm]
    have h := hordered hji hi (by simpa only [abs_sub_comm] using hS)
    simpa only [add_comm] using h

theorem physical_two_sided_actual_cut_score_ledger (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (i : ℕ) (hi : i ≤ steps.length)
    (km kp : Fin (steps.length+1) → ℝ) (hkm : ∀j,0 ≤ km j) (hkp : ∀j,0 ≤ kp j)
    (hnormm : ∑j,pathMassDifferences steps 0 j*km j=1)
    (hnormp : ∑j,pathMassDifferences steps 0 j*kp j=1)
    {c eta : ℝ} (heta : 0 ≤ eta)
    (hmeanm : |(∑j,(pathMassDifferences steps 0 j*km j)*physicalPathSecondMoment n steps q0 j.val)-c| ≤ eta)
    (hmeanp : |(∑j,(pathMassDifferences steps 0 j*kp j)*physicalPathSecondMoment n steps q0 j.val)-c| ≤ eta) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let Am : PhysicalPathState (FeatureIndex n → ℝ) n steps → ℝ := fun z=>(physicalPinnedPair
      (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 km z.1 z.2).1
    let Ap : PhysicalPathState (FeatureIndex n → ℝ) n steps → ℝ := fun z=>(physicalPinnedPair
      (uniformWeight n) (finiteFeature n) (spinSource n) steps 0 kp z.1 z.2).1
    let am := fun j=>pathMassDifferences steps 0 j*km j
    let ap := fun j=>pathMassDifferences steps 0 j*kp j
    actualCutReplicaDefect n steps q0 i c ≤
      24*variance Am mu+24*variance Ap mu+6*eta^2+
        32*(∑j,am j*physicalSideNoiseMoment n steps q0 i j.val)+
        32*(∑j,ap j*physicalSideNoiseMoment n steps q0 i j.val)+
        8*(∑j,am j*(if i < j.val then physicalSideMovementMoment n steps q0 i j.val else 0))+
        8*(∑j,ap j*(if j.val < i then physicalSideMovementMoment n steps q0 i j.val else 0))+
        actualCutCovarianceEnergy n steps q0 i := by
  let P (ss : List (GaussianStep (FeatureIndex n))) (k : ℕ) : Prop :=
    ∀(km kp : Fin (ss.length+1) → ℝ) (hkm : ∀j,0 ≤ km j) (hkp : ∀j,0 ≤ kp j)
    (hnormm : ∑j,pathMassDifferences ss 0 j*km j=1)
    (hnormp : ∑j,pathMassDifferences ss 0 j*kp j=1)
    {c eta : ℝ} (heta : 0 ≤ eta)
    (hmeanm : |(∑j,(pathMassDifferences ss 0 j*km j)*physicalPathSecondMoment n ss q0 j.val)-c| ≤ eta)
    (hmeanp : |(∑j,(pathMassDifferences ss 0 j*kp j)*physicalPathSecondMoment n ss q0 j.val)-c| ≤ eta),
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 ss
    let Am : PhysicalPathState (FeatureIndex n → ℝ) n ss → ℝ := fun z=>(physicalPinnedPair
      (uniformWeight n) (finiteFeature n) (spinSource n) ss 0 km z.1 z.2).1
    let Ap : PhysicalPathState (FeatureIndex n → ℝ) n ss → ℝ := fun z=>(physicalPinnedPair
      (uniformWeight n) (finiteFeature n) (spinSource n) ss 0 kp z.1 z.2).1
    let am := fun j=>pathMassDifferences ss 0 j*km j
    let ap := fun j=>pathMassDifferences ss 0 j*kp j
    actualCutReplicaDefect n ss q0 k c ≤
      24*variance Am mu+24*variance Ap mu+6*eta^2+
        32*(∑j,am j*physicalSideNoiseMoment n ss q0 k j.val)+
        32*(∑j,ap j*physicalSideNoiseMoment n ss q0 k j.val)+
        8*(∑j,am j*(if k < j.val then physicalSideMovementMoment n ss q0 k j.val else 0))+
        8*(∑j,ap j*(if j.val < k then physicalSideMovementMoment n ss q0 k j.val else 0))+
        actualCutCovarianceEnergy n ss q0 k
  let pre := steps.take i
  let tail := steps.drop i
  have he : pre++tail=steps := List.take_append_drop i steps
  have hl : pre.length=i := by simp [pre,min_eq_left hi]
  have ho : OrderedSteps 0 (pre++tail) := by simpa only [he] using ha
  have hp : P (pre++tail) pre.length := by
    intro km kp hkm hkp hnormm hnormp c eta heta hmeanm hmeanp
    have h := physical_two_sided_defect_score_ledger n pre tail ho q0 km kp
      hkm hkp hnormm hnormp heta hmeanm hmeanp
    dsimp only at h
    rw [physicalCutPairDefectSecond_eq_actualCutReplicaDefect n pre tail ho q0,
      ← actualCutCovarianceEnergy_at_prefix] at h
    exact h
  rw [he,hl] at hp
  exact hp km kp hkm hkp hnormm hnormp heta hmeanm hmeanp

end OAI.SKFluctuations

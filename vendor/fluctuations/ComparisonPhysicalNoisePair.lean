module

public import ComparisonWholeUnitPhysicalSampling
public import ComparisonNoiseMarginals

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem physicalCutPairDefectSecond_nonneg (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0) (c : ℝ) :
    0 ≤ physicalCutPairDefectSecond n pre tail q0 c := by
  unfold physicalCutPairDefectSecond
  apply integral_nonneg
  intro z
  change (0:ℝ) ≤ _
  have h := hierarchyPairMean_mono (uniformWeight_pos n) (finiteFeature n)
    (K:=fun _ _=>0) (L:=fun sigma tau=>(orderedOverlap n sigma tau-c)^2)
    (fun _ _=>sq_nonneg _) tail (ha.suffix pre tail) (actualCutField pre tail z.1 z.2)
  simpa only [hierarchyPairMean_const (uniformWeight_pos n) (finiteFeature n)
    tail (ha.suffix pre tail)] using h

theorem physical_ordered_noise_le_two_defects (n : ℕ)
    (pre mid tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 ((pre++mid)++tail)) (q0 : FeatureIndex n → ℝ≥0)
    {Si Sj Ci eta : ℝ} (hCi : 0 ≤ Ci) (heta : 0 ≤ eta) (hS : |Sj-Si| ≤ eta) :
    let steps := (pre++mid)++tail
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let X := actualSpinPath n steps id
    let Cj := ∫z,physicalSpinTraceCovSq n tail (actualCutField (pre++mid) tail z.1 z.2) ∂mu
    let Di := physicalCutPairDefectSecond n pre (mid++tail) q0 Si
    let Dj := physicalCutPairDefectSecond n (pre++mid) tail q0 Sj
    (∫z,(inner ℝ (X (steps.length+1) z-X (pre++mid).length z)
      (X (pre++mid).length z-X pre.length z))^2 ∂mu) ≤
      Real.sqrt (Ci+Cj)*(eta+4*Real.sqrt (Di+Dj)) := by
  dsimp only
  let steps := (pre++mid)++tail
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  let Cj := ∫z,physicalSpinTraceCovSq n tail (actualCutField (pre++mid) tail z.1 z.2) ∂mu
  let Di := physicalCutPairDefectSecond n pre (mid++tail) q0 Si
  let Dj := physicalCutPairDefectSecond n (pre++mid) tail q0 Sj
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hfull : OrderedSteps 0 (pre++(mid++tail)) := by
    simpa only [List.append_assoc] using ha
  have hDi : 0 ≤ Di := physicalCutPairDefectSecond_nonneg n pre (mid++tail) hfull q0 Si
  have hDj : 0 ≤ Dj := physicalCutPairDefectSecond_nonneg n (pre++mid) tail ha q0 Sj
  have hCj : 0 ≤ Cj := integral_nonneg (fun _=>Finset.sum_nonneg
    (fun _ _=>Finset.sum_nonneg (fun _ _=>sq_nonneg _)))
  have hX (k : ℕ) : Measurable (X k) := actualSpinPath_measurable n steps ha id measurable_id k
  have hbound (k l : ℕ) (z) : ‖X k z-X l z‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have hk := actualSpinPath_norm_le n steps ha id k z
      have hl := actualSpinPath_norm_le n steps ha id l z
      linarith)
  have hV : MemLp (fun z=>‖X (pre++mid).length z-X pre.length z‖^2) 2 mu := by
    apply MemLp.of_bound (((hX _).sub (hX _)).norm.pow_const 2).aestronglyMeasurable 4
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    change ‖X (pre++mid).length z-X pre.length z‖^2 ≤ 4
    nlinarith [hbound (pre++mid).length pre.length z,norm_nonneg (X (pre++mid).length z-X pre.length z)]
  have hmoment := momentNorm_two_sq_integral mu hV
  have hfour (z) : (‖X (pre++mid).length z-X pre.length z‖^2)^2=
      ‖X (pre++mid).length z-X pre.length z‖^4 := by ring
  simp only [hfour] at hmoment
  have hm := physical_movement_fourth_moment_le_pair n pre mid tail hfull q0 Si Sj
  dsimp only at hm
  have hm' : momentNorm mu (fun z=>‖X (pre++mid).length z-X pre.length z‖^2) 2 ≤
      |Sj-Si|+3*Real.sqrt Di+Real.sqrt Dj := by
    let F (ss : List (GaussianStep (FeatureIndex n))) :=
      momentNorm (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 ss)
        (fun z=>‖actualSpinPath n ss id (pre++mid).length z-actualSpinPath n ss id pre.length z‖^2) 2
    change F (pre++(mid++tail)) ≤ |Sj-Si|+3*Real.sqrt Di+Real.sqrt Dj at hm
    rw [← List.append_assoc] at hm
    exact hm
  have hrDi := Real.sqrt_le_sqrt (le_add_of_nonneg_right hDj : Di ≤ Di+Dj)
  have hrDj := Real.sqrt_le_sqrt (le_add_of_nonneg_left hDi : Dj ≤ Di+Dj)
  have hM : Real.sqrt (∫z,‖X (pre++mid).length z-X pre.length z‖^4 ∂mu) ≤
      eta+4*Real.sqrt (Di+Dj) := by
    rw [← hmoment,Real.sqrt_sq (momentNorm_nonneg (μ:=mu) _ _)]
    linarith
  have hnoise := physical_ordered_noise_integral_le_trace n (pre++mid) tail ha q0
    (i:=pre.length) (by simp)
  dsimp only at hnoise
  change _ ≤ Real.sqrt Cj*Real.sqrt (∫z,‖X (pre++mid).length z-X pre.length z‖^4 ∂mu) at hnoise
  have hC := Real.sqrt_le_sqrt (le_add_of_nonneg_left hCi : Cj ≤ Ci+Cj)
  have hprod := mul_le_mul hC hM (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hnoise.trans hprod

end OAI.SKFluctuations

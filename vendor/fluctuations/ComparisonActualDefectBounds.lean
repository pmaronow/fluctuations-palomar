module

public import ComparisonSelectedScore

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem actualCutReplicaDefect_le_four (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : ℕ) {c : ℝ} (hc : c∈Icc (-1:ℝ) 1) :
    actualCutReplicaDefect n steps q0 k c ≤ 4 := by
  have hb sigma tau : (orderedOverlap n sigma tau-c)^2 ≤ 4 := by
    have hO := (abs_le.mp (orderedOverlap_abs_le_one n sigma tau))
    nlinarith [hc.1,hc.2]
  have h := rootLevelPairMean_mono (uniformWeight_pos n) (finiteFeature n) q0
    (K:=fun sigma tau=>(orderedOverlap n sigma tau-c)^2) (L:=fun _ _=>(4:ℝ)) hb steps ha k
  rw [rootLevelPairMean_const (uniformWeight_pos n) (finiteFeature n) q0 steps ha k 4] at h
  exact h

theorem actualCenteredCutReplicaDefect_mem_Icc (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : ℕ) (hk : k ≤ steps.length) :
    actualCutReplicaDefect n steps q0 k (physicalPathSecondMoment n steps q0 k)∈Icc (0:ℝ) 4 := by
  refine ⟨actualCutReplicaDefect_nonneg n steps ha q0 k _,actualCutReplicaDefect_le_four n steps ha q0 k ?_⟩
  have hS := rootLevelPairMean_SK_bounds n (uniformWeight_pos n) (finiteFeature n) q0 steps ha k
  rw [← physicalSecondMoment_eq_rootLevelPairMean n steps ha q0 k hk] at hS
  exact ⟨by linarith [hS.1],hS.2.1⟩

end OAI.SKFluctuations

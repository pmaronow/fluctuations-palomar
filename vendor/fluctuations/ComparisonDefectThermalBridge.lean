module

public import ComparisonActualIntegratedDefect
public import SKFluctuationsOAI.Probability.SKFluctuations.VarianceTestZeroRoot

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem actualCutReplicaDefect_eq_centered_pair_variance (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : ℕ) (c : ℝ) :
    actualCutReplicaDefect n steps q0 k c=
      rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
        (fun sigma tau=>(orderedOverlap n sigma tau)^2) steps k-
      2*c*rootLevelPairMean (uniformWeight n) (finiteFeature n) q0 (orderedOverlap n) steps k+c^2 := by
  have he : (fun sigma tau:Spin n=>(orderedOverlap n sigma tau-c)^2)=
      (fun sigma tau=>1*((orderedOverlap n sigma tau)^2+(-2*c)*orderedOverlap n sigma tau)+1*c^2) := by
    funext sigma tau
    ring
  unfold actualCutReplicaDefect
  rw [he,rootLevelPairMean_linear (uniformWeight_pos n) (finiteFeature n) q0
    (fun sigma tau=>(orderedOverlap n sigma tau)^2+(-2*c)*orderedOverlap n sigma tau)
    (fun _ _=>c^2) steps ha 1 1 k]
  have he2 : (fun sigma tau:Spin n=>(orderedOverlap n sigma tau)^2+(-2*c)*orderedOverlap n sigma tau)=
      (fun sigma tau=>1*(orderedOverlap n sigma tau)^2+(-2*c)*orderedOverlap n sigma tau) := by
    funext sigma tau
    ring
  rw [he2,rootLevelPairMean_linear (uniformWeight_pos n) (finiteFeature n) q0
    (fun sigma tau=>(orderedOverlap n sigma tau)^2) (orderedOverlap n) steps ha 1 (-2*c) k,
    rootLevelPairMean_const (uniformWeight_pos n) (finiteFeature n) q0 steps ha k (c^2)]
  ring

theorem actualCenteredCutReplicaDefect_eq_thermal_defect (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : ℕ) (hk : k ≤ steps.length) :
    actualCutReplicaDefect n steps q0 k (physicalPathSecondMoment n steps q0 k)=
      rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
        (fun sigma tau=>(orderedOverlap n sigma tau)^2) steps k-
      (physicalPathSecondMoment n steps q0 k)^2 := by
  rw [actualCutReplicaDefect_eq_centered_pair_variance n steps ha q0 k,
    ← physicalSecondMoment_eq_rootLevelPairMean n steps ha q0 k hk]
  ring

theorem actualCenteredCutReplicaDefect_mem_unit_interval (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (k : ℕ) (hk : k ≤ steps.length) :
    actualCutReplicaDefect n steps q0 k (physicalPathSecondMoment n steps q0 k)∈Icc (0:ℝ) 1 := by
  refine ⟨actualCutReplicaDefect_nonneg n steps ha q0 k _,?_⟩
  rw [actualCenteredCutReplicaDefect_eq_thermal_defect n steps ha q0 k hk]
  have hB := (rootLevelPairMean_SK_bounds n (uniformWeight_pos n) (finiteFeature n) q0 steps ha k).2.2.2
  nlinarith [sq_nonneg (physicalPathSecondMoment n steps q0 k)]

end OAI.SKFluctuations

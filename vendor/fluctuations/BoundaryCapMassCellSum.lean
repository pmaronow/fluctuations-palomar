module

public import PhysicalBoundaryCapLaw
public import FiniteMassBandIntegral
public import WallSampledFieldGap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalWeightedCutSum_zero_prefix (k : ℕ) (durations : List ℝ≥0) (C : ℕ → ℝ) :
    physicalWeightedCutSum (List.replicate k 0 ++ durations) C =
      physicalWeightedCutSum durations (fun j => C (k+j)) := by
  induction k generalizing C with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,physicalWeightedCutSum,NNReal.coe_zero,zero_mul,zero_add,ih]
    congr 1
    funext j
    congr 1
    omega

theorem physicalWeightedCutSum_sampleMassDurations {a : ℝ} (as : List PositiveMass)
    (ha : MassOrdered a as) (C : ℕ → ℝ) :
    physicalWeightedCutSum (sampleMassDurations a as) C = massCellSum as a C := by
  induction as generalizing a C with
  | nil => rfl
  | cons b bs ih =>
    simp only [sampleMassDurations,physicalWeightedCutSum,massCellSum,
      Real.coe_toNNReal _ (sub_nonneg.mpr ha.2.1),ih ha.2.2]

theorem physicalBoundaryCap_massCellSum (n : ℕ) (q : ℝ → FeatureIndex n → ℝ≥0)
    (before band : List PositiveMass) {a : ℝ}
    (hband : MassOrdered a band) (tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q 0 k))
      (physicalFiniteCapBoundaryTrace n
        (List.replicate (sampleClockSteps q 0 before).length 0 ++ sampleMassDurations a band)
        (sampleClockSteps q 0 before ++ sampleClockSteps q a band) tail ha) 0 =
      massCellSum band a (fun j =>
        ∫ p, physicalCutSourceSquareTrace n
          ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail) id
          (before.length+j) p
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0)
            ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)) := by
  have hlength : (List.replicate (sampleClockSteps q 0 before).length 0 ++ sampleMassDurations a band).length ≤
      (sampleClockSteps q 0 before ++ sampleClockSteps q a band).length := by
    have hd : (sampleMassDurations a band).length = band.length := by
      clear hband ha
      induction band generalizing a with
      | nil => rfl
      | cons b bs ih => simp only [sampleMassDurations,List.length_cons,ih]
    simp only [List.length_append,List.length_replicate,sampleClockSteps_length,hd,le_refl]
  rw [physicalFiniteCapBoundaryTrace_rooted_eq_weightedCuts n _ _ _ _ ha hlength,
    physicalWeightedCutSum_zero_prefix,physicalWeightedCutSum_sampleMassDurations band hband]
  simp only [sampleClockSteps_length]

end OAI.SKFluctuations.LaplaceWindowFormalization

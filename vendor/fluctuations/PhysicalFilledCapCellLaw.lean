module

public import PhysicalFilledTraceBound
public import PhysicalBoundaryCapLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

def physicalCapCellTrace (n d : ℕ) (e : Fin (d+1) ≃ FeatureIndex (n+1)) :
    (pre tail : List (GaussianStep (FeatureIndex (n+1))))→
      {a : ℝ}→OrderedSteps a (pre++tail)→ℕ→(FeatureIndex (n+1)→ℝ)→ℝ
  | [],_,_,_,_,_=>0
  | (m,q)::pre,tail,_,ha,0,x=>
      ∫t in 0..1,physicalFilledSourceTraceExpectation (n+1) d
        (physicalJointGaussianDriver (n+1) d e q) (pre++tail) ha.2.2.2 ha.2.2.1 1 t x
  | (m,q)::pre,tail,_,ha,j+1,x=>
      shiftedMean (Measure.pi fun k=>gaussianReal 0 (q k)) m
        (gaussianHierarchy (uniformWeight (n+1)) (finiteFeature (n+1)) (pre++tail))
        (physicalCapCellTrace n d e pre tail ha.2.2.2 j) x

theorem physicalCapCellTrace_smooth (n d : ℕ) (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (pre tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (j : ℕ) :
    BddSmooth 0 (physicalCapCellTrace n d e pre tail ha j) := by
  induction pre generalizing a j with
  | nil=>exact BddSmooth.const 0 0
  | cons st pre ih=>
    rcases st with ⟨m,q⟩
    cases j with
    | zero=>exact physicalFilledSourceTrace_integral_smooth (n+1) d _ (pre++tail) ha.2.2.2 ha.2.2.1 1
    | succ j=>
      change BddSmooth 0 (fun x=>shiftedMean (Measure.pi fun k=>gaussianReal 0 (q k)) m
        (gaussianHierarchy (uniformWeight (n+1)) (finiteFeature (n+1)) (pre++tail))
        (physicalCapCellTrace n d e pre tail ha.2.2.2 j) x)
      exact (ih ha.2.2.2 j).shiftedMean
        (gaussianHierarchy_regular (uniformWeight_pos (n+1)) (finiteFeature (n+1)) (pre++tail) ha.2.2.2 0)
        (gaussianHierarchy_integrable (uniformWeight_pos (n+1)) (finiteFeature (n+1)) (pre++tail) ha.2.2.2 m q)

theorem physicalCapCellTrace_mem_Icc (n d : ℕ) (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (pre tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (j : ℕ) (x : FeatureIndex (n+1)→ℝ) :
    physicalCapCellTrace n d e pre tail ha j x∈Icc (0:ℝ) 1 := by
  induction pre generalizing a j x with
  | nil=>norm_num [physicalCapCellTrace]
  | cons st pre ih=>
    rcases st with ⟨m,q⟩
    cases j with
    | zero=>
      refine ⟨?_,physicalFilledSourceTrace_integral_le_one (n+1) d e q (pre++tail) ha.2.2.2 ha.2.2.1 x⟩
      apply intervalIntegral.integral_nonneg zero_le_one
      intro t _
      exact physicalFilledSourceTraceExpectation_nonneg (n+1) d _ (pre++tail) ha.2.2.2 ha.2.2.1 1 t x
    | succ j=>
      have hi := gaussianHierarchy_integrable (uniformWeight_pos (n+1)) (finiteFeature (n+1)) (pre++tail) ha.2.2.2 m q x
      have hlow := shiftedMean_nonneg (fun y=>(ih ha.2.2.2 j y).1) hi
      have hupp := shiftedMean_mono (physicalCapCellTrace_smooth n d e pre tail ha.2.2.2 j)
        (BddSmooth.const 0 (1:ℝ)) (fun y=>(ih ha.2.2.2 j y).2) hi
      rw [shiftedMean_const _ hi] at hupp
      exact ⟨hlow,hupp⟩

theorem physicalWeightedCutSum_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (durations : List ℝ≥0) (C : ℕ→E→ℝ) (hC : ∀j,BddSmooth 0 (C j)) :
    BddSmooth 0 (fun x=>physicalWeightedCutSum durations (fun j=>C j x)) := by
  induction durations generalizing C with
  | nil=>exact BddSmooth.const 0 0
  | cons w ws ih=>
    exact ((hC 0).const_mul w).add
      (ih (fun j=>C (j+1)) (fun j=>hC (j+1)))

theorem shiftedMean_physicalWeightedCutSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (m : ℝ) (F : E→ℝ)
    (durations : List ℝ≥0) (C : ℕ→E→ℝ) (hC : ∀j,BddSmooth 0 (C j)) (x : E)
    (hi : Integrable (fun z=>Real.exp (m*F (x+z))) ν) :
    shiftedMean ν m F (fun y=>physicalWeightedCutSum durations (fun j=>C j y)) x=
      physicalWeightedCutSum durations (fun j=>shiftedMean ν m F (C j) x) := by
  induction durations generalizing C with
  | nil=>simpa only [physicalWeightedCutSum] using shiftedMean_const (0:ℝ) hi
  | cons w ws ih=>
    simp only [physicalWeightedCutSum]
    rw [shiftedMean_add ((hC 0).const_mul w)
      (physicalWeightedCutSum_smooth ws (fun j=>C (j+1)) (fun j=>hC (j+1))) hi,
      shiftedMean_const_mul,ih _ (fun j=>hC (j+1))]

theorem physicalFiniteCapIndexedTrace_eq_weightedCellSum (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (hlen : durations.length ≤ pre.length)
    (x : FeatureIndex (n+1)→ℝ) :
    physicalFiniteCapIndexedTrace n d e durations pre tail ha x=
      physicalWeightedCutSum durations (fun j=>physicalCapCellTrace n d e pre tail ha j x) := by
  induction pre generalizing a durations x with
  | nil=>have : durations=[] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
         subst durations;rfl
  | cons st pre ih=>
    cases durations with
    | nil=>rfl
    | cons w ws=>
      rcases st with ⟨m,q⟩
      have hlen' : ws.length ≤ pre.length := by simpa only [List.length_cons,Nat.add_le_add_iff_right] using hlen
      simp only [physicalFiniteCapIndexedTrace,physicalWeightedCutSum]
      rw [funext (ih ws ha.2.2.2 hlen')]
      rw [shiftedMean_physicalWeightedCutSum _ _ _ ws _
        (fun j=>physicalCapCellTrace_smooth n d e pre tail ha.2.2.2 j) x
        (gaussianHierarchy_integrable (uniformWeight_pos (n+1)) (finiteFeature (n+1)) (pre++tail) ha.2.2.2 m q x)]
      rfl

def physicalRootedCapCellTrace (n d : ℕ) (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (q₀ : FeatureIndex (n+1)→ℝ≥0) (pre tail : List (GaussianStep (FeatureIndex (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (j : ℕ) : ℝ :=
    zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k)) (physicalCapCellTrace n d e pre tail ha j) 0

theorem physicalRootedCapCellTrace_mem_Icc (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1)→ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (j : ℕ) :
    physicalRootedCapCellTrace n d e q₀ pre tail ha j∈Icc (0:ℝ) 1 := by
  unfold physicalRootedCapCellTrace zeroContinuation
  simp only [zero_add]
  constructor
  · exact integral_nonneg fun x=>(physicalCapCellTrace_mem_Icc n d e pre tail ha j x).1
  · have hh := integral_mono (μ := Measure.pi fun k=>gaussianReal 0 (q₀ k)) (physicalCapCellTrace_smooth n d e pre tail ha j).integrable
      (integrable_const (1:ℝ)) (fun x=>(physicalCapCellTrace_mem_Icc n d e pre tail ha j x).2)
    simpa only [integral_const,probReal_univ,one_smul] using hh

theorem physicalRootedCapIndexedTrace_eq_weightedCellSum (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1)→ℝ≥0)
    (durations : List ℝ≥0) (pre tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (hlen : durations.length ≤ pre.length) :
    zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k))
      (physicalFiniteCapIndexedTrace n d e durations pre tail ha) 0=
      physicalWeightedCutSum durations (fun j=>physicalRootedCapCellTrace n d e q₀ pre tail ha j) := by
  unfold zeroContinuation
  simp only [zero_add]
  simp_rw [physicalFiniteCapIndexedTrace_eq_weightedCellSum n d e durations pre tail ha hlen]
  simpa only [physicalRootedCapCellTrace,zeroContinuation,zero_add] using
    physicalWeightedCutSum_integral (Measure.pi fun k=>gaussianReal 0 (q₀ k)) durations
    (fun j x=>physicalCapCellTrace n d e pre tail ha j x)
    (fun j=>(physicalCapCellTrace_smooth n d e pre tail ha j).integrable)

end OAI.SKFluctuations.LaplaceWindowFormalization

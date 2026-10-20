module

public import ComparisonSignedCavityStarClockTransport
public import SKFluctuationsOAI.Probability.SKFluctuations.CavityFrozenJet

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy Cavity

theorem featureGauge_globalFlip_eq_of_zero_field (n : ℕ)
    (x : FeatureIndex n → ℝ) (hx : ∀ i, x (Sum.inl i) = 0) :
    featureGauge (fun _ : Fin n => false) x = x := by
  ext j
  change featureSigns (fun _ : Fin n => false) j * x j = x j
  rcases j with i | (_ | e)
  · simp [featureSigns, spinValue, hx]
  · simp [featureSigns]
  · simp [featureSigns, spinValue]

theorem spinMean_zero_of_zero_field (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ) (hx : ∀ i, x (Sum.inl i) = 0) (i : Fin n) :
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) steps x = 0 := by
  have h := spinMean_gauge n steps (fun _ : Fin n => false) x i
  rw [featureGauge_globalFlip_eq_of_zero_field n x hx] at h
  have he : (fun σ => finiteFeature n σ (spinSource n i)) =
      (fun σ => normalizedSpin n σ i) := by
    funext σ
    exact finiteFeature_source n σ i
  rw [he] at h
  simp only [spinValue, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul] at h
  linarith

theorem hierarchyPairMean_overlap_zero_of_zero_field (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (hx : ∀ i, x (Sum.inl i) = 0) :
    hierarchyPairMean (uniformWeight n) (finiteFeature n) (orderedOverlap n) steps x = 0 := by
  rw [hierarchyPairMean_overlap_eq_norm n steps ha x]
  have he : (fun i => gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) steps x) = 0 := by
    funext i
    exact spinMean_zero_of_zero_field n steps x hx i
  rw [he]
  simp

namespace Cavity

theorem finitePhysicalMean_zero_of_bare_root (n : ℕ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (b h : ℕ → ℝ) (hh0 : h 0 = 0) :
    finitePhysicalMean n as b h 0 = 0 := by
  let q := physicalCompletedClock n b h
  let steps := diagonalBoundarySteps as (q 0) (fun k => q (k+1))
  have hs : OrderedSteps 0 steps := diagonalBoundarySteps_ordered as (by norm_num) (by norm_num)
    ho.pairwise ho.members_le_one (fun a _ => a.property.le) _ _
  have hsupport : ∀ᵐ x ∂Measure.pi (fun j => gaussianReal 0 (Real.toNNReal (q 0 j))),
      ∀ i : Fin n, x (Sum.inl i) = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply gaussian_coordinate_zero_ae
    simp [q, physicalCompletedClock, hh0]
  change physicalPathSecondMoment n steps (fun j => Real.toNNReal (q 0 j)) 0 = 0
  rw [physicalSecondMoment_eq_rootLevelPairMean n steps hs _ 0 (Nat.zero_le _)]
  unfold rootLevelPairMean zeroContinuation
  apply integral_eq_zero_of_ae
  filter_upwards [hsupport] with x hx
  have he : levelPairMean (uniformWeight n) (finiteFeature n) (orderedOverlap n) steps 0 =
      hierarchyPairMean (uniformWeight n) (finiteFeature n) (orderedOverlap n) steps := by
    cases steps <;> rfl
  simp only [he, zero_add]
  exact hierarchyPairMean_overlap_zero_of_zero_field n steps hs x hx

theorem finitePhysicalMixedClock_zero_of_bare_root (n : ℕ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (b h : ℕ → ℝ) (hh0 : h 0 = 0) :
    finitePhysicalMixedClock n as b h 0 = 0 := by
  simp only [finitePhysicalMixedClock, hh0, finitePhysicalMean_zero_of_bare_root n ho b h hh0,
    mul_zero, add_zero]

end Cavity
end OAI.SKFluctuations

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity

theorem retainedStarMixedClock_zero_of_zero_root_field (n : ℕ)
    (bf hf : ℝ → ℝ≥0) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (hh0 : hf 0 = 0) : retainedStarMixedClock n bf hf as 0 = 0 := by
  apply finitePhysicalMixedClock_zero_of_bare_root (n+1) ho
  simp [retainedStarField, partitionPoint, hh0]

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem bare_root_field_zero
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hh : M.h 0 = 0) : M.hf 0 = 0 := by
  have hR : M.R 0 = 0 := comparisonSweepQuantile_zero M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.alpha
  change Real.toNNReal (M.h 0+laplaceComparisonStrength M.context.d M.lam (M.R 0)*M.R 0) = 0
  rw [hR, hh]
  simp

theorem bare_retainedStarMixedClock_zero
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hh : M.h 0 = 0) {as : List PositiveMass} (ho : MassOrdered 0 as) :
    retainedStarMixedClock n M.bf M.hf as 0 = 0 :=
  retainedStarMixedClock_zero_of_zero_root_field n M.bf M.hf ho (M.bare_root_field_zero hh)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

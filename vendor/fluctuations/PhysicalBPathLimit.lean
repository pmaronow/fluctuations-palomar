module

public import PhysicalCapActualLaw
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockPathPairMeasurable

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (FeatureIndex (n + 1)) := fun _ _ => Classical.propDecidable _

def physicalSampledB (n : ℕ) (b h : ℝ → ℝ≥0) (as : List PositiveMass)
    (ha : MassOrdered 0 as) : ℝ → ℝ :=
  stepPairMoment (uniformWeight (n + 1)) (finiteFeature (n + 1))
    (completedPathClock (n + 1) b h 0)
    (sampleClockSteps (completedPathClock (n + 1) b h) 0 as)
    (sampleClockSteps_ordered _ as ha).mem_pos
    (fun σ τ => (orderedOverlap (n + 1) σ τ) ^ 2)

def physicalFeatureCoordinateBound (n : ℕ) (i : FeatureIndex (n + 1)) : ℝ :=
  ∑ σ, |finiteFeature (n + 1) σ (Pi.single i 1)|

def physicalBApproximationConstant (n : ℕ) (b h : ℝ → ℝ≥0) : ℝ :=
  ClockTree.errorJetVariation 2 0 0 *
    (4 * clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n + 1) b h))

theorem physicalSampledB_intervalIntegrable (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (a c : ℝ) :
    IntervalIntegrable (physicalSampledB n b h as ha) volume a c :=
  stepPairMoment_intervalIntegrable _ _ _ _ _ _ a c

theorem physicalOrderedPathB_intervalIntegrable (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (orderedPathB (n + 1) b h) volume 0 1 :=
  pathPairMoment_intervalIntegrable_all (uniformWeight_pos (n + 1)) (orderedFeature (n + 1))
    (orderedPathClock (n + 1) b h) (orderedPathClock_monotone (n + 1) hb hh) _

theorem physicalSampledB_l1_bound (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as = 1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) :
    (∫ u in 0..1, |physicalSampledB n b h as ha u - orderedPathB (n + 1) b h u|) ≤
      mesh * physicalBApproximationConstant n b h := by
  have hD : ∀ i, 0 ≤ physicalFeatureCoordinateBound n i := by
    intro i
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hφ : ∀ σ i, |finiteFeature (n + 1) σ (Pi.single i 1)| ≤ physicalFeatureCoordinateBound n i := by
    intro σ i
    unfold physicalFeatureCoordinateBound
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (finiteFeature (n + 1) τ (Pi.single i 1))) (Finset.mem_univ σ)
  have hP : ∀ σ τ, |(orderedOverlap (n + 1) σ τ) ^ 2| ≤ (1 : ℝ) := by
    intro σ τ
    simpa only [abs_pow, one_pow] using
      pow_le_pow_left₀ (abs_nonneg (orderedOverlap (n + 1) σ τ))
        (orderedOverlap_abs_le_one (n + 1) σ τ) 2
  have hbound := sampledPairMoment_l1_bound (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
    (physicalFeatureCoordinateBound n) hD hφ (completedPathClock (n + 1) b h)
    (completedPathClock_monotone (n + 1) hb hh) as ha he hm
    (fun σ τ => (orderedOverlap (n + 1) σ τ)^2) (by norm_num : (0 : ℝ) ≤ 1) hP
  have heq : (∫ u in 0..1, |physicalSampledB n b h as ha u - orderedPathB (n + 1) b h u|) =
      ∫ u in 0..1, |physicalSampledB n b h as ha u -
        pathPairMoment (uniformWeight (n + 1)) (finiteFeature (n + 1))
          (completedPathClock (n + 1) b h) (fun σ τ => (orderedOverlap (n + 1) σ τ)^2) u| := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u hu
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    rw [show orderedPathB (n + 1) b h u = _ from
      orderedPathPair_eq_completed (n + 1) (by omega) b h hb hh _ hu]
  rw [heq]
  calc
    _ ≤ ClockTree.errorJetVariation 2 0 0 * 1 *
        (4 * mesh * clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n + 1) b h)) := hbound
    _ = mesh * physicalBApproximationConstant n b h := by
      unfold physicalBApproximationConstant
      ring

theorem physicalSampledB_band_integral_error (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as = 1)
    {mesh a c : ℝ} (hm : PartitionMesh mesh 0 as) (ha0 : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1) :
    |(∫ u in a..c, physicalSampledB n b h as ha u) - (∫ u in a..c, orderedPathB (n + 1) b h u)| ≤
      mesh * physicalBApproximationConstant n b h := by
  have hf := physicalSampledB_intervalIntegrable n b h as ha a c
  have hg := physicalOrderedPathB_intervalIntegrable n b h hb hh
  have hsub : uIcc a c ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hac, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc ha0 hc1
  rw [← intervalIntegral.integral_sub hf (hg.mono_set hsub)]
  apply (intervalIntegral.abs_integral_le_integral_abs hac).trans
  apply le_trans ?_ (physicalSampledB_l1_bound n b h hb hh as ha he hm)
  exact intervalIntegral.integral_mono_interval ha0 hac hc1
    (Eventually.of_forall fun _ => abs_nonneg _)
    (((physicalSampledB_intervalIntegrable n b h as ha 0 1).sub hg).abs)

theorem physicalSampledB_band_integral_tendsto (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀ j, MassOrdered 0 (as j)) (he : ∀ j, partitionEnd 0 (as j) = 1)
    (hm : ∀ j, PartitionMesh (mesh j) 0 (as j)) (hmesh : Tendsto mesh atTop (𝓝 0))
    {a c : ℝ} (ha0 : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1) :
    Tendsto (fun j => ∫ u in a..c, physicalSampledB n b h (as j) (ho j) u)
      atTop (𝓝 (∫ u in a..c, orderedPathB (n + 1) b h u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun j => physicalSampledB_band_integral_error n b h hb hh (as j) (ho j) (he j) (hm j) ha0 hac hc1)
    (by simpa using hmesh.mul_const (physicalBApproximationConstant n b h))

theorem physicalOrderedPathB_band_le_of_finite (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (as : ℕ → List PositiveMass) (mesh bound : ℕ → ℝ)
    (ho : ∀ j, MassOrdered 0 (as j)) (he : ∀ j, partitionEnd 0 (as j) = 1)
    (hm : ∀ j, PartitionMesh (mesh j) 0 (as j)) (hmesh : Tendsto mesh atTop (𝓝 0))
    {a c C : ℝ} (ha0 : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1)
    (hbound : ∀ᶠ j in atTop, (∫ u in a..c, physicalSampledB n b h (as j) (ho j) u) ≤ bound j)
    (hC : Tendsto bound atTop (𝓝 C)) :
    (∫ u in a..c, orderedPathB (n + 1) b h u) ≤ C :=
  le_of_tendsto_of_tendsto
    (physicalSampledB_band_integral_tendsto n b h hb hh as mesh ho he hm hmesh ha0 hac hc1) hC hbound

theorem physicalSampledB_canonical_band_tendsto (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (us : List PositiveMass) (hu : ∀ u ∈ us, u.val ≤ 1)
    {a c : ℝ} (ha0 : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1) :
    Tendsto (fun j => ∫ u in a..c, physicalSampledB n b h (finiteCutMasses us j)
      (finiteCutMasses_ordered us hu j) u)
      atTop (𝓝 (∫ u in a..c, orderedPathB (n + 1) b h u)) :=
  physicalSampledB_band_integral_tendsto n b h hb hh (finiteCutMasses us)
    (fun j => (((j + 1 : ℕ) : ℝ))⁻¹) (finiteCutMasses_ordered us hu)
    (finiteCutMasses_end us hu) (finiteCutMasses_mesh us hu) uniformMasses_mesh_tendsto ha0 hac hc1

theorem physicalOrderedPathB_canonical_band_le (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (us : List PositiveMass) (hu : ∀ u ∈ us, u.val ≤ 1) (bound : ℕ → ℝ)
    {a c C : ℝ} (ha0 : 0 ≤ a) (hac : a ≤ c) (hc1 : c ≤ 1)
    (hbound : ∀ᶠ j in atTop, (∫ u in a..c, physicalSampledB n b h (finiteCutMasses us j)
      (finiteCutMasses_ordered us hu j) u) ≤ bound j)
    (hC : Tendsto bound atTop (𝓝 C)) :
    (∫ u in a..c, orderedPathB (n + 1) b h u) ≤ C :=
  le_of_tendsto_of_tendsto
    (physicalSampledB_canonical_band_tendsto n b h hb hh us hu ha0 hac hc1) hC hbound

theorem physicalSampledB_canonical_retained_tendsto (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (us : List PositiveMass) (hu : ∀ u ∈ us, u.val ≤ 1)
    (u : PositiveMass) (huNode : u ∈ us) :
    Tendsto (fun j => physicalSampledB n b h (finiteCutMasses us j)
      (finiteCutMasses_ordered us hu j) u.val)
      atTop (𝓝 (orderedPathB (n + 1) b h u.val)) := by
  change Tendsto _ _ (𝓝 (orderedPathPair (n + 1) b h _ u.val))
  rw [orderedPathPair_eq_completed (n + 1) (by omega) b h hb hh _ ⟨u.property, hu u huNode⟩]
  exact retainedMoment_tendsto_all (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
    (completedPathClock (n + 1) b h) (completedPathClock_monotone (n + 1) hb hh)
    (finiteCutMasses us) (fun j => (((j + 1 : ℕ) : ℝ))⁻¹)
    (finiteCutMasses_ordered us hu) (finiteCutMasses_mesh us hu)
    (finiteCutMasses_end us hu) uniformMasses_mesh_tendsto u (hu u huNode)
    (fun j => finiteCutMasses_nodes us j huNode) _

end
end OAI.SKFluctuations.LaplaceWindowFormalization

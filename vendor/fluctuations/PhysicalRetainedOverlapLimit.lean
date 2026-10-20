module

public import PhysicalLocalCapTrace
public import PhysicalBPathLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (FeatureIndex (n+1)) := fun _ _=>Classical.propDecidable _
set_option maxHeartbeats 1000000

theorem physicalPathSecondMoment_eq_stepPairDisorder (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 (pre++tail)) (q₀ : FeatureIndex n→ℝ≥0) :
    physicalPathSecondMoment n (pre++tail) q₀ pre.length=
      stepPairDisorder (uniformWeight n) (finiteFeature n) q₀ pre tail (orderedOverlap n) 0 := by
  rw [←physicalPrefixMeanSq_eq_pathSecondMoment n pre tail ha q₀]
  have hh := funext (physicalSpinMeanSq_eq_pairMean n tail (ha.suffix pre tail))
  rw [hh]
  have he := funext (hierarchyPairMean_eq_nested (uniformWeight_pos n) (finiteFeature n) (orderedOverlap n) tail (ha.suffix pre tail))
  rw [he]
  rfl

theorem physicalRetainedCutSecondMoment_error (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {u mesh : ℝ} (hu : u∈Ioc (0:ℝ) 1) (before after : List PositiveMass)
    (ho : MassOrdered 0 before) (ht : MassOrdered u after)
    (hau : ∀a∈before,a.val ≤ u) (he : partitionEnd 0 before=u)
    (hf : partitionEnd u after=1) (hm : PartitionMesh mesh 0 (before++after)) :
    let q := completedPathClock (n+1) b h
    let pre := sampleClockSteps q 0 before
    let tail := sampleClockSteps q u after
    physicalPathSecondMoment (n+1) (pre++tail) (q 0) pre.length-
      orderedPathS (n+1) b h u ≤ 
        mesh*(2*ClockTree.errorJetVariation 2 0 0*
          clockVariationBound (physicalFeatureCoordinateBound n) q) ∧
    orderedPathS (n+1) b h u-
      physicalPathSecondMoment (n+1) (pre++tail) (q 0) pre.length ≤ 
        mesh*(2*ClockTree.errorJetVariation 2 0 0*
          clockVariationBound (physicalFeatureCoordinateBound n) q) := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let pre := sampleClockSteps q 0 before
  let tail := sampleClockSteps q u after
  let D := physicalFeatureCoordinateBound n
  have hq := completedPathClock_monotone (n+1) hb hh
  have hfull : MassOrdered 0 (before++after) := ho.append_end (he.symm ▸ ht)
  have hpre := sampleClockSteps_ordered q before ho
  have htail := sampleClockSteps_ordered q after ht
  have hsteps : pre++tail=sampleClockSteps q 0 (before++after) := by
    dsimp [pre,tail]
    rw [sampleClockSteps_append,he]
  have hordered : OrderedSteps 0 (pre++tail) := by
    rw [hsteps]
    exact sampleClockSteps_ordered q _ hfull
  have hD : ∀i,0 ≤ D i := fun i=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hφ : ∀σ i,|finiteFeature (n+1) σ (Pi.single i 1)| ≤ D i := by
    intro σ i
    exact Finset.single_le_sum (fun τ _=>abs_nonneg (finiteFeature (n+1) τ (Pi.single i 1))) (Finset.mem_univ σ)
  have hP : ∀σ τ,|orderedOverlap (n+1) σ τ| ≤ (1:ℝ) := orderedOverlap_abs_le_one (n+1)
  have hcmp := stepPairDisorder_path_comparison (uniformWeight_pos (n+1)) (finiteFeature (n+1))
    D hD hφ (q 0) pre tail ⟨u,hu.1⟩ hu.2 hpre htail
    (sampleClockSteps_mass_le q 0 before hau) q hq (orderedOverlap (n+1))
    (by norm_num : (0:ℝ) ≤ 1) hP 0
  have hdist : stepPathPairDistance D (q 0) pre tail q u ≤ 2*mesh*clockVariationBound D q := by
    unfold stepPathPairDistance
    rw [sampleClockSteps_terminal q hq 0 before ho,he,hsteps,
      sampleClockSteps_terminal q hq 0 (before++after) hfull,
      partitionEnd_append,he,hf]
    simp only [clockCoordinateDistance,sub_self,abs_zero,zero_mul,Finset.sum_const_zero,zero_add,add_zero]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (sample_stepPathClockDistance_le D q hq _ hfull hm) (by norm_num : (0:ℝ)≤2)
  have habs : |physicalPathSecondMoment (n+1) (pre++tail) (q 0) pre.length-
      orderedPathS (n+1) b h u| ≤ mesh*(2*ClockTree.errorJetVariation 2 0 0*clockVariationBound D q) := by
    rw [physicalPathSecondMoment_eq_stepPairDisorder (n+1) pre tail hordered (q 0)]
    have heq : orderedPathS (n+1) b h u=
        pathPairDisorder (uniformWeight (n+1)) (finiteFeature (n+1)) q ⟨u,hu.1⟩ (orderedOverlap (n+1)) 0 := by
      rw [orderedPathS,orderedPathPair_eq_completed (n+1) (by omega) b h hb hh _ hu]
      simp only [pathPairMoment,dite_eq_left hu.1]
      rfl
    rw [heq]
    have hscaled := mul_le_mul_of_nonneg_left hdist (ClockTree.errorJetVariation_nonneg 2 0 0)
    simp only [mul_one] at hcmp
    nlinarith [hcmp,hscaled]
  refine ⟨(le_abs_self _).trans habs,?_⟩
  simpa only [neg_sub] using (neg_le_abs _).trans habs

theorem physicalRetainedCutSecondMoment_tendsto (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {u : ℝ} (hu : u∈Ioc (0:ℝ) 1) (before after : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (before j)) (ht : ∀j,MassOrdered u (after j))
    (hau : ∀j,∀a∈before j,a.val ≤ u) (he : ∀j,partitionEnd 0 (before j)=u)
    (hf : ∀j,partitionEnd u (after j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (before j++after j))
    (hmesh : Tendsto mesh atTop (𝓝 0)) :
    let q := completedPathClock (n+1) b h
    Tendsto (fun j=>physicalPathSecondMoment (n+1)
      (sampleClockSteps q 0 (before j)++sampleClockSteps q u (after j))
      (q 0) (sampleClockSteps q 0 (before j)).length) atTop
      (𝓝 (orderedPathS (n+1) b h u)) := by
  dsimp only
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  have herr := hmesh.mul_const (2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n+1) b h))
  simp only [zero_mul] at herr
  apply squeeze_zero (fun _=>abs_nonneg _) (fun j=>?_) herr
  have hh := physicalRetainedCutSecondMoment_error n b h hb hh hu (before j) (after j)
    (ho j) (ht j) (hau j) (he j) (hf j) (hm j)
  exact abs_le.mpr ⟨by linarith [hh.2],hh.1⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

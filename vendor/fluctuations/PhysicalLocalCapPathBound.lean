module

public import PhysicalRetainedOverlapLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (FeatureIndex (n+1)) := fun _ _=>Classical.propDecidable _
set_option maxHeartbeats 1000000

theorem physicalSampledLocalCapTrace_le_ordered_increment (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {u v mesh g : ℝ} (hu : u∈Ioc (0:ℝ) 1) (hv : v∈Ioc (0:ℝ) 1)
    (huv : u ≤ v) (before band after : List PositiveMass) (durations : List ℝ≥0)
    (ho : MassOrdered 0 before) (ht : MassOrdered u band) (hf : MassOrdered v after)
    (hau : ∀a∈before,a.val ≤ u) (hbv : ∀a∈band,a.val ≤ v)
    (he : partitionEnd 0 before=u) (hmid : partitionEnd u band=v)
    (hend : partitionEnd v after=1) (hm : PartitionMesh mesh 0 ((before++band)++after))
    (hg : 0<g)
    (hslope : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1)))=>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) durations
      (sampleClockSteps (completedPathClock (n+1) b h) u band)) :
    let q := completedPathClock (n+1) b h
    let common := sampleClockSteps q 0 before
    let mid := sampleClockSteps q u band
    let tail := sampleClockSteps q v after
    let hfull : OrderedSteps 0 ((common++mid)++tail) := by
      have ho' : MassOrdered 0 ((before++band)++after) :=
        (ho.append_end (he.symm ▸ ht)).append_end (by
          rw [partitionEnd_append,he,hmid];exact hf)
      have hs : (common++mid)++tail=sampleClockSteps q 0 ((before++band)++after) := by
        dsimp [common,mid,tail]
        rw [sampleClockSteps_append,sampleClockSteps_append,partitionEnd_append,he,hmid]
      rw [hs]
      exact sampleClockSteps_ordered q _ ho'
    zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q 0 k))
      (physicalFiniteCapIndexedTrace n d e (List.replicate common.length 0++durations)
        (common++mid) tail hfull) 0 ≤
      (orderedPathS (n+1) b h v-orderedPathS (n+1) b h u+
        2*mesh*(2*ClockTree.errorJetVariation 2 0 0*
          clockVariationBound (physicalFeatureCoordinateBound n) q))/((n+1:ℝ)*g) := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let common := sampleClockSteps q 0 before
  let mid := sampleClockSteps q u band
  let tail := sampleClockSteps q v after
  have hright : MassOrdered 0 (before++band) := ho.append_end (he.symm ▸ ht)
  have hrend : partitionEnd 0 (before++band)=v := by rw [partitionEnd_append,he,hmid]
  have hleft : MassOrdered u (band++after) := ht.append_end (hmid.symm ▸ hf)
  have hlend : partitionEnd u (band++after)=1 := by rw [partitionEnd_append,hmid,hend]
  have hrightBounds : ∀a∈before++band,a.val ≤ v := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact (hau a ha).trans huv
    · exact hbv a ha
  have hleftMesh : PartitionMesh mesh 0 (before++(band++after)) := by
    simpa only [List.append_assoc] using hm
  have herrRight := (physicalRetainedCutSecondMoment_error n b h hb hh hv
    (before++band) after hright hf hrightBounds hrend hend hm).1
  have herrLeft := (physicalRetainedCutSecondMoment_error n b h hb hh hu
    before (band++after) ho hleft hau he hlend hleftMesh).2
  have hpre : common++mid=sampleClockSteps q 0 (before++band) := by
    dsimp [common,mid]
    rw [sampleClockSteps_append,he]
  have hpost : mid++tail=sampleClockSteps q u (band++after) := by
    dsimp [mid,tail]
    rw [sampleClockSteps_append,hmid]
  have ho' : MassOrdered 0 ((before++band)++after) :=
    hright.append_end (hrend.symm ▸ hf)
  have hsteps : (common++mid)++tail=sampleClockSteps q 0 ((before++band)++after) := by
    rw [hpre]
    dsimp [tail]
    rw [sampleClockSteps_append q 0 (before++band) after,hrend]
  have hfull : OrderedSteps 0 ((common++mid)++tail) := by
    rw [hsteps]
    exact sampleClockSteps_ordered q _ ho'
  have hfield : ∀st∈mid,∀j,st.2 (Sum.inl j)=st.2 (Sum.inl 0) :=
    sampledFieldClock_aligned (n+1) (by omega) b h band u
  have hcap := physicalFiniteCapIndexedTrace_band_rooted_le_path_increment
    n d e (q 0) durations common mid tail hfull hg hfield hslope
  have hinc : physicalPathSecondMoment (n+1) ((common++mid)++tail) (q 0) (common++mid).length-
      physicalPathSecondMoment (n+1) ((common++mid)++tail) (q 0) common.length ≤
      orderedPathS (n+1) b h v-orderedPathS (n+1) b h u+
        2*mesh*(2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n) q) := by
    rw [←hpre] at herrRight
    rw [←hpost,←List.append_assoc] at herrLeft
    change _ ≤ _ at herrRight herrLeft
    dsimp only [q,common,tail] at herrRight herrLeft ⊢
    linarith
  exact hcap.trans (div_le_div_of_nonneg_right hinc (mul_pos (by positivity : 0<(n+1:ℝ)) hg).le)

end OAI.SKFluctuations.LaplaceWindowFormalization

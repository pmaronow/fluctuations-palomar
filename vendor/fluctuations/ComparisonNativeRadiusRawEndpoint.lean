module

public import ComparisonNativeRadiusWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000

theorem orderedPathS_le_native_retained_raw_finite (n l : ℕ) (hl : 0<l)
    (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh xs : ℝ} (hmesh : PartitionMesh mesh 0 as) (hxs : 0<xs)
    (i : ℕ) (hi : i ≤ as.length) (hu : 0<partitionPoint 0 as i) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    orderedPathS (n+1) b h (partitionPoint 0 as i) ≤
      (physicalRawRatio (n+1) l steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q 0 k))
        id measurable_id)^2*(xs+partitionPoint 0 as i)+
      mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) q) := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let steps := sampleClockSteps q 0 as
  have herr := physicalSampledNodeSecondMoment_error n b h hb hh as ho he hmesh i hi hu
  have hraw := physicalProfile_second_le_raw_ratio (n+1) l hl steps
    (sampleClockSteps_ordered q _ ho) (q 0) hxs (i:=i) (by simp only [steps,sampleClockSteps_length];omega)
  rw [physicalCutMass_sampleClockSteps q 0 as i hi] at hraw
  have hlo := (abs_le.mp herr).1
  dsimp only [q,steps] at hraw hlo ⊢
  linarith

theorem orderedPathS_le_retained_native_raw (n l : ℕ) (hl : 0<l)
    (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    {u xs B : ℝ} (hu : 0<u) (hxs : 0<xs)
    (hretain : ∀j,∃i ≤ (as j).length,partitionPoint 0 (as j) i=u)
    (hraw : ∀ᶠ j in atTop,
      (physicalRawRatio (n+1) l (sampleClockSteps (completedPathClock (n+1) b h) 0 (as j))
        0 xs (Measure.pi fun k=>gaussianReal 0 (completedPathClock (n+1) b h 0 k))
        id measurable_id)^2 ≤ B) :
    orderedPathS (n+1) b h u ≤ B*(xs+u) := by
  let q := completedPathClock (n+1) b h
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) q
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  have herrlim : Tendsto (fun j=>mesh j*Cnode) atTop (𝓝 0) := by
    simpa using hlim.mul_const Cnode
  have hevent : ∀ᶠ (j:ℕ) in atTop,orderedPathS (n+1) b h u ≤ B*(xs+u)+epsilon := by
    filter_upwards [hraw,(tendsto_order.mp herrlim).2 epsilon hepsilon] with j hjraw hjerr
    obtain ⟨i,hi,hir⟩ := hretain j
    have hiu : 0<partitionPoint 0 (as j) i := by simpa only [hir] using hu
    have ht := orderedPathS_le_native_retained_raw_finite n l hl b h hb hh
      (as j) (ho j) (he j) (hmesh j) hxs i hi hiu
    rw [hir] at ht
    have hm := mul_le_mul_of_nonneg_right hjraw (by linarith : 0 ≤ xs+u)
    dsimp only [q,Cnode] at hjerr
    exact ht.trans (by linarith)
  exact hevent.exists.choose_spec

end OAI.SKFluctuations.LaplaceWindowFormalization

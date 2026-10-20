module

public import CavityActualBoundaryPrefixLaw
public import CavityBoundaryRowTransfer
public import CavityFiniteProfileClipping
public import SKFluctuationsOAI.Probability.SKFluctuations.FiniteRetainedGridReady

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem boundaryTripleMean_original_prefix {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre post : List PositiveMass)
    {a : ℝ} (ho : MassOrdered a (pre++post)) (q : ℕ→ι→ℝ≥0)
    (high : ℕ) (Q : S→S→S→ℝ) :
    boundaryTripleMean w φ (pre++post) q pre.length (pre.length+high) Q =
      prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps post (fun j=>q (pre.length+j))))
        (boundaryTripleMean w φ post (fun j=>q (pre.length+j)) 0 high Q) := by
  induction pre generalizing a q with
  | nil => funext x; simp only [List.nil_append,List.length_nil,Nat.zero_add,clockSteps,prefixTest]
  | cons b pre ih =>
    funext x
    simp only [List.cons_append,List.length_cons,boundaryTripleMean,clockSteps,prefixTest]
    have hi : (fun j=>q (pre.length+1+j))=(fun j=>q (pre.length+j+1)) := by
      funext j; congr 1; omega
    rw [hi]
    have hn : pre.length+1+high-1=pre.length+high := by omega
    rw [hn]
    congr 1
    · rw [prefixContinuation_hierarchy]
      congr 1
      exact clockSteps_append pre post (fun j=>q (j+1))
    · exact ih ho.2.2 (fun j=>q (j+1))

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations
open Hierarchy Cavity

theorem physical_resampling_eq_boundaryTripleDisorder_original_low (n l : ℕ)
    (pre post : List PositiveMass) (ho : MassOrdered 0 (pre++post))
    (q : ℕ→FeatureIndex n→ℝ) (high : ℕ) (hh : high ≤ post.length) :
    let inc := cumulativeIncrements (q 0) (fun j=>q (j+1))
    let preSteps := clockSteps pre inc
    let postSteps := clockSteps post (fun j=>inc (pre.length+j))
    let μ := Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))
    let μlow := actualPrefixFieldLaw (uniformWeight n) (finiteFeature n)
      preSteps postSteps μ id measurable_id
    physicalExteriorResamplingMoment n l postSteps μlow id measurable_id high =
      (ClockTree.boundaryTripleClock (S := Spin n) (pre++post)
        pre.length (pre.length+high)).disorderExpect (uniformWeight n) (finiteFeature n) 0 q
        (fun σ=>
          let z := ClockTree.boundaryTripleSpin (pre++post) pre.length (pre.length+high) σ
          |orderedOverlap n z.1 z.2.1-orderedOverlap n z.1 z.2.2|^(2*l)) 0 := by
  dsimp only
  let inc := cumulativeIncrements (q 0) (fun j=>q (j+1))
  let ps := clockSteps pre inc
  let ts := clockSteps post (fun j=>inc (pre.length+j))
  let μ := Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))
  let mid := ts.take high
  let tail := ts.drop high
  have hfull : mid++tail=ts := List.take_append_drop high ts
  have hlen : ts.length=post.length := length_clockSteps _ _
  have hmid : mid.length=high := by
    dsimp [mid]; exact List.length_take_of_le (by simpa only [hlen] using hh)
  have hs : OrderedSteps 0 (ps++(mid++tail)) := by
    rw [hfull]
    dsimp only [ps,ts]
    rw [←clockSteps_append]
    exact clockSteps_ordered ho inc
  have H := physical_boundary_resampling_original_prefix n l ps mid tail hs μ id measurable_id
  dsimp only at H
  conv at H => rhs; rw [hfull,hmid]
  rw [←H,ClockTree.disorderExpect_integral (uniformWeight_pos n) (finiteFeature n)
    (ClockTree.boundaryTripleClock (S := Spin n) (pre++post) pre.length (pre.length+high)) ho]
  simp only [zeroContinuation,Pi.zero_apply,sub_zero,zero_add]
  apply integral_congr_ae
  exact Eventually.of_forall fun y=>by
    dsimp only [id_eq]
    rw [actual_prepend_expect (uniformWeight_pos n) (finiteFeature n) ps
      (actualBoundaryResamplingTree (S := Spin n) mid tail) hs]
    rw [ClockTree.boundaryTripleClock_expect (uniformWeight_pos n) (finiteFeature n)
      (pre++post) ho inc pre.length (pre.length+high)
        (fun d c f=>|orderedOverlap n d c-orderedOverlap n d f|^(2*l)) y,
      ClockTree.boundaryTripleMean_original_prefix (uniformWeight_pos n) (finiteFeature n)
        pre post ho inc high]
    conv_lhs => arg 2; rw [hfull]
    apply congrArg (fun B=>prefixTest ps (gaussianHierarchy (uniformWeight n)
      (finiteFeature n) ts) B y)
    funext z
    rw [actual_boundary_resampling_tree_expect (uniformWeight_pos n) (finiteFeature n)
      mid tail (hs.suffix ps _) _,
      ClockTree.boundaryTripleMean_zero_eq_hierarchy (uniformWeight_pos n) (finiteFeature n)
        post ho.suffix_end (fun j=>inc (pre.length+j)) high
          (fun d c f=>|orderedOverlap n d c-orderedOverlap n d f|^(2*l)) z]
    simp only [hfull,hmid,ts]

theorem physical_resampling_eq_threeAtSlotDisorder_original_low (n l : ℕ)
    (pre post : List PositiveMass) (ho : MassOrdered 0 (pre++post))
    (T : ClockTree (Spin n) (pre++post)) (q : ℕ→FeatureIndex n→ℝ)
    (i j k : T.Slot) (hjk : j ≠ k)
    (hlow : T.splitIndex i j=T.splitIndex i k)
    (hgap : T.splitIndex i j<T.splitIndex j k)
    (hlo : T.splitIndex i j=pre.length)
    (high : ℕ) (hhi : T.splitIndex j k=pre.length+high) (hh : high ≤ post.length) :
    let inc := cumulativeIncrements (q 0) (fun z=>q (z+1))
    let μ := Measure.pi (fun z=>gaussianReal 0 (Real.toNNReal (q 0 z)))
    let μlow := actualPrefixFieldLaw (uniformWeight n) (finiteFeature n)
      (clockSteps pre inc) (clockSteps post (fun z=>inc (pre.length+z))) μ id measurable_id
    physicalExteriorResamplingMoment n l (clockSteps post (fun z=>inc (pre.length+z)))
      μlow id measurable_id high =
    T.disorderExpect (uniformWeight n) (finiteFeature n) 0 q
      (fun σ=>|orderedOverlap n (T.atSlot σ i) (T.atSlot σ j)-
        orderedOverlap n (T.atSlot σ i) (T.atSlot σ k)|^(2*l)) 0 := by
  dsimp only
  rw [T.disorderExpect_boundary_threeAtSlot (uniformWeight_pos n) (finiteFeature n)
    ho 0 q 0 i j k hjk hlow hgap
    (fun d c f=>|orderedOverlap n d c-orderedOverlap n d f|^(2*l)),hlo,hhi]
  exact physical_resampling_eq_boundaryTripleDisorder_original_low n l pre post ho q high hh

def originalBoundaryPrefixLaw (n : ℕ) (as : List PositiveMass)
    (q : ℕ→FeatureIndex n→ℝ) (low : ℕ) : Measure (FeatureIndex n→ℝ) :=
  let inc := cumulativeIncrements (q 0) (fun j=>q (j+1))
  actualPrefixFieldLaw (uniformWeight n) (finiteFeature n)
    (clockSteps (as.take low) inc)
    (clockSteps (as.drop low) (fun j=>inc (low+j)))
    (Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id

def originalBoundaryTailSteps (n : ℕ) (as : List PositiveMass)
    (q : ℕ→FeatureIndex n→ℝ) (low : ℕ) : List (GaussianStep (FeatureIndex n)) :=
  clockSteps (as.drop low) (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (low+j))

def originalBoundaryResamplingMoment (n l : ℕ) (as : List PositiveMass)
    (q : ℕ→FeatureIndex n→ℝ) (low high : ℕ) : ℝ :=
  physicalExteriorResamplingMoment n l (originalBoundaryTailSteps n as q low)
    (originalBoundaryPrefixLaw n as q low) id measurable_id (high-low)

theorem originalBoundaryPrefixLaw_probability (n : ℕ) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (q : ℕ→FeatureIndex n→ℝ)
    (low : ℕ) (hlow : low ≤ as.length) :
    IsProbabilityMeasure (originalBoundaryPrefixLaw n as q low) := by
  unfold originalBoundaryPrefixLaw
  apply actualPrefixFieldLaw_probability (a:=0) (uniformWeight_pos n) (finiteFeature n)
  rw [←clockSteps_take_drop as (cumulativeIncrements (q 0) (fun j=>q (j+1))) low hlow]
  exact clockSteps_ordered ho _

theorem original_boundary_resampling_eq_triple (n l : ℕ) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (q : ℕ→FeatureIndex n→ℝ) (low high : ℕ)
    (hlh : low ≤ high) (hh : high ≤ as.length) :
    originalBoundaryResamplingMoment n l as q low high =
      (ClockTree.boundaryTripleClock (S := Spin n) as low high).disorderExpect
        (uniformWeight n) (finiteFeature n) 0 q
        (fun σ=>let z:=ClockTree.boundaryTripleSpin as low high σ;
          |orderedOverlap n z.1 z.2.1-orderedOverlap n z.1 z.2.2|^(2*l)) 0 := by
  have hlo : low ≤ as.length := hlh.trans hh
  have ht : (as.take low).length=low := List.length_take_of_le hlo
  have hadd : low+(high-low)=high := by omega
  have hpost : high-low ≤ (as.drop low).length := by simp only [List.length_drop]; omega
  have H := physical_resampling_eq_boundaryTripleDisorder_original_low n l
    (as.take low) (as.drop low) (by simpa only [List.take_append_drop] using ho) q
    (high-low) hpost
  dsimp only at H
  rw [ht,List.take_append_drop,hadd] at H
  simpa only [originalBoundaryResamplingMoment,originalBoundaryPrefixLaw,
    originalBoundaryTailSteps,ht,List.take_append_drop,hadd] using H

theorem original_boundary_resampling_eq_full_tree (n l : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (q : ℕ→FeatureIndex n→ℝ) (i j k : T.Slot) (hjk : j ≠ k)
    (hlow : T.splitIndex i j=T.splitIndex i k)
    (hgap : T.splitIndex i j<T.splitIndex j k) :
    originalBoundaryResamplingMoment n l as q (T.splitIndex i j) (T.splitIndex j k) =
    T.disorderExpect (uniformWeight n) (finiteFeature n) 0 q
      (fun σ=>|orderedOverlap n (T.atSlot σ i) (T.atSlot σ j)-
        orderedOverlap n (T.atSlot σ i) (T.atSlot σ k)|^(2*l)) 0 := by
  rw [T.disorderExpect_boundary_threeAtSlot (uniformWeight_pos n) (finiteFeature n)
    ho 0 q 0 i j k hjk hlow hgap
    (fun d c f=>|orderedOverlap n d c-orderedOverlap n d f|^(2*l))]
  exact original_boundary_resampling_eq_triple n l as ho q _ _ hgap.le
    (T.splitIndex_le_clockLength j k)

end OAI.SKFluctuations

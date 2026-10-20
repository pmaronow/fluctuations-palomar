module

public import CavityThreeLeafPruning
public import CavityExteriorResamplingClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem boundaryTripleMean_zero_eq_hierarchy {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (high : ℕ) (Q : S → S → S → ℝ) (x : ι → ℝ) :
    boundaryTripleMean w φ as q 0 high Q x =
      gaussianHierarchyMean w φ (fun d => levelPairMean w φ (Q d) (clockSteps as q) high x)
        (clockSteps as q) x := by
  have hz : boundaryTripleMean w φ as q 0 high Q x =
      singleMean w φ as q (fun d => pairMean w φ as q high (Q d) x) x := by
    cases as <;> rfl
  rw [hz]
  have he : (fun d => pairMean w φ as q high (Q d) x) =
      fun d => levelPairMean w φ (Q d) (clockSteps as q) high x :=
    funext fun d => congrFun (pairMean_eq_levelPairMean hw φ as ho q high (Q d)) x
  rw [he]
  exact congrFun (singleMean_eq_hierarchy hw φ ho q
    (fun d => levelPairMean w φ (Q d) (clockSteps as q) high x)) x

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations
open Hierarchy Cavity

theorem physical_resampling_eq_boundaryTripleDisorder (n l : ℕ)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (q : ℕ → FeatureIndex n → ℝ) (high : ℕ) (hh : high≤as.length) :
    let steps := diagonalBoundarySteps as (q 0) (fun j=>q (j+1))
    physicalExteriorResamplingMoment n l steps
      (Measure.pi (fun i => gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id high =
      (ClockTree.boundaryTripleClock (S := Spin n) as 0 high).disorderExpect
        (uniformWeight n) (finiteFeature n) 0 q
        (fun σ => let z := (ClockTree.boundaryTripleSpin as 0 high σ);
          |orderedOverlap n z.1 z.2.1-orderedOverlap n z.1 z.2.2|^(2*l)) 0 := by
  dsimp only
  let steps := diagonalBoundarySteps as (q 0) (fun j=>q (j+1))
  have hsteps : steps=clockSteps as (cumulativeIncrements (q 0) (fun j=>q (j+1))) :=
    (clockSteps_cumulative as (q 0) (fun j=>q (j+1))).symm
  have hlen : steps.length=as.length := by
    rw [hsteps]
    have he (bs : List PositiveMass) (v : ℕ → FeatureIndex n → ℝ≥0) :
        (clockSteps bs v).length=bs.length := by
      induction bs generalizing v with
      | nil => rfl
      | cons b bs ih => simp only [clockSteps,List.length_cons,ih]
    exact he _ _
  let mid := steps.take high
  let tail := steps.drop high
  have hfull : mid++tail=steps := List.take_append_drop high steps
  have hmid : mid.length=high := by
    dsimp [mid]
    exact List.length_take_of_le (by simpa only [hlen] using hh)
  have hs : OrderedSteps 0 (mid++tail) := by
    rw [hfull,hsteps]
    exact clockSteps_ordered ho _
  have H := physical_exterior_resampling_eq_tree n l mid tail hs
    (Measure.pi (fun i => gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id
  conv at H =>
    lhs
    rw [hfull,hmid]
  rw [H,ClockTree.disorderExpect_integral (uniformWeight_pos n) (finiteFeature n)
    (ClockTree.boundaryTripleClock (S := Spin n) as 0 high) ho]
  simp only [zeroContinuation,Pi.zero_apply,sub_zero,zero_add]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [id_eq]
    rw [actual_boundary_resampling_tree_expect (uniformWeight_pos n) (finiteFeature n)
      mid tail hs (fun d c f => |orderedOverlap n d c-orderedOverlap n d f|^(2*l)) y,
      ClockTree.boundaryTripleClock_expect (uniformWeight_pos n) (finiteFeature n) as ho
        (cumulativeIncrements (q 0) (fun j=>q (j+1))) 0 high
        (fun d c f => |orderedOverlap n d c-orderedOverlap n d f|^(2*l)) y,
      ClockTree.boundaryTripleMean_zero_eq_hierarchy (uniformWeight_pos n) (finiteFeature n) as ho
        (cumulativeIncrements (q 0) (fun j=>q (j+1))) high
        (fun d c f => |orderedOverlap n d c-orderedOverlap n d f|^(2*l)) y]
    simp only [hfull,hmid,←hsteps]

end OAI.SKFluctuations

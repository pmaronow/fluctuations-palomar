module

public import CavityCenteringMoments
public import CavityPhysicalMixedClock
public import CavityPhysicalForkLawBridge

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy Cavity

theorem physicalOverlapMoment_eq_actual_pair (n l : ℕ) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (q : ℕ → FeatureIndex n → ℝ)
    (j : ℕ) (hj : j≤as.length) :
    physicalOverlapMoment n l (diagonalBoundarySteps as (q 0) (fun k=>q (k+1)))
      (Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id j =
    (ClockTree.pairClock as j).disorderExpect (uniformWeight n) (finiteFeature n) 0 q
      (fun σ=>|orderedOverlap n (ClockTree.pairSpin as j σ).1
        (ClockTree.pairSpin as j σ).2|^(2*l)) 0 := by
  exact actual_terminalFork_eq_pairDisorder (uniformWeight_pos n) (finiteFeature n)
    as ho q j hj (fun σ τ=>|orderedOverlap n σ τ|^(2*l))

theorem physicalStarPairMoment_zero_eq_raw (n l : ℕ) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (q : ℕ → FeatureIndex n → ℝ)
    (j : ℕ) (hj : j≤as.length) :
    physicalStarPairMoment n l (diagonalBoundarySteps as (q 0) (fun k=>q (k+1)))
      (Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id j 0=
    physicalOverlapMoment n l (diagonalBoundarySteps as (q 0) (fun k=>q (k+1)))
      (Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id j := by
  rw [physicalStarPairMoment_eq_pairDisorder n l as ho q j hj,
    physicalOverlapMoment_eq_actual_pair n l as ho q j hj]
  simp only [sub_zero]

theorem physicalStarPairMoment_trueMean_le_raw (n l : ℕ) (hl : 0<l)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (b h : ℕ → ℝ)
    (j : ℕ) (hj : j≤as.length) :
    let q := physicalCompletedClock n b h
    let steps := diagonalBoundarySteps as (q 0) (fun k=>q (k+1))
    let μ := Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))
    physicalStarPairMoment n l steps μ id measurable_id j (finitePhysicalMean n as b h j)≤
      (2:ℝ)^(2*l)*physicalOverlapMoment n l steps μ id measurable_id j := by
  dsimp only
  rw [physicalStarPairMoment_eq_pairDisorder n l as ho _ j hj,
    physicalOverlapMoment_eq_actual_pair n l as ho _ j hj,
    finitePhysicalMean_eq_actual_pair n ho b h j hj]
  exact (ClockTree.pairClock as j).disorderExpect_centered_abs_pow_le
    (uniformWeight_pos n) (finiteFeature n) ho 0 (physicalCompletedClock n b h) 0
    (fun σ=>orderedOverlap n (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)
    (by omega)

end OAI.SKFluctuations

module

public import CavitySavedStarPair
public import CavityAttachedTree
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalTerminalPairLaw
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockMassIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

theorem actual_terminalFork_eq_pairDisorder {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (q : ℕ → ι → ℝ)
    (j : ℕ) (hj : j ≤ as.length) (Q : S → S → ℝ) :
    let steps := diagonalBoundarySteps as (q 0) (fun k => q (k+1))
    let μ := Measure.pi (fun i => gaussianReal 0 (Real.toNNReal (q 0 i)))
    (∫ p, conditionalForkTest w φ steps id j (terminalPairTest steps Q) p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap id measurable_id) =
      (ClockTree.pairClock as j).disorderExpect w φ 0 q
        (fun σ => Q (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) 0 := by
  dsimp only
  let steps := diagonalBoundarySteps as (q 0) (fun k => q (k+1))
  have hs : OrderedSteps 0 steps := by
    dsimp [steps]
    rw [← clockSteps_cumulative]
    exact clockSteps_ordered ho _
  have hj' : j ≤ steps.length := by
    have hlen (bs : List PositiveMass) (l : ι → ℝ) (c : ℕ → ι → ℝ) :
        (diagonalBoundarySteps bs l c).length = bs.length := by
      induction bs generalizing l c with
      | nil => rfl
      | cons b bs ih => simp only [diagonalBoundarySteps, List.length_cons, ih]
    simpa only [steps, hlen] using hj
  have he := integral_terminalFork_eq_levelPairMean hw φ steps hs
    (Measure.pi (fun i => gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id j hj' Q
  change _ = (ClockTree.pairClock as j).disorderExpect w φ (fun _ => 0) q
    (fun σ => Q (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) 0
  rw [ClockTree.pairDisorder_eq_rootLevelPairMean hw φ as ho q j Q]
  simpa only [rootLevelPairMean, zeroContinuation, zero_add, id_eq, steps] using he

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Cavity
open scoped Topology NNReal BigOperators

theorem physicalStarPairMoment_eq_pairDisorder (n l : ℕ) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (q : ℕ → FeatureIndex n → ℝ)
    (j : ℕ) (hj : j ≤ as.length) (S : ℝ) :
    physicalStarPairMoment n l
      (diagonalBoundarySteps as (q 0) (fun k => q (k+1)))
      (Measure.pi (fun i => gaussianReal 0 (Real.toNNReal (q 0 i)))) id measurable_id j S =
      (ClockTree.pairClock as j).disorderExpect (uniformWeight n) (finiteFeature n) 0 q
        (fun σ => |orderedOverlap n (ClockTree.pairSpin as j σ).1
          (ClockTree.pairSpin as j σ).2-S|^(2*l)) 0 := by
  exact actual_terminalFork_eq_pairDisorder (uniformWeight_pos n) (finiteFeature n)
    as ho q j hj (fun σ τ => |orderedOverlap n σ τ-S|^(2*l))

end OAI.SKFluctuations

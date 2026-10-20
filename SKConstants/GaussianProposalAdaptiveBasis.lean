module

public import SKConstants.GaussianProposalRevelation
public import SKConstants.GaussianProposalAdaptiveKernel
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.GaussianProposal

variable {ι Past : Type*} [Fintype ι] [LinearOrder ι] [MeasurableSpace Past]

@[expose] def gaussianUpperLaw (sigma : ℝ) (ι : Type*) [Fintype ι] [LinearOrder ι] :
    Measure (UpperPair ι → ℝ) :=
  Measure.pi (fun p : UpperPair ι => gaussianReal 0
    (if p.1.1 = p.1.2 then (((4 : ℕ) : ℝ) * sigma ^ 2).toNNReal else (((2 : ℕ) : ℝ) * sigma ^ 2).toNNReal))

instance (sigma : ℝ) : IsProbabilityMeasure (gaussianUpperLaw sigma ι) := by
  unfold gaussianUpperLaw
  infer_instance

@[expose] def adaptiveBasisCoordinates (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (past : Past) (z : EuclideanSpace ℝ (ι × ι)) : UpperPair ι → ℝ :=
  fun p => basisEntry sigma (basis past) p z

theorem adaptiveBasis_entry_measurable (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j)) (p : UpperPair ι) :
    Measurable (fun x : Past × EuclideanSpace ℝ (ι × ι) =>
      basisEntry sigma (basis x.1) p x.2) := by
  unfold basisEntry goeBilinear linearForm
  apply Finset.measurable_sum
  intro q hq
  have hz : Measurable (fun x : Past × EuclideanSpace ℝ (ι × ι) => x.2 q) :=
    (EuclideanSpace.proj q).continuous.measurable.comp measurable_snd
  exact (measurable_const.mul
    (((hbasis p.1.1 q.1).comp measurable_fst).mul
      ((hbasis p.1.2 q.2).comp measurable_fst) |>.add
      (((hbasis p.1.1 q.2).comp measurable_fst).mul
        ((hbasis p.1.2 q.1).comp measurable_fst)))).mul hz

theorem adaptiveBasis_coordinates_measurable (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j)) :
    Measurable (Function.uncurry (adaptiveBasisCoordinates sigma basis)) := by
  apply Measurable.of_eval
  intro p
  exact adaptiveBasis_entry_measurable sigma basis hbasis p

omit [MeasurableSpace Past] in
theorem adaptiveBasis_fiber_law (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (horth : ∀ a i j, dot (basis a i) (basis a j) = if i = j then 1 else 0)
    (a : Past) :
    (primitiveGaussian (ι × ι)).map (adaptiveBasisCoordinates sigma basis a) =
      gaussianUpperLaw sigma ι := by
  exact basisEntries_joint_law sigma (basis a) (horth a)

theorem adaptiveBasis_joint_law (μ : Measure Past) [SFinite μ]
    (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j))
    (horth : ∀ a i j, dot (basis a i) (basis a j) = if i = j then 1 else 0) :
    (μ.prod (primitiveGaussian (ι × ι))).map
      (fun x : Past × EuclideanSpace ℝ (ι × ι) =>
        (x.1, adaptiveBasisCoordinates sigma basis x.1 x.2)) =
      μ.prod (gaussianUpperLaw sigma ι) := by
  exact adaptiveStep_joint_law (adaptiveBasis_coordinates_measurable sigma basis hbasis)
    (adaptiveBasis_fiber_law sigma basis horth)

theorem adaptiveBasis_output_law (μ : Measure Past) [IsProbabilityMeasure μ]
    (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j))
    (horth : ∀ a i j, dot (basis a i) (basis a j) = if i = j then 1 else 0) :
    (μ.prod (primitiveGaussian (ι × ι))).map
      (Function.uncurry (adaptiveBasisCoordinates sigma basis)) =
      gaussianUpperLaw sigma ι := by
  exact adaptiveStep_output_law_ae (adaptiveBasis_coordinates_measurable sigma basis hbasis)
    (Filter.Eventually.of_forall (adaptiveBasis_fiber_law sigma basis horth))

theorem adaptiveBasis_independent (μ : Measure Past) [IsProbabilityMeasure μ]
    (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j))
    (horth : ∀ a i j, dot (basis a i) (basis a j) = if i = j then 1 else 0) :
    IndepFun Prod.fst (Function.uncurry (adaptiveBasisCoordinates sigma basis))
      (μ.prod (primitiveGaussian (ι × ι))) := by
  exact adaptiveStep_independent_ae (adaptiveBasis_coordinates_measurable sigma basis hbasis)
    (Filter.Eventually.of_forall (adaptiveBasis_fiber_law sigma basis horth))

end SKConstants.GaussianProposal

module

public import SKConstants.Completion.LFine.QueryGeometry
public import SKConstants.Completion.LFine.FreshRowSeeds
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.LFine
open GaussianProposal FineInformation SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def fixedPastPosterior (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a : ℝ≥0) (Bpast Dpast : ScalarContinuousPath a) : ℝ :=
  actualParisiFullMagnetization β a
    (scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) a (0,(Bpast,Dpast))
        ⟨a,a.coe_nonneg,le_rfl⟩)

def FreshPosteriorMeanStatement (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (n : ℕ) (Bpast Dpast : Fin n → ScalarContinuousPath a) : Prop :=
  ∀ i, meanSpin (freshRowsLaw W h f n)
    (gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))) i =
      fixedPastPosterior W β hβ a (Bpast i) (Dpast i)

theorem freshRows_oneQuery_of_posterior (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (n m : ℕ) (Bpast Dpast : Fin n → ScalarContinuousPath a)
    (N : ℝ) (hN : 0 < N) (s : ℝ) (hs : s ≠ 0)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (m₀ : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0)
    (hm₀ : E *ᵥ m₀ = 0)
    (hposterior : FreshPosteriorMeanStatement W β hβ a h f n Bpast Dpast) :
    let mean := fun i => fixedPastPosterior W β hβ a (Bpast i) (Dpast i)
    let t := fun i => (mean i - m₀ i) / s
    let u := normalizedQuery N (paperFrame E t 0)
    let P := remainingProjection (paperFrame E t)
    let row := gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))
    (∫ z, oneQueryEnergy row N u P z ∂freshRowsLaw W h f n) =
      s * queryResidualNorm N E t *
        (N⁻¹ * ∑ j, P j j * mixedMean (freshRowsLaw W h f n) row j) -
      2 * (N⁻¹)^2 * ∑ i, u i * P i i * mean i *
        mixedMean (freshRowsLaw W h f n) row i := by
  dsimp only
  let mean := fun i => fixedPastPosterior W β hβ a (Bpast i) (Dpast i)
  let t := fun i => (mean i - m₀ i) / s
  unfold FreshPosteriorMeanStatement at hposterior
  have hmean : m₀ + s • t = mean := by
    ext i
    dsimp [t]
    field_simp
    ring
  have hkill (i : Fin n) :
      (∑ j, remainingProjection (paperFrame E t) j i *
        meanSpin (freshRowsLaw W h f n)
          (gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))) j) = 0 := by
    simp_rw [hposterior]
    simpa only [hmean] using paperFrame_mean_killed_sum E t m₀ s hE hm₀ i
  rw [freshRows_oneQuery_expectation W β hβ a h f n Bpast Dpast N
    (normalizedQuery N (paperFrame E t 0)) (remainingProjection (paperFrame E t)) hkill]
  simp_rw [hposterior]
  have hdot := paperFrame_query_dot_mean N hN E t m₀ s hE hm₀
  rw [hmean] at hdot
  change N⁻¹ * (∑ i, normalizedQuery N (paperFrame E t 0) i * mean i) = _ at hdot
  rw [hdot]

end SKConstants.Completion.LFine

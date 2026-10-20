module

public import SKConstants.Completion.LJ3.GrowingOriginalLag
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LJ3
open SKConstantsOAI.ZeroTemperatureSK LJ
variable {Ω : Type*} [MeasurableSpace Ω]

def growingLagDyadicTime (δ : ℝ≥0) (l j k : ℕ) : ℝ≥0 :=
  growingQueryTime δ j + scalarBrownianDyadicTime (growingQueryDuration δ j) l k

theorem growingLagDyadicTime_monotone (δ : ℝ≥0) (l j : ℕ) :
    Monotone (growingLagDyadicTime δ l j) :=
  monotone_const.add (scalarBrownianDyadicTime_mono _ _)

theorem growingLagDyadicTime_zero (δ : ℝ≥0) (l j : ℕ) :
    growingLagDyadicTime δ l j 0 = growingQueryTime δ j := by
  simp only [growingLagDyadicTime, scalarBrownianDyadicTime_zero, add_zero]

theorem growingLagDyadicTime_end (δ : ℝ≥0) (l j : ℕ) :
    growingLagDyadicTime δ l j (2 ^ l) = growingQueryTime δ (j + 1) := by
  simp only [growingLagDyadicTime, scalarBrownianDyadicTime_end, growingQueryTime_succ]

theorem actualGrowingOriginalLag_dyadic_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1)
    (K l : ℕ) (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) :
    Concentration.LocalQuadraticMGF
      (actualGrowingOriginalLag W β (growingLagDyadicTime δ l) weight (fun _ => 2 ^ l) K) W.law
      (256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ))
      (1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ))) := by
  exact actualGrowingOriginalLag_mgf W β hβ δ hδ _ (growingLagDyadicTime_monotone δ l)
    (growingLagDyadicTime_zero δ l) _ (fun j => (growingLagDyadicTime_end δ l j).le)
    weight hweight K hsmall

theorem actualGrowingOriginalLag_dyadic_centered_log_mgf (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1)
    (K l : ℕ) (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) (θ : ℝ)
    (hθ : |θ| ≤ 1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ))) :
    Real.log (∫ w, Real.exp (θ *
      (actualGrowingOriginalLag W β (growingLagDyadicTime δ l) weight (fun _ => 2 ^ l) K w -
        ∫ z, actualGrowingOriginalLag W β (growingLagDyadicTime δ l) weight (fun _ => 2 ^ l) K z
          ∂W.law)) ∂W.law) ≤
      256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ) * θ ^ 2 := by
  exact actualGrowingOriginalLag_centered_log_mgf W β hβ δ hδ _ (growingLagDyadicTime_monotone δ l)
    (growingLagDyadicTime_zero δ l) _ (fun j => (growingLagDyadicTime_end δ l j).le)
    weight hweight K hsmall θ hθ

end SKConstants.Completion.LJ3

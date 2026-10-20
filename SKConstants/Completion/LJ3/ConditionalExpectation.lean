module

public import SKConstants.Completion.LJ3.ConditionalMGF
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LJ3
open SKConstantsOAI.ZeroTemperatureSK LJ
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem condExp_le_of_event_conditioning {S : Type*} [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Ω → S) (hP : Measurable P)
    (f : Ω → ℝ) (hf : Integrable f μ) (B : ℝ)
    (hbound : ∀ E : Set S, MeasurableSet E → μ (P ⁻¹' E) ≠ 0 →
      (∫ w, f w ∂μ[|P ⁻¹' E]) ≤ B) :
    μ[f | MeasurableSpace.comap P inferInstance] ≤ᵐ[μ] (fun _ => B) := by
  let m := MeasurableSpace.comap P inferInstance
  have hm : m ≤ mΩ := hP.comap_le
  have htest (A : Set Ω) (hA : MeasurableSet[m] A) :
      (∫ w in A, f w ∂μ) ≤ μ.real A * B := by
    obtain ⟨E, hE, rfl⟩ := hA
    by_cases h0 : μ (P ⁻¹' E) = 0
    · simp [Measure.restrict_eq_zero.mpr h0, measureReal_def, h0]
    · have hc := hbound E hE h0
      rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv] at hc
      have hp : 0 < μ.real (P ⁻¹' E) := ENNReal.toReal_pos h0 (measure_ne_top _ _)
      calc
        _ = μ.real (P ⁻¹' E) * ((μ.real (P ⁻¹' E))⁻¹ * ∫ w in P ⁻¹' E, f w ∂μ) := by
          rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hc hp.le
  apply ae_of_ae_trim (μ := μ) hm
  apply @ae_le_of_forall_setIntegral_le Ω m (μ.trim hm) _ _
    (integrable_condExp.trim hm stronglyMeasurable_condExp) (integrable_const B)
  intro A hA _
  rw [← setIntegral_trim (μ := μ) hm stronglyMeasurable_condExp hA,
    ← setIntegral_trim (μ := μ) hm stronglyMeasurable_const hA, setIntegral_condExp hm hf hA]
  simpa only [setIntegral_const, smul_eq_mul] using htest A hA

theorem originalLagSum_condExp_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ)
    (hQ : 0 < Q) (hh : 0 < h) (hq : ∀ k, |q k| ≤ Q)
    (hduration : (t n : ℝ) - t 0 ≤ h) (θ : ℝ) (hθ : |θ| ≤ 1 / (4 * h * Q)) :
    W.law[fun w => Real.exp (θ * originalLagSum W β t q n w) |
      MeasurableSpace.comap (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0))
        inferInstance] ≤ᵐ[W.law] (fun _ => Real.exp (32 * h ^ 2 * Q ^ 2 * θ ^ 2)) := by
  let := W.isProbability
  apply condExp_le_of_event_conditioning W.law _
    (measurable_boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) _
    ((originalLagSum_local_mgf W β hβ t ht q n Q h hQ hh hq hduration).integrable_exp_mul θ hθ)
  intro E hE hE0
  exact (originalLagSum_conditional_local_mgf W β hβ t ht E hE hE0 q n Q h hQ hh hq
    hduration).mgf_le θ hθ

end SKConstants.Completion.LJ3

module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKSupport/Foundations/IntegrableCompBoundedDeriv.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKSupport.Model

@[expose] public section

namespace SKConstantsOAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma integrable_comp_of_bounded_deriv [IsFiniteMeasure P] {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (C : ℝ≥0) (hC : ∀ x, |deriv f x| ≤ C) {Y : Ω → ℝ} (hY : Integrable Y P) :
    Integrable (fun ω => f (Y ω)) P := by
  have hl : LipschitzWith C f := lipschitzWith_of_nnnorm_deriv_le hf
    (fun x => show ‖deriv f x‖₊ ≤ C from by exact_mod_cast hC x)
  apply ((integrable_const ‖f 0‖).add (hY.norm.const_mul (C:ℝ))).mono'
    (hf.continuous.comp_aestronglyMeasurable hY.aestronglyMeasurable)
  filter_upwards [] with ω
  have h := hl.norm_sub_le (Y ω) 0
  simp only [sub_zero] at h
  have htri := norm_add_le (f (Y ω)-f 0) (f 0)
  rw [sub_add_cancel] at htri
  dsimp
  simp only [Real.norm_eq_abs] at h htri
  linarith

end ZeroTemperatureSK.WeakIto

end
end
end

end SKConstantsOAI

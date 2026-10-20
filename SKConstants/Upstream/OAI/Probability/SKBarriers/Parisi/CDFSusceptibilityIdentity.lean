module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Parisi/CDFSusceptibilityIdentity.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFSupportContact
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFSusceptibilityIntegral

@[expose] public section

namespace SKConstantsOAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem exists_scalarCDFParisi_minimizer_area {β : ℝ} (hβ : β ≠ 0) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0=
        ∫ s in Icc (0:ℝ) 1, cdf (μ : Measure ℝ) s := by
  obtain ⟨μ,hμ,hm,hs⟩ := exists_scalarCDFParisi_minimizer_susceptibility β
  refine ⟨μ,hμ,hm,?_⟩
  rw [hs,integral_congr_ae (scalarCDFParisi_overlap_eq_ae hβ μ hμ hm),
    supported_cdf_area μ hμ]

end SK.Analytic

end
end

end SKConstantsOAI

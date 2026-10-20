module

public import SKConstants.Completion.LGram.SourceMeasurable
public import SKConstants.Completion.LGram.Budget

@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal
namespace SKConstants.Completion.LGram
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false

theorem actualSource_wholeGram_power_compl_le {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r K : ℕ) (hN : 0 < r+K) (γ : ℝ) (hγ : 0 ≤ γ)
    (hrow : SourceMixedRowsLawStatement W β hβ δ r K) :
    (M1.SourceLinkedLaw W β hβ δ r K).real
      (sourceWholeGramEvent W β hβ δ r K (((r+K:ℕ):ℝ)^(-γ)))ᶜ ≤
      2 * Real.exp (((K+(K+1):ℕ):ℝ)*Real.log 9 -
        ((r+K:ℕ):ℝ)^(1-2*γ) / (768 * Concentration.squareVarianceScale
          (actualParisiFullMixedRowMGFProxy W β (growingQueryTime δ K):ℝ) 3)) := by
  have h := actualSource_wholeGram_compl_le W β hβ δ hδ r K hN (((r+K:ℕ):ℝ)^(-γ))
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) (-γ)) hrow
  rwa [gramTailBudget_power (r+K) (K+(K+1)) hN _ γ hγ] at h

end SKConstants.Completion.LGram

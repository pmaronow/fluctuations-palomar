module

public import QuantitativePaper.MainFluctuationReduction
public import QuantitativePaper.AbsoluteComparisonProposition

@[expose] public section

/-! The genuine small-window model comparison discharges the sole
external hypothesis of the main fluctuation and tail reductions. -/
noncomputable section
namespace QuantitativePaper

theorem uniform_absolute_comparison : UniformAbsoluteComparisonHypothesis := by
  intro β0 hβ0
  obtain ⟨L,C,hL,hL1,hLβ,hC,hcomparison⟩:=absolute_selfconsistent_comparison β0 hβ0
  refine ⟨C,L,hC,⟨hL,hL1⟩,?_⟩
  intro n hn β hb lam hlam
  convert (hcomparison n hn β hb lam hlam).2 using 1 <;> norm_num

end QuantitativePaper

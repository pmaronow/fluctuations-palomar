module

public import QuantitativePaper.MainFluctuationComparison

@[expose] public section

/-! Literal main Theorem 1.4 in the original free-energy normalization. -/
namespace QuantitativePaper

theorem fixed_temperature_fluctuations : MainFixedTemperatureFluctuationsTarget :=
  main_fixed_temperature_fluctuations_of_comparison uniform_absolute_comparison

end QuantitativePaper

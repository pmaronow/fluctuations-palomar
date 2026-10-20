module

public import SKBarriers2.Corner.MassVariationScalar
public import SKBarriers2.Corner.EntropyInputs

@[expose] public section

open Set MeasureTheory ProbabilityTheory

namespace SKBarriers2.Corner

theorem massVariationBound_of_scalarData_C2_and_path {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hC2 : MassSensitivityC2 β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hpath : UniformMassPathRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u) :=
  massVariationBound_of_scalarData_C2_and_entropyInputs D hl hu hC2
    (scalarData_uniformWindowEntropyInputs D hl hu) hpath

end SKBarriers2.Corner

module

public import SKBarriers2.Corner.PathEnergyInner9
public import SKBarriers2.Corner.PathEnergyGenerator
public import SKBarriers2.Corner.PathEnergyBias3
public import SKBarriers2.Corner.PathEnergySource3

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory

namespace SKBarriers2.Corner

theorem scalarData_pathEnergyC2 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    PathEnergyC2 β (cdf (D.μ : Measure ℝ)) (Icc l u) :=
  scalarData_pathEnergyC2_of_parts D hl hu
    (scalarData_windowInnerEnergyC2 D hl hu)
    (scalarData_windowGeneratorComparisonC2 D hl hu)
    (scalarData_windowInnerBiasC2 D hl hu)
    (scalarData_windowPrefixEnergyRecursions D hl hu)

end SKBarriers2.Corner

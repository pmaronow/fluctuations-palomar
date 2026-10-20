module

public import SKConstants.Completion.SJ7.Mean
public import SKConstants.Completion.SJ7.CoefficientMeans
public import SKConstants.Completion.SJ7.QueryCoefficient
public import SKConstants.Completion.SJ7.OriginalLagLimit
public import SKConstants.Completion.SJ7.Holder

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped NNReal

namespace SKConstants.Completion.SJ7
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint4

theorem growingResidual_integrable_mean {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K : ℕ) (hmesh : LagMesh β δ K)
    (Zv : (Bool × Ω) × A → ℝ)
    (hZv : IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv) :
    Integrable (growingResidual W Z β hβ δ K Zv)
      (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) ∧
    (∫ u, growingResidual W Z β hβ δ K Zv u
      ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) =
      3 / 2 * (actualParisiEnergyReference W β (growingQueryTime δ (K + 1)) -
        LJ.gridEnergy W β (growingQueryTime δ) K) :=
  ⟨growingResidual_integrable W Z β hβ δ K Zv hZv,
    growingResidual_mean W Z β hβ δ hmesh.1 K Zv hZv⟩

end SKConstants.Completion.SJ7

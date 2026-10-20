module

public import SKConstants.Completion.SJ3.Mean
public import SKConstants.Completion.SJ3.JointIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.SJ3
open SKConstantsOAI.ZeroTemperatureSK Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem growingResidual_integrable (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ) {Zv : (Bool × Ω) × A → ℝ}
    (hZv : IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv) :
    Integrable (growingResidual W Z β hβ δ K Zv)
      (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) := by
  have hiZ : Integrable Zv (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) :=
    (memLp_rowLinked W Z β _ hZv.2.1).integrable (by norm_num)
  exact hiZ.sub ((LJ.integrable_actualFiniteRow W Z β hβ (growingQueryTime δ) K _).add
    (integrable_const _))

theorem growingResidual_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) {Zv : (Bool × Ω) × A → ℝ}
    (hZv : IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv) :
    (∫ u, growingResidual W Z β hβ δ K Zv u
      ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) =
      3 / 2 * (actualParisiEnergyReference W β (growingQueryTime δ (K + 1)) -
        LJ.gridEnergy W β (growingQueryTime δ) K) := by
  have hiZ : Integrable Zv (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) :=
    (memLp_rowLinked W Z β _ hZv.2.1).integrable (by norm_num)
  have hiF := LJ.integrable_actualFiniteRow W Z β hβ (growingQueryTime δ) K
    (growingQueryTime δ (K + 1))
  have hiFC : Integrable (fun u => LJ.actualFiniteRow W Z β hβ (growingQueryTime δ) K u +
      LJ.gridEnergy W β (growingQueryTime δ) K / 2)
      (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) :=
    (hiF.add (integrable_const _)).congr (ae_of_all _ (fun _ => rfl))
  unfold growingResidual
  rw [integral_sub hiZ hiFC,
    integral_add hiF (integrable_const _), integral_const, probReal_univ, one_smul,
    jointRowIntegral_mean W Z β hβ _ Zv hZv,
    LJ.actualFiniteRow_mean W Z β hβ _ (growingQueryTime_strictMono δ hδ) K _ le_rfl]
  ring

def GrowingResidualMeanStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ), 0 < δ →
      ∀ Zv, IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv →
        Integrable (growingResidual W Z β hβ δ K Zv)
          (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) ∧
        (∫ u, growingResidual W Z β hβ δ K Zv u
          ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) =
          3 / 2 * (actualParisiEnergyReference W β (growingQueryTime δ (K + 1)) -
            LJ.gridEnergy W β (growingQueryTime δ) K)

theorem GrowingResidualMeanStatement_holds : GrowingResidualMeanStatement := by
  intro Ω A _ _ W Z β hβ δ K hδ Zv hZv
  exact ⟨growingResidual_integrable W Z β hβ δ K hZv, growingResidual_mean W Z β hβ δ hδ K hZv⟩

end SKConstants.Completion.SJ3

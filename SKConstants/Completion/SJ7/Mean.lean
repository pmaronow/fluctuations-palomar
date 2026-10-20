module

public import SKConstants.Completion.SJ7.MeanLeftSums

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.SJ7
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem jointRowIntegral_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (Zv : (Bool × Ω) × A → ℝ)
    (hZv : IsJointRowIntegral W Z β hβ V Zv) :
    (∫ u, Zv u ∂actualParisiFullQuerySpinLaw W Z β V) =
      3 / 2 * actualParisiEnergyReference W β V := by
  have hL2 := jointRowIntegral_tendsto_L2_linked W Z β hβ V Zv hZv
  exact tendsto_nhds_unique
    (integral_tendsto_of_L2 (actualParisiFullQuerySpinLaw W Z β V)
      (jointRowLeftSum W Z β hβ V) Zv (measurable_jointRowLeftSum W Z β hβ V)
      hZv.1 (jointRowIntegral_memLp_linked W Z β hβ V Zv hZv) hL2.1 hL2.2)
    (jointRowLeftSum_mean_tendsto W Z β hβ V)

theorem growingResidual_integrable (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ) (Zv : (Bool × Ω) × A → ℝ)
    (hZv : IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv) :
    Integrable (growingResidual W Z β hβ δ K Zv)
      (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) :=
  (jointRowIntegral_integrable W Z β hβ _ Zv hZv).sub
    ((LJ.integrable_actualFiniteRow W Z β hβ _ K _).add (integrable_const _))

theorem growingResidual_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ)
    (Zv : (Bool × Ω) × A → ℝ)
    (hZv : IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv) :
    (∫ u, growingResidual W Z β hβ δ K Zv u
      ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) =
      3 / 2 * (actualParisiEnergyReference W β (growingQueryTime δ (K + 1)) -
        LJ.gridEnergy W β (growingQueryTime δ) K) := by
  have hZi := jointRowIntegral_integrable W Z β hβ _ Zv hZv
  have hFi := LJ.integrable_actualFiniteRow W Z β hβ (growingQueryTime δ) K (growingQueryTime δ (K + 1))
  unfold growingResidual
  rw [integral_sub (g := fun u => LJ.actualFiniteRow W Z β hβ (growingQueryTime δ) K u +
      LJ.gridEnergy W β (growingQueryTime δ) K / 2) hZi (hFi.add (integrable_const _)),
    integral_add (g := fun _ => LJ.gridEnergy W β (growingQueryTime δ) K / 2) hFi (integrable_const _), integral_const,
    jointRowIntegral_mean W Z β hβ _ Zv hZv,
    LJ.actualFiniteRow_mean W Z β hβ _ (growingQueryTime_strictMono δ hδ) K _ le_rfl]
  simp only [probReal_univ, one_smul]
  ring

theorem growingResidual_abs_mean_le (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ)
    (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1)
    (Zv : (Bool × Ω) × A → ℝ)
    (hZv : IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv) :
    |∫ u, growingResidual W Z β hβ δ K Zv u
      ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))| ≤
      (3 / 2 * (1 / β ^ 2 + 33 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2))) * δ := by
  rw [growingResidual_mean W Z β hβ δ hδ K Zv hZv, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), abs_sub_comm, LJ.gridEnergy_growing_eq]
  have h := LQ.actual_growing_energy_error W β hβ δ hδ K hsmall
  nlinarith

end SKConstants.Completion.SJ7

module

public import SKConstants.Completion.N7.HistoryMean
public import SKConstants.Completion.N13e.Psi
public import SKConstants.Completion.LQ.ActualGrowingQuadrature
public import SKConstants.ParisiScalarEnergyEntropyIdentity
public import SKConstants.Completion.Blueprint.Experiment

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators Topology

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK LC4a LM4 LM4b
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualRowInformation_terms_integrable
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (J : (Bool × Ω) × A → ℝ)
    (hJ : IsActualRowDIntegral W Z β hβ V J) :
    Integrable (fun u => Real.log (actualRowLink β W V u))
        (actualParisiFullQuerySpinLaw W Z β V) ∧
      Integrable J (actualParisiFullQuerySpinLaw W Z β V) ∧
      Integrable (actualRowDBracket W β V) (actualParisiFullQuerySpinLaw W Z β V) := by
  have hbound : ∀ᵐ u ∂actualRowBaseLaw W Z, actualRowLink β W V u ≤ 2 :=
    ae_of_all _ (fun u => (actualRowLink_bounds β W V u).2)
  refine ⟨?_, ?_, ?_⟩
  · rw [← actual_linkedRowLaw_eq]
    exact integrable_log_withDensity_of_bounded _ _ (measurable_actualRowLink β W V)
      (fun u => (actualRowLink_bounds β W V u).1.le) 2
      (fun u => (actualRowLink_bounds β W V u).2)
  · rw [← actual_linkedRowLaw_eq]
    exact linkedRowLaw_integrable hbound (hJ.1.integrable (by norm_num))
  · exact Integrable.of_bound (measurable_actualRowDBracket W β V).aestronglyMeasurable
      (4 * (V : ℝ)) (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (actualRowDBracket_bounds W β hβ V u).1]
        exact (actualRowDBracket_bounds W β hβ V u).2))

theorem actualRowInformation_mean
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (J : (Bool × Ω) × A → ℝ)
    (hJ : IsActualRowDIntegral W Z β hβ V J) :
    (∫ u, actualRowInformation β W V J (actualRowDBracket W β V) u
      ∂actualParisiFullQuerySpinLaw W Z β V) = actualParisiEntropyReference W β V := by
  obtain ⟨hl, hj, hq⟩ := actualRowInformation_terms_integrable W Z β hβ V J hJ
  have hlog : (∫ u, Real.log (actualRowLink β W V u)
      ∂actualParisiFullQuerySpinLaw W Z β V) =
      ∫ u, Real.log (actualParisiFullTerminalSpinDensity β W V u)
        ∂actualParisiFullTerminalSpinLaw β W V :=
    (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).integral_comp
      (measurable_actualParisiFullTerminalSpinDensity β W V).log.aestronglyMeasurable
  unfold actualRowInformation rowInformation
  rw [integral_add (f := fun u => Real.log (actualRowLink β W V u) - J u)
      (g := fun u => actualRowDBracket W β V u / 2) (hl.sub hj) (hq.div_const 2),
    integral_sub hl hj, integral_div,
    hlog, N7.actualRowDIntegral_mean W Z β hβ V J hJ,
    N7.actualRowDBracket_mean W Z β hβ V]
  linarith [N7.scalar_information_balance_all_times W β hβ V]

theorem integrable_actualZeta
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (w c : ℕ → ℝ) (k : ℕ) (e : ℝ) (V : ℝ≥0) :
    Integrable (actualZeta W Z β hβ t w c k e) (actualParisiFullQuerySpinLaw W Z β V) := by
  have hp (s : ℝ≥0) : Integrable (actualRowPotential W β s)
      (actualParisiFullQuerySpinLaw W Z β V) :=
    Integrable.of_bound (measurable_actualRowPotential W β s).aestronglyMeasurable
      (3/2) (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs]
        exact actualRowPotential_abs_le W β s u))
  exact ((integrable_finsetSum (Finset.range k) (fun j _ =>
      ((hp _).sub (hp _)).const_mul (w j))).add
    (integrable_finsetSum (Finset.range k) (fun j _ =>
      (integrable_actualRowQueryDefect W Z β hβ _ _ V).const_mul (c j)))).sub
    (integrable_const (e/2))

theorem coarsePsi_mean
    {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ) (J : (Bool × Ω) × A → ℝ)
    (hJ : IsActualRowDIntegral W Z β hβ (growingQueryTime δ (k+1)) J) :
    (∫ u, N13e.coarsePsi W Z β hβ δ k J u
      ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (k+1))) =
      actualParisiEntropyReference W β (growingQueryTime δ (k+1)) -
        β * actualCoarseEnergy W β (growingQueryTime δ) k := by
  obtain ⟨hl, hj, hq⟩ := actualRowInformation_terms_integrable W Z β hβ _ J hJ
  have hi : Integrable (actualRowInformation β W _ J (actualRowDBracket W β _))
      (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (k+1))) :=
    (hl.sub hj).add (hq.div_const 2)
  unfold N13e.coarsePsi actualPsi
  rw [integral_sub hi ((integrable_actualZeta W Z β hβ _ _ _ _ _ _).const_mul β),
    integral_const_mul, actualRowInformation_mean W Z β hβ _ J hJ,
    actualCoarseZeta_mean W Z β hβ _ (growingQueryTime_strictMono δ hδ) k _ le_rfl]

theorem actualCoarseEnergy_eq_growingEnergySum
    (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (k : ℕ) :
    actualCoarseEnergy W β (growingQueryTime δ) k =
      LQ.actualParisiGrowingEnergySum W β δ k := by
  unfold actualCoarseEnergy LQ.actualParisiGrowingEnergySum
  apply Finset.sum_congr rfl
  intro j _
  unfold actualCoarseSpinMean actualCoarseScale actualQueryCellMean
    LQ.actualParisiQueryIntervalSpinMean
  rw [mul_comm]
  congr 1
  · congr 1
    apply intervalIntegral.integral_congr
    intro v _
    exact mul_comm _ _

theorem coarsePsi_mean_pressure
    {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ)
    (hV : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ growingQueryTime δ (k+1))
    (J : (Bool × Ω) × A → ℝ)
    (hJ : IsActualRowDIntegral W Z β hβ (growingQueryTime δ (k+1)) J) :
    (∫ u, N13e.coarsePsi W Z β hβ δ k J u
      ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (k+1))) =
      Real.log 2 - Blueprint.parisiPressure β +
        β^2/4 * (actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (k+1)))^2 +
        β * (actualParisiEnergyReference W β (growingQueryTime δ (k+1)) -
          actualCoarseEnergy W β (growingQueryTime δ) k) := by
  rw [coarsePsi_mean W Z β hβ δ hδ k J hJ]
  have h := actualParisi_scalar_entropy_energy_identity W β hβ _ hV
  change Real.log 2 - _ + β * _ = Blueprint.parisiPressure β - _ at h
  linarith

theorem actualCoarseEnergy_quadrature_error
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ)
    (hsmall : ∀ i < k+1, growingQueryDuration δ i ≤ 1) :
    |actualCoarseEnergy W β (growingQueryTime δ) k -
      actualParisiEnergyReference W β (growingQueryTime δ (k+1))| ≤
      (1/β^2 + 33 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ)+1)/2)) * (δ : ℝ) := by
  rw [actualCoarseEnergy_eq_growingEnergySum]
  exact LQ.actual_growing_energy_error W β hβ δ hδ k hsmall

end SKConstants.Completion.N13f

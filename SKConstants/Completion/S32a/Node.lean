module

public import SKConstants.Completion.Blueprint5a.Statements

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace SKConstants.Completion.S32a
open SKConstantsOAI.ZeroTemperatureSK

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

omit [MeasurableSpace Ω] in
theorem scalarGlobalStieltjesWeightedProcess_eq_of_endpoints
    (f : StieltjesFunction ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (h : f t = f 0) (w : Ω) :
    scalarGlobalStieltjesWeightedProcess f B t w = f t * B t w := by
  have hz : f.measure (Ioc (0 : ℝ) (t : ℝ)) = 0 := by
    rw [f.measure_Ioc, h, sub_self, ENNReal.ofReal_zero]
  unfold scalarGlobalStieltjesWeightedProcess
  rw [intervalIntegral.integral_of_le t.coe_nonneg, setIntegral_measure_zero _ hz, sub_zero]

theorem actualParisiQueryDriver_eq_driver_pre
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (u : Ω × A) :
    (actualParisiQueryBrownianSystem W Z β hβ).B t u = W.driver t u.1 := by
  have ht' : (t : ℝ) ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ) := ht
  have h0 : (0 : ℝ) ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ) :=
    (parisiEquilibriumPhysicalEndpoint β).coe_nonneg
  have hft : actualParisiNegativeRhoStieltjes W β hβ t = -1 := by
    change -actualParisiQueryRho W β t = -1
    rw [actualParisiQueryRho_eq_one_pre W β hβ t ht']
  have hf0 : actualParisiNegativeRhoStieltjes W β hβ 0 = -1 := by
    change -actualParisiQueryRho W β 0 = -1
    rw [actualParisiQueryRho_eq_one_pre W β hβ 0 h0]
  have hgt : actualParisiSigmaStieltjes W β hβ t = 0 :=
    actualParisiQuerySigma_eq_zero_pre W β hβ t ht'
  have hg0 : actualParisiSigmaStieltjes W β hβ 0 = 0 :=
    actualParisiQuerySigma_eq_zero_pre W β hβ 0 h0
  change -scalarGlobalStieltjesWeightedProcess
      (actualParisiNegativeRhoStieltjes W β hβ) W.driver t u.1 +
    scalarGlobalStieltjesWeightedProcess (actualParisiSigmaStieltjes W β hβ)
      Z.driver t u.2 = W.driver t u.1
  rw [scalarGlobalStieltjesWeightedProcess_eq_of_endpoints _ _ t (hft.trans hf0.symm),
    scalarGlobalStieltjesWeightedProcess_eq_of_endpoints _ _ t (hgt.trans hg0.symm),
    hft, hgt]
  ring

theorem actualParisiQueryDriver_eq_pre_ae
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z, ∀ t : ℝ≥0,
      t ≤ parisiEquilibriumPhysicalEndpoint β →
        (actualParisiQueryBrownianSystem W Z β hβ).B t (u.1.2, u.2) = W.B t u.1.2 := by
  let := W.isProbability
  let := Z.isProbability
  have hd : ∀ᵐ u ∂LM4.actualRowBaseLaw W Z, ∀ t, W.driver t u.1.2 = W.B t u.1.2 :=
    (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
      (ν := Z.law)).quasiMeasurePreserving.ae
      ((measurePreserving_snd (μ := scalarHiddenPriorBool 0)
        (ν := W.law)).quasiMeasurePreserving.ae W.driver_indistinguishable)
  filter_upwards [hd] with u hu
  intro t ht
  exact (actualParisiQueryDriver_eq_driver_pre W Z β hβ t ht (u.1.2, u.2)).trans (hu t)

theorem preSupportQueryDriver_holds : Blueprint5a.PreSupportQueryDriverStatement := by
  intro Ω A _ _ W Z β hβ t ht
  filter_upwards [actualParisiQueryDriver_eq_pre_ae W Z β hβ] with u hu
  exact hu t ht

theorem actualParisiQueryDriver_eq_pre_linked_ae
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    ∀ᵐ u ∂actualParisiFullQuerySpinLaw W Z β V, ∀ t : ℝ≥0,
      t ≤ parisiEquilibriumPhysicalEndpoint β →
        (actualParisiQueryBrownianSystem W Z β hβ).B t (u.1.2, u.2) = W.B t u.1.2 :=
  (SJ3.rowLinked_absolutelyContinuous W Z β V).ae_le
    (actualParisiQueryDriver_eq_pre_ae W Z β hβ)

end SKConstants.Completion.S32a

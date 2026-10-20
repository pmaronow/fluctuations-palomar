module

public import SKConstants.Completion.N7.IntegralMean
public import SKConstants.Completion.N7.BracketMean
public import SKConstants.Completion.N7.EntropyMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N7
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 LM4 LM4b
variable {Ω : Type*} [MeasurableSpace Ω]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem modelObservationDHistory_hasLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    HasLaw (modelObservationDHistory W β hβ V) (unlinkedObservationDHistoryLaw W β hβ V)
      (actualRowBaseLaw W W) :=
  ⟨(measurable_modelObservationDHistory W β hβ V).aemeasurable, rfl⟩

theorem modelObservationDHistory_paths_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    ∀ᵐ u ∂actualRowBaseLaw W W, ∀ s : ℝ≥0, s ≤ V →
      historyPathAt V (modelObservationDHistory W β hβ V u).2.1 s =
        actualParisiFullScalarProcess W β s u.1.2 ∧
      historyPathAt V (modelObservationDHistory W β hβ V u).2.2 s =
        (actualParisiAuxBrownianSystem W W β hβ).B s (u.1.2, u.2) := by
  have hY := ((measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
    (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
      (ν := W.law))).quasiMeasurePreserving.ae
        (boundedDriftPastPath_version W (actualParisiFullScalarDrift β) V)
  have hdrivers := (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).prod
    (MeasurePreserving.id W.law)
  have hD := hdrivers.quasiMeasurePreserving.ae
    (brownianFinitePath_version (actualParisiAuxBrownianSystem W W β hβ) V)
  filter_upwards [hY, hD] with u hy hd
  intro s hs
  dsimp only [historyPathAt, modelObservationDHistory]
  rw [projIcc_of_mem _ ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩]
  exact ⟨hy ⟨s, s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩,
    hd ⟨s, s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩⟩

theorem historyDLeftSum_model_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    (fun u => historyDLeftSum W β V l (modelObservationDHistory W β hβ V u))
      =ᵐ[actualRowBaseLaw W W] actualRowDLeftSum W W β hβ V l := by
  filter_upwards [modelObservationDHistory_paths_ae W β hβ V] with u hu
  simp only [historyDLeftSum, predictableGaussianSum_eq_fin_sum, actualRowDLeftSum,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [historyDCoefficient, actualRowDCoefficient]
  rw [(hu _ (dyadic_time_le_horizon V l k k.isLt.le)).1,
    (hu _ (dyadic_time_le_horizon V l (k + 1) k.isLt)).2,
    (hu _ (dyadic_time_le_horizon V l k k.isLt.le)).2]
  rfl

theorem historyDIntegral_model
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J) :
    IsActualRowDIntegral W W β hβ V (J ∘ modelObservationDHistory W β hβ V) := by
  have hm := modelObservationDHistory_hasLaw W β hβ V
  have hErr (l : ℕ) := (hJ.2.1 l)
  have hErrm (l : ℕ) : AEStronglyMeasurable
      (fun h => (historyDLeftSum W β V l h - J h) ^ 2)
      (unlinkedObservationDHistoryLaw W β hβ V) := (hErr l).aestronglyMeasurable
  have he (l : ℕ) : (fun u => (historyDLeftSum W β V l
      (modelObservationDHistory W β hβ V u) - J (modelObservationDHistory W β hβ V u)) ^ 2)
      =ᵐ[actualRowBaseLaw W W]
      (fun u => (actualRowDLeftSum W W β hβ V l u -
        (J ∘ modelObservationDHistory W β hβ V) u) ^ 2) :=
    (historyDLeftSum_model_ae W β hβ V l).mono (fun u hu => by
      dsimp only [Function.comp_def] at hu ⊢
      rw [hu])
  refine ⟨hm.memLp_fun_comp hJ.1, ?_, ?_⟩
  · intro l
    exact (hm.integrable_fun_comp (hErr l)).congr (he l)
  · apply hJ.2.2.congr'
    apply Eventually.of_forall
    intro l
    exact ((hm.integral_comp (hErrm l)).symm).trans (integral_congr_ae (he l))

theorem historyDIntegral_mean
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J) :
    (∫ h, J h ∂linkedObservationDHistoryLaw W β hβ V) =
      ∫ r in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β r) ^ 2 *
        actualParisiFullSusceptibilityExpected W β r := by
  rw [linkedObservationDHistoryLaw, integral_map
    (measurable_modelObservationDHistory W β hβ V).aemeasurable
    (history_information_terms_integrable W β hβ V J hJ).2.1.aestronglyMeasurable]
  exact actualRowDIntegral_mean W W β hβ V _ (historyDIntegral_model W β hβ V J hJ)

theorem historyDBracket_model_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (fun u => historyDBracket W β V (modelObservationDHistory W β hβ V u))
      =ᵐ[actualRowBaseLaw W W] actualRowDBracket W β V := by
  filter_upwards [modelObservationDHistory_paths_ae W β hβ V] with u hu
  unfold historyDBracket actualRowDBracket
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le V.coe_nonneg] at ht
  have htV : t.toNNReal ≤ V := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal t ht.1]
    exact ht.2
  dsimp only [historyDCoefficient, actualRowDCoefficient]
  rw [← Real.coe_toNNReal t ht.1, (hu _ htV).1]
  simp only [Real.toNNReal_coe]
  rfl

theorem historyDBracket_mean
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (∫ h, historyDBracket W β V h ∂linkedObservationDHistoryLaw W β hβ V) =
      ∫ r in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β r) ^ 2 *
        actualParisiFullSusceptibilityExpected W β r := by
  have hac : actualParisiFullQuerySpinLaw W W β V ≪ actualRowBaseLaw W W := by
    rw [← LM4.actual_linkedRowLaw_eq β W W V]
    exact withDensity_absolutelyContinuous _ _
  rw [linkedObservationDHistoryLaw, integral_map
    (measurable_modelObservationDHistory W β hβ V).aemeasurable
    (measurable_historyDBracket W β V).aestronglyMeasurable,
    integral_congr_ae (hac.ae_le (historyDBracket_model_ae W β hβ V))]
  exact actualRowDBracket_mean W W β hβ V

theorem history_information_mean
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J) :
    (∫ h, historyInformation W β V J h ∂linkedObservationDHistoryLaw W β hβ V) =
      actualParisiEntropyReference W β V := by
  have ht := history_information_terms_integrable W β hβ V J hJ
  unfold historyInformation
  rw [integral_add
      (f := fun h => Real.log (historyLinkDensity β V h) - J h)
      (g := fun h => historyDBracket W β V h / 2) (ht.1.sub ht.2.1) (ht.2.2.div_const 2),
    integral_sub ht.1 ht.2.1, integral_div, history_log_mean_eq_scalar_log W β hβ V,
    historyDIntegral_mean W β hβ V J hJ, historyDBracket_mean W β hβ V]
  linarith [scalar_information_balance_all_times W β hβ V]

end SKConstants.Completion.N7

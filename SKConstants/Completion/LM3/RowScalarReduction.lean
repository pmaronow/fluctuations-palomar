module
public import SKConstants.Completion.LM3.RowInformationMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

theorem history_log_mean_eq_scalar_log
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (∫ h, Real.log (historyLinkDensity β V h) ∂linkedObservationDHistoryLaw W β hβ V) =
      ∫ u, Real.log (actualParisiFullTerminalSpinDensity β W V u)
        ∂actualParisiFullTerminalSpinLaw β W V := by
  have hmp : MeasurePreserving (fun u : (Bool × Ω) × Ω => u.1.2)
      (actualParisiFullQuerySpinLaw W W β V) W.law :=
    ⟨measurable_fst.snd, (actualParisiFullQuerySpinLaw_path_hasLaw W W β V).map_eq⟩
  have hy := hmp.quasiMeasurePreserving.ae
    (boundedDriftPastPath_version W (actualParisiFullScalarDrift β) V)
  have he : (fun u => Real.log (historyLinkDensity β V (modelObservationDHistory W β hβ V u)))
      =ᵐ[actualParisiFullQuerySpinLaw W W β V]
      (fun u => Real.log (actualParisiFullTerminalSpinDensity β W V u.1)) := by
    filter_upwards [hy] with u hu
    congr 1
    exact congrArg (actualParisiSpinLinkDensity β u.1.1 V) (hu ⟨V, V.coe_nonneg, le_rfl⟩)
  rw [linkedObservationDHistoryLaw, integral_map
    (measurable_modelObservationDHistory W β hβ V).aemeasurable
    (measurable_historyLinkDensity β V).log.aestronglyMeasurable, integral_congr_ae he]
  exact (actualParisiFullQuerySpinLaw_terminal_hasLaw W W β V).integral_comp
    (measurable_actualParisiFullTerminalSpinDensity β W V).log.aestronglyMeasurable

theorem history_information_mean_scalar_reduction
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J) :
    (∫ h, historyInformation W β V J h ∂linkedObservationDHistoryLaw W β hβ V) =
      actualParisiEntropyReference W β V +
        ((∫ w, actualParisiMagnetizationObservable W β V w *
          scalarGlobalStieltjesWeightedProcess (actualSigmaSquareStieltjes W β hβ) W.driver V w
            ∂W.law) - (∫ h, J h ∂linkedObservationDHistoryLaw W β hβ V)) +
        ((∫ h, historyDBracket W β V h ∂linkedObservationDHistoryLaw W β hβ V) -
          (∫ w, actualParisiMagnetizationObservable W β V w *
            scalarGlobalStieltjesWeightedProcess (actualSigmaSquareStieltjes W β hβ) W.driver V w
              ∂W.law)) / 2 := by
  have ht := history_information_terms_integrable W β hβ V J hJ
  have hs := scalar_information_balance W β hβ V hV
  unfold historyInformation
  rw [integral_add
      (f := fun h => Real.log (historyLinkDensity β V h) - J h)
      (g := fun h => historyDBracket W β V h / 2) (ht.1.sub ht.2.1) (ht.2.2.div_const 2),
    integral_sub ht.1 ht.2.1, integral_div, history_log_mean_eq_scalar_log W β hβ V]
  linarith

theorem growingReplay_information_mean_scalar_reduction
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hV : parisiEquilibriumPhysicalEndpoint β ≤ V)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ ranks q V hVH)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    (∫ u, growingReplayInformation W β hβ δ hδ ranks q V I u
      ∂growingReplayLinkedLaw W β hβ δ ranks q V) =
      (ranks + q : ℕ) * (actualParisiEntropyReference W β V +
        ((∫ w, actualParisiMagnetizationObservable W β V w *
          scalarGlobalStieltjesWeightedProcess (actualSigmaSquareStieltjes W β hβ) W.driver V w
            ∂W.law) - (∫ h, J h ∂linkedObservationDHistoryLaw W β hβ V)) +
        ((∫ h, historyDBracket W β V h ∂linkedObservationDHistoryLaw W β hβ V) -
          (∫ w, actualParisiMagnetizationObservable W β V w *
            scalarGlobalStieltjesWeightedProcess (actualSigmaSquareStieltjes W β hβ) W.driver V w
              ∂W.law)) / 2) := by
  rw [growingReplay_information_mean_eq_row_mean W β hβ δ hδ ranks q V hVH hHist J hJ I hI,
    history_information_mean_scalar_reduction W β hβ V hV J hJ]

end SKConstants.Completion.LM3

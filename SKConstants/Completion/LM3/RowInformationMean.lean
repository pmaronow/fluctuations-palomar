module
public import SKConstants.Completion.LM3.RowL2Identification
public import SKConstants.ProposalGibbsChangeOfMeasure

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_historyLinkDensity (β : ℝ) (V : ℝ≥0) :
    Measurable (historyLinkDensity β V) := by
  have hy : Measurable (fun h : ObservationDHistory V => h.2.1 ⟨V, V.coe_nonneg, le_rfl⟩) :=
    (ContinuousMap.measurable_eval _).comp measurable_snd.fst
  have hm : Measurable (fun h : ObservationDHistory V =>
      actualParisiFullMagnetization β V (h.2.1 ⟨V, V.coe_nonneg, le_rfl⟩)) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp hy
  exact measurable_const.add
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul hm)

theorem linkedObservationDHistoryLaw_eq_withDensity
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    linkedObservationDHistoryLaw W β hβ V =
      (unlinkedObservationDHistoryLaw W β hβ V).withDensity
        (fun h => ENNReal.ofReal (historyLinkDensity β V h)) := by
  let := W.isProbability
  let μ := ((scalarHiddenPriorBool 0).prod W.law).prod W.law
  have hY := ((measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
    (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
      (ν := W.law))).quasiMeasurePreserving.ae
    (boundedDriftPastPath_version W (actualParisiFullScalarDrift β) V)
  have hd : (fun u : (Bool × Ω) × Ω =>
      ENNReal.ofReal (actualParisiFullTerminalSpinDensity β W V u.1)) =ᵐ[μ]
      (fun u => ENNReal.ofReal (historyLinkDensity β V (modelObservationDHistory W β hβ V u))) := by
    filter_upwards [hY] with u hu
    congr 1
    exact (congrArg (actualParisiSpinLinkDensity β u.1.1 V)
      (hu ⟨V, V.coe_nonneg, le_rfl⟩)).symm
  unfold linkedObservationDHistoryLaw actualParisiFullQuerySpinLaw actualParisiFullTerminalSpinLaw
  rw [prod_withDensity_left (measurable_actualParisiFullTerminalSpinDensity β W V).ennreal_ofReal,
    withDensity_congr_ae hd]
  exact map_withDensity_comp μ (modelObservationDHistory W β hβ V)
    (measurable_modelObservationDHistory W β hβ V) _
    (measurable_historyLinkDensity β V).ennreal_ofReal

theorem continuous_historyDCoefficient_time (W : BrownianSystem Ω) (β : ℝ)
    (V : ℝ≥0) (h : ObservationDHistory V) : Continuous (fun t => historyDCoefficient W β V t h) := by
  have hy : Continuous (fun t : ℝ => historyPathAt V h.2.1 t) :=
    h.2.1.continuous.comp (continuous_projIcc (h := V.coe_nonneg))
  have hp : Continuous (fun t : ℝ => (t, historyPathAt V h.2.1 t)) := continuous_id.prodMk hy
  have hxi := (continuous_actualParisiSpinLinkCoefficient β h.1).comp hp
  convert (continuous_actualParisiQuerySigma W β).mul hxi using 1
  funext t
  rfl

theorem measurable_historyDBracket (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) :
    Measurable (historyDBracket W β V) := by
  have hy : Measurable (fun p : ℝ × ObservationDHistory V => historyPathAt V p.2.2.1 p.1) :=
    (continuous_eval.comp
      (continuous_snd.snd.fst.prodMk
        ((continuous_projIcc (h := V.coe_nonneg)).comp continuous_fst))).measurable
  have hm := (continuous_actualParisiFullMagnetization β).measurable.comp (measurable_fst.prodMk hy)
  have ha := (continuous_actualParisiFullCurvature β).measurable.comp (measurable_fst.prodMk hy)
  have hx : Measurable (fun p : ℝ × ObservationDHistory V => scalarHiddenSign p.2.1) :=
    (measurable_of_finite scalarHiddenSign).comp measurable_snd.fst
  have hg : Measurable (fun p : ℝ × ObservationDHistory V =>
      (historyDCoefficient W β V p.1 p.2)^2) :=
    (((continuous_actualParisiQuerySigma W β).measurable.comp measurable_fst).mul
      ((hx.mul ha).div (measurable_const.add (hx.mul hm)))).pow_const 2
  unfold historyDBracket
  simp_rw [intervalIntegral.integral_of_le V.coe_nonneg]
  exact hg.stronglyMeasurable.integral_prod_left'.measurable

theorem historyDBracket_bounds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (h : ObservationDHistory V) :
    0 ≤ historyDBracket W β V h ∧ historyDBracket W β V h ≤ 4 * (V : ℝ) := by
  have hc : Continuous (fun t => (historyDCoefficient W β V t h)^2) :=
    (continuous_historyDCoefficient_time W β V h).pow 2
  have hb (t : ℝ) : |historyDCoefficient W β V t h| ≤ 2 := by
    rw [historyDCoefficient, abs_mul, abs_of_nonneg (actualParisiQuerySigma_bounds W β hβ t).1]
    exact (mul_le_mul (actualParisiQuerySigma_bounds W β hβ t).2
      (actualParisiSpinLinkCoefficient_bound β h.1 t _) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  unfold historyDBracket
  refine ⟨intervalIntegral.integral_nonneg V.coe_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  have hi := intervalIntegral.integral_mono_on (μ := volume) V.coe_nonneg
    (hc.intervalIntegrable 0 V) (continuous_const.intervalIntegrable 0 V)
    (fun t _ => show (historyDCoefficient W β V t h)^2 ≤ (4 : ℝ) by
      have hs := pow_le_pow_left₀ (abs_nonneg _) (hb t) 2
      simpa only [sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using hs)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hi

theorem history_information_terms_integrable
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J) :
    Integrable (fun h => Real.log (historyLinkDensity β V h)) (linkedObservationDHistoryLaw W β hβ V) ∧
    Integrable J (linkedObservationDHistoryLaw W β hβ V) ∧
    Integrable (historyDBracket W β V) (linkedObservationDHistoryLaw W β hβ V) := by
  have hp (h : ObservationDHistory V) : 0 < historyLinkDensity β V h :=
    actualParisiSpinLinkDensity_pos β _ V _
  have hb (h : ObservationDHistory V) : historyLinkDensity β V h ≤ 2 :=
    actualParisiSpinLinkDensity_le_two β _ V _
  have hQ : Integrable (historyDBracket W β V) (linkedObservationDHistoryLaw W β hβ V) :=
    Integrable.of_bound (measurable_historyDBracket W β V).aestronglyMeasurable (4 * (V : ℝ))
      (ae_of_all _ (fun h => by
        rw [Real.norm_eq_abs, abs_of_nonneg (historyDBracket_bounds W β hβ V h).1]
        exact (historyDBracket_bounds W β hβ V h).2))
  refine ⟨?_, ?_, hQ⟩
  · rw [linkedObservationDHistoryLaw_eq_withDensity]
    exact integrable_log_withDensity_of_bounded _ _ (measurable_historyLinkDensity β V)
      (fun h => (hp h).le) 2 hb
  · rw [linkedObservationDHistoryLaw_eq_withDensity]
    exact integrable_withDensity_of_bounded _ _ (measurable_historyLinkDensity β V)
      (fun h => (hp h).le) 2 hb (hJ.1.integrable (by norm_num))

theorem growingReplay_information_mean_eq_row_mean
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ ranks q V hVH)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    (∫ u, growingReplayInformation W β hβ δ hδ ranks q V I u
      ∂growingReplayLinkedLaw W β hβ δ ranks q V) =
      (ranks + q : ℕ) * (∫ h, historyInformation W β V J h
        ∂linkedObservationDHistoryLaw W β hβ V) := by
  have ht := history_information_terms_integrable W β hβ V J hJ
  have hi : Integrable (historyInformation W β V J) (linkedObservationDHistoryLaw W β hβ V) :=
    (ht.1.sub ht.2.1).add (ht.2.2.div_const 2)
  have hlaw := canonical_linked_row_hasLaw W β hβ δ hδ ranks q V hVH hHist
  have he (i : Fin (ranks + q)) := (hlaw i).integral_comp hi.aestronglyMeasurable
  simp only [Function.comp_def] at he
  rw [integral_congr_ae (growingReplayInformation_eq_history_sum_ae W β hβ δ hδ ranks q V hVH
      hHist J hJ I hI), integral_finsetSum _ (fun i _ => (hlaw i).integrable_fun_comp hi)]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end SKConstants.Completion.LM3

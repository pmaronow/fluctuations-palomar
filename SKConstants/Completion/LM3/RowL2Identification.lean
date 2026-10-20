module
public import SKConstants.Completion.LM3.RowIntegralTransport

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

theorem canonical_unlinked_row_hasLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ ranks q V hVH)
    (i : Fin (ranks + q)) :
    HasLaw (fun u => replayObservationDHistory W β hβ δ ranks q V hVH u i)
      (unlinkedObservationDHistoryLaw W β hβ V) (growingReplayUnlinkedLaw W δ ranks q) := by
  have hall : HasLaw (replayObservationDHistory W β hβ δ ranks q V hVH)
      (Measure.pi (fun _ : Fin (ranks + q) => unlinkedObservationDHistoryLaw W β hβ V))
      (growingReplayUnlinkedLaw W δ ranks q) :=
    ⟨(measurable_replayObservationDHistory W β hβ δ hδ ranks q V hVH).aemeasurable, hHist.1⟩
  exact (measurePreserving_eval (fun _ : Fin (ranks + q) =>
    unlinkedObservationDHistoryLaw W β hβ V) i).hasLaw.comp hall

theorem canonical_linked_row_hasLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ ranks q V hVH)
    (i : Fin (ranks + q)) :
    HasLaw (fun u => replayObservationDHistory W β hβ δ ranks q V hVH u i)
      (linkedObservationDHistoryLaw W β hβ V) (growingReplayLinkedLaw W β hβ δ ranks q V) := by
  have hall : HasLaw (replayObservationDHistory W β hβ δ ranks q V hVH)
      (Measure.pi (fun _ : Fin (ranks + q) => linkedObservationDHistoryLaw W β hβ V))
      (growingReplayLinkedLaw W β hβ δ ranks q V) :=
    ⟨(measurable_replayObservationDHistory W β hβ δ hδ ranks q V hVH).aemeasurable, hHist.2⟩
  exact (measurePreserving_eval (fun _ : Fin (ranks + q) =>
    linkedObservationDHistoryLaw W β hβ V) i).hasLaw.comp hall

theorem growingReplayDIntegral_of_history
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ ranks q V hVH)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J) :
    IsGrowingReplayDIntegral W β hβ δ hδ ranks q V
      (fun u => ∑ i, J (replayObservationDHistory W β hβ δ ranks q V hVH u i)) := by
  let R := replayObservationDHistory W β hβ δ ranks q V hVH
  have hR := canonical_unlinked_row_hasLaw W β hβ δ hδ ranks q V hVH hHist
  have hE (l : ℕ) : MemLp (fun h => historyDLeftSum W β V l h - J h) 2
      (unlinkedObservationDHistoryLaw W β hβ V) :=
    (memLp_two_iff_integrable_sq
      (((measurable_historyDLeftSum W β V l).aemeasurable.sub hJ.1.aemeasurable).aestronglyMeasurable)).mpr
        (hJ.2.1 l)
  have hPull (i : Fin (ranks + q)) (l : ℕ) := (hR i).memLp_fun_comp (hE l)
  have hMean (i : Fin (ranks + q)) (l : ℕ) :
      (∫ u, (historyDLeftSum W β V l (R u i) - J (R u i))^2
        ∂growingReplayUnlinkedLaw W δ ranks q) =
      ∫ h, (historyDLeftSum W β V l h - J h)^2 ∂unlinkedObservationDHistoryLaw W β hβ V :=
    (hR i).integral_comp ((hE l).aemeasurable.pow_const 2).aestronglyMeasurable
  have hlim (i : Fin (ranks + q)) :
      Tendsto (fun l => ∫ u, (historyDLeftSum W β V l (R u i) - J (R u i))^2
        ∂growingReplayUnlinkedLaw W δ ranks q) atTop (𝓝 0) := by
    simp_rw [hMean]
    exact hJ.2.2
  have hErr (l : ℕ) :
      (fun u => (growingReplayDLeftSum W β hβ δ hδ ranks q V l u - ∑ i, J (R u i))^2)
        =ᵐ[growingReplayUnlinkedLaw W δ ranks q]
      (fun u => (∑ i, (historyDLeftSum W β V l (R u i) - J (R u i)))^2) := by
    filter_upwards [growingReplayDLeftSum_eq_history_sum_ae W β hβ δ hδ ranks q V hVH l]
      with u hu
    rw [hu, Finset.sum_sub_distrib]
  refine ⟨memLp_finsetSum Finset.univ (fun i _ => (hR i).memLp_fun_comp hJ.1), ?_, ?_⟩
  · intro l
    exact (integrable_sq_finset_sum Finset.univ
      (fun i _ => (hPull i l).aemeasurable) (fun i _ => (hPull i l).integrable_sq)).congr
        (hErr l).symm
  · have ht := tendsto_integral_sq_finset_sum Finset.univ
      (fun i _ l => (hPull i l).aemeasurable) (fun i _ l => (hPull i l).integrable_sq)
      (fun i _ => hlim i)
    exact ht.congr' (Eventually.of_forall (fun l => integral_congr_ae (hErr l).symm))

theorem growingReplayDIntegral_eq_history_sum_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ ranks q V hVH)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    I =ᵐ[growingReplayUnlinkedLaw W δ ranks q]
      fun u => ∑ i, J (replayObservationDHistory W β hβ δ ranks q V hVH u i) :=
  growingReplayDIntegral_unique W β hβ δ hδ ranks q V I _ hI
    (growingReplayDIntegral_of_history W β hβ δ hδ ranks q V hVH hHist J hJ)

def historyInformation (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0)
    (J : ObservationDHistory V → ℝ) (h : ObservationDHistory V) : ℝ :=
  Real.log (historyLinkDensity β V h) - J h + historyDBracket W β V h / 2

theorem growingReplayInformation_eq_history_sum_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ ranks q V hVH)
    (J : ObservationDHistory V → ℝ) (hJ : IsHistoryDIntegral W β hβ V J)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    growingReplayInformation W β hβ δ hδ ranks q V I =ᵐ[
      growingReplayLinkedLaw W β hβ δ ranks q V]
      fun u => ∑ i, historyInformation W β V J
        (replayObservationDHistory W β hβ δ ranks q V hVH u i) := by
  have hac : growingReplayLinkedLaw W β hβ δ ranks q V ≪ growingReplayUnlinkedLaw W δ ranks q :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [(growingReplayDIntegral_eq_history_sum_ae W β hβ δ hδ ranks q V hVH
      hHist J hJ I hI).filter_mono hac.ae_le,
    (growingReplayDBracket_eq_history_sum_ae W β hβ δ hδ ranks q V hVH).filter_mono hac.ae_le]
    with u hi hq
  have hp (i : Fin (ranks + q)) : historyLinkDensity β V
      (replayObservationDHistory W β hβ δ ranks q V hVH u i) ≠ 0 :=
    (actualParisiSpinLinkDensity_pos β _ V _).ne'
  rw [growingReplayInformation_eq, growingReplayLinkDensity_eq_history_product W β hβ δ ranks q V hVH,
    Real.log_prod (fun i _ => hp i), hi, hq]
  simp only [historyInformation, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]

end SKConstants.Completion.LM3

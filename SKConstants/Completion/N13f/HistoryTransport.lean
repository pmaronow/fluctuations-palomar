module

public import SKConstants.Completion.N7.HistoryIntegral
public import SKConstants.Completion.N13f.InformationMean
public import SKConstants.Completion.NScalar.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 LM4 LM4b
variable {Ω : Type*} [MeasurableSpace Ω]

theorem replayRowBracket_eq_history_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q) (i : Fin (r+q)) :
    replayRowBracket W β hβ δ hδ r q V i =ᵐ[growingReplayUnlinkedLaw W δ r q]
      fun u => historyDBracket W β V (replayObservationDHistory W β hβ δ r q V hVH u i) := by
  filter_upwards [replayDCoefficient_eq_history_ae W β hβ δ hδ r q V hVH] with u hu
  change (∫ s in (0 : ℝ)..(V : ℝ), (brownianVectorContinuousCoefficient W.B
    (actualParisiGrowingReplayDCoefficient W β hβ δ hδ r q) s.toNNReal u i)^2) = _
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le V.coe_nonneg] at hs
  have hsV : s.toNNReal ≤ V := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal s hs.1]
    exact hs.2
  dsimp only [historyDBracket]
  rw [hu _ hsV i, Real.coe_toNNReal s hs.1]

theorem actualRowReferenceTransport_of_historyLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ r q V hVH)
    (i : Fin (r+q)) : ActualRowReferenceTransportStatement W W β hβ δ hδ r q V i := by
  let F : ObservationDHistory V → (ℕ → ℝ) × ℝ :=
    fun h => ((fun l => historyDLeftSum W β V l h), historyDBracket W β V h)
  have hFm : Measurable F :=
    (Measurable.of_eval (fun l => measurable_historyDLeftSum W β V l)).prodMk
      (measurable_historyDBracket W β V)
  have hd := ((canonical_unlinked_row_hasLaw W β hβ δ hδ r q V hVH hHist i).identDistrib
    (N7.modelObservationDHistory_hasLaw W β hβ V)).comp hFm
  have hR : (fun u => ((fun l => replayRowLeftSum W β hβ δ hδ r q V i l u),
      replayRowBracket W β hβ δ hδ r q V i u)) =ᵐ[growingReplayUnlinkedLaw W δ r q]
      F ∘ (fun u => replayObservationDHistory W β hβ δ r q V hVH u i) := by
    filter_upwards [ae_all_iff.mpr (fun l =>
      N7.replayRowLeftSum_eq_history_ae W β hβ δ hδ r q V hVH i l),
      replayRowBracket_eq_history_ae W β hβ δ hδ r q V hVH i] with u hu hq
    exact Prod.ext (funext hu) hq
  have hM : F ∘ modelObservationDHistory W β hβ V =ᵐ[actualRowBaseLaw W W]
      fun u => ((fun l => actualRowDLeftSum W W β hβ V l u),actualRowDBracket W β V u) := by
    filter_upwards [ae_all_iff.mpr (fun l => N7.historyDLeftSum_model_ae W β hβ V l),
      N7.historyDBracket_model_ae W β hβ V] with u hu hq
    exact Prod.ext (funext hu) hq
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst hR.symm).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd hM)

theorem coarsePsi_iid_abs_of_historyLaw
    {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r k : ℕ) (i : Fin (r+k))
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ r k
      (growingQueryTime δ (k+1)) le_rfl)
    (J : (Bool × Ω) × Ω → ℝ) (hJm : Measurable J)
    (hJ : IsActualRowDIntegral W W β hβ (growingQueryTime δ (k+1)) J)
    (hsmall : ∀ j < k, (growingQueryDuration δ (j+1) : ℝ) ≤ 1/8)
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let V := growingQueryTime δ (k+1)
    let ν := actualParisiFullQuerySpinLaw W W β V
    (actualParisiFullMixedRowsLaw W W β V n).real {u | (n : ℝ)*η ≤
      |∑ j : Fin n, Concentration.centeredObservable ν (N13e.coarsePsi W W β hβ δ k J) (u j)|} ≤
      2*Real.exp (-(n : ℝ)*min
        (η^2/(8*(psiMomentConstant β*(1+(V : ℝ)))^2))
        (η/(4*(psiMomentConstant β*(1+(V : ℝ)))))) :=
  N13e.coarsePsi_iid_abs NScalar.SusceptibilityProfileStatement_holds W W β hβ δ hδ r k i
    (actualRowReferenceTransport_of_historyLaw W β hβ δ hδ r k _ le_rfl hHist i)
    J hJm hJ hsmall hn hη

end SKConstants.Completion.N13f

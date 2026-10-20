module
public import SKConstants.Completion.LM3.RowHistory

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

instance unlinkedObservationDHistoryLaw_probability (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    IsProbabilityMeasure (unlinkedObservationDHistoryLaw W β hβ V) := by
  let := W.isProbability
  unfold unlinkedObservationDHistoryLaw
  infer_instance

instance linkedObservationDHistoryLaw_probability (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    IsProbabilityMeasure (linkedObservationDHistoryLaw W β hβ V) := by
  unfold linkedObservationDHistoryLaw
  infer_instance

theorem measurable_historyDCoefficient (W : BrownianSystem Ω) (β : ℝ)
    (V : ℝ≥0) (s : ℝ) : Measurable (historyDCoefficient W β V s) := by
  have hy : Measurable (fun h : ObservationDHistory V => historyPathAt V h.2.1 s) :=
    (ContinuousMap.measurable_eval _).comp measurable_snd.fst
  have hx := (measurable_of_finite scalarHiddenSign).comp
    (measurable_fst : Measurable (Prod.fst : ObservationDHistory V → Bool))
  have hm : Measurable (fun h : ObservationDHistory V =>
      actualParisiFullMagnetization β s (historyPathAt V h.2.1 s)) :=
    ((continuous_actualParisiFullMagnetization β).comp
    (continuous_const.prodMk continuous_id)).measurable.comp hy
  have ha : Measurable (fun h : ObservationDHistory V =>
      actualParisiFullCurvature β s (historyPathAt V h.2.1 s)) :=
    ((continuous_actualParisiFullCurvature β).comp
    (continuous_const.prodMk continuous_id)).measurable.comp hy
  exact ((hx.mul ha).div (measurable_const.add (hx.mul hm))).const_mul _

theorem measurable_historyDLeftSum (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) :
    Measurable (historyDLeftSum W β V l) := by
  have he : historyDLeftSum W β V l = fun h : ObservationDHistory V =>
      ∑ k : Fin (2^l), historyDCoefficient W β V ((brownianDyadicGrid V).time l k) h *
        (historyPathAt V h.2.2 ((brownianDyadicGrid V).time l (k + 1)) -
          historyPathAt V h.2.2 ((brownianDyadicGrid V).time l k)) := by
    funext h
    exact predictableGaussianSum_eq_fin_sum
      (fun (k : ℕ) (h : ObservationDHistory V) =>
        historyPathAt V h.2.2 ((brownianDyadicGrid V).time l (k + 1)) -
        historyPathAt V h.2.2 ((brownianDyadicGrid V).time l k))
      (fun k => historyDCoefficient W β V ((brownianDyadicGrid V).time l k)) (2^l) h
  rw [he]
  apply Finset.measurable_sum
  intro k _
  exact (measurable_historyDCoefficient W β V _).mul
    (((ContinuousMap.measurable_eval _).comp measurable_snd.snd).sub
      ((ContinuousMap.measurable_eval _).comp measurable_snd.snd))

theorem dyadic_time_le_horizon (V : ℝ≥0) (l k : ℕ) (hk : k ≤ 2^l) :
    (brownianDyadicGrid V).time l k ≤ V := by
  calc
    _ ≤ (brownianDyadicGrid V).time l (2^l) := (brownianDyadicGrid V).monotone l hk
    _ = V := by simp [brownianDyadicGrid]

theorem replayDCoefficient_eq_history_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q) :
    ∀ᵐ u ∂growingReplayUnlinkedLaw W δ ranks q, ∀ s : ℝ≥0, s ≤ V → ∀ i,
      brownianVectorContinuousCoefficient W.B
        (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) s u i =
      historyDCoefficient W β V s (replayObservationDHistory W β hβ δ ranks q V hVH u i) := by
  let := W.isProbability
  have he := (measurePreserving_snd
    (μ := parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q)
    (ν := Measure.pi (fun _ : Fin (ranks + q) => W.law))).quasiMeasurePreserving.ae
      (actualParisiGrowingReplayPastCallback_brownian_ae W β hβ δ hδ ranks q)
  filter_upwards [he] with u hu
  intro s hs i
  dsimp only [historyDCoefficient, replayObservationDHistory, historyPathAt, replayFieldPath]
  rw [projIcc_of_mem _ ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩]
  change actualParisiQuerySigma W β s * actualParisiSpinLinkCoefficient β (u.1.2 i) s
      (actualParisiGrowingReplayPastCallback W β hβ δ hδ ranks q s
        (u.1.1, fun t j => W.B t (u.2 j)) i) = _
  rw [hu u.1.1 s]
  rfl

theorem replayDPath_eq_history_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q) :
    ∀ᵐ u ∂growingReplayUnlinkedLaw W δ ranks q, ∀ s : ℝ≥0, s ≤ V → ∀ i,
      historyPathAt V (replayObservationDHistory W β hβ δ ranks q V hVH u i).2.2 s =
      W.B s (u.2 i) := by
  let := W.isProbability
  have he := (measurePreserving_snd
    (μ := parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q)
    (ν := Measure.pi (fun _ : Fin (ranks + q) => W.law))).quasiMeasurePreserving.ae
      (scalarPrimitiveBrownianVectorPathVersion_ae W (scalarGrowingSourceHorizon δ q) (ranks + q))
  filter_upwards [he] with u hu
  intro s hs i
  dsimp only [historyPathAt, replayObservationDHistory]
  rw [projIcc_of_mem _ ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩]
  exact hu i ⟨s, s.coe_nonneg, NNReal.coe_le_coe.mpr (hs.trans hVH)⟩

theorem growingReplayDLeftSum_eq_history_sum_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q) (l : ℕ) :
    growingReplayDLeftSum W β hβ δ hδ ranks q V l =ᵐ[growingReplayUnlinkedLaw W δ ranks q]
      fun u => ∑ i, historyDLeftSum W β V l
        (replayObservationDHistory W β hβ δ ranks q V hVH u i) := by
  filter_upwards [replayDCoefficient_eq_history_ae W β hβ δ hδ ranks q V hVH,
    replayDPath_eq_history_ae W β hβ δ ranks q V hVH] with u hc hd
  rw [growingReplayDLeftSum, brownianVectorContinuousLeftSum_eq_sum_coordinate]
  apply Finset.sum_congr rfl
  intro i _
  simp only [brownianVectorContinuousCoordinateLeftSum, brownianVectorCoordinatePredictableSum,
    historyDLeftSum, predictableGaussianSum_eq_fin_sum, one_mul]
  apply Finset.sum_congr rfl
  intro k _
  change brownianVectorContinuousCoefficient W.B
      (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q)
      ((brownianDyadicGrid V).time l k) u i *
      (W.B ((brownianDyadicGrid V).time l (k + 1)) (u.2 i) -
        W.B ((brownianDyadicGrid V).time l k) (u.2 i)) = _
  rw [hc _ (dyadic_time_le_horizon V l k k.isLt.le) i,
    hd _ (dyadic_time_le_horizon V l (k + 1) k.isLt) i,
    hd _ (dyadic_time_le_horizon V l k k.isLt.le) i]

theorem growingReplayDBracket_eq_history_sum_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q) :
    growingReplayDBracket W β hβ δ hδ ranks q V =ᵐ[growingReplayUnlinkedLaw W δ ranks q]
      fun u => ∑ i, historyDBracket W β V
        (replayObservationDHistory W β hβ δ ranks q V hVH u i) := by
  filter_upwards [replayDCoefficient_eq_history_ae W β hβ δ hδ ranks q V hVH] with u hc
  unfold growingReplayDBracket brownianVectorContinuousQuadraticVariation
  apply Finset.sum_congr rfl
  intro i _
  change (∫ s in (0 : ℝ)..(V : ℝ), (brownianVectorContinuousCoefficient W.B
    (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) s.toNNReal u i)^2) = _
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le V.coe_nonneg] at hs
  have hsV : s.toNNReal ≤ V := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal s hs.1]
    exact hs.2
  dsimp only
  rw [hc _ hsV i, Real.coe_toNNReal s hs.1]

end SKConstants.Completion.LM3

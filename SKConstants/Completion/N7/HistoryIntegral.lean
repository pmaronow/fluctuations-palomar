module

public import SKConstants.Completion.N7.HistoryMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N7
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 LM4b
variable {Ω : Type*} [MeasurableSpace Ω]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem replayRowLeftSum_eq_history_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q) (i : Fin (r₀ + q)) (l : ℕ) :
    replayRowLeftSum W β hβ δ hδ r₀ q V i l =ᵐ[growingReplayUnlinkedLaw W δ r₀ q]
      fun u => historyDLeftSum W β V l
        (replayObservationDHistory W β hβ δ r₀ q V hVH u i) := by
  filter_upwards [replayDCoefficient_eq_history_ae W β hβ δ hδ r₀ q V hVH,
    replayDPath_eq_history_ae W β hβ δ r₀ q V hVH] with u hc hd
  simp only [replayRowLeftSum, brownianVectorContinuousCoordinateLeftSum,
    brownianVectorCoordinatePredictableSum, historyDLeftSum,
    predictableGaussianSum_eq_fin_sum, one_mul]
  apply Finset.sum_congr rfl
  intro k _
  change brownianVectorContinuousCoefficient W.B
      (actualParisiGrowingReplayDCoefficient W β hβ δ hδ r₀ q)
      ((brownianDyadicGrid V).time l k) u i *
      (W.B ((brownianDyadicGrid V).time l (k + 1)) (u.2 i) -
        W.B ((brownianDyadicGrid V).time l k) (u.2 i)) = _
  rw [hc _ (dyadic_time_le_horizon V l k k.isLt.le) i,
    hd _ (dyadic_time_le_horizon V l (k + 1) k.isLt) i,
    hd _ (dyadic_time_le_horizon V l k k.isLt.le) i]

theorem historyDIntegral_exists_of_historyLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ r₀ q V hVH)
    (i : Fin (r₀ + q)) :
    ∃ J : ObservationDHistory V → ℝ, Measurable J ∧ IsHistoryDIntegral W β hβ V J := by
  let μ := growingReplayUnlinkedLaw W δ r₀ q
  let ν := unlinkedObservationDHistoryLaw W β hβ V
  let R := fun u => replayObservationDHistory W β hβ δ r₀ q V hVH u i
  let X := historyDLeftSum W β V
  have hR : HasLaw R ν μ := canonical_unlinked_row_hasLaw W β hβ δ hδ r₀ q V hVH hHist i
  have he := replayRowLeftSum_eq_history_ae W β hβ δ hδ r₀ q V hVH i
  have hrep (l : ℕ) : MemLp (replayRowLeftSum W β hβ δ hδ r₀ q V i l) 2 μ :=
    (replayRowLeftSum_hasSubgaussianMGF W β hβ δ hδ r₀ q V i l).memLp 2
  have hmem (l : ℕ) : MemLp (X l) 2 ν := by
    rw [← hR.map_eq]
    apply (memLp_map_measure_iff (measurable_historyDLeftSum W β V l).aestronglyMeasurable
      hR.aemeasurable).mpr
    exact (hrep l).ae_eq (he l)
  let F : ℕ → Lp ℝ 2 ν := fun l => (hmem l).toLp (X l)
  have hcauchy : CauchySeq F := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N, hN⟩ := brownianVectorContinuousCoordinateLeftSum_L2_cauchy
      (parisiGrowingReplaySpinStaticLaw W δ (r₀ + q) q) W.law W.B i
      W.brownian.toIsPreBrownianReal W.measurable
      (fun t u => actualParisiGrowingReplayDCoefficient W β hβ δ hδ r₀ q t u i)
      (fun t => (measurable_pi_apply i).comp (measurable_replayDCoefficient W β hβ δ hδ r₀ q t))
      2 (fun t u => replayDCoefficient_bound W β hβ δ hδ r₀ q t u i)
      (replayDCoefficient_continuous_ae W β hβ δ hδ r₀ q i)
      (brownianDyadicGrid V) 1 (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
      (fun l d j _ => brownianDyadicGrid_left_le V l d j) (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun m hm l hl => ?_⟩
    have hd : dist (F m) (F l) ^ 2 = ∫ h, (X m h - X l h) ^ 2 ∂ν := by
      rw [dist_eq_norm]
      exact norm_toLp_difference_sq_eq_integral (hmem m) (hmem l)
    have htransport : (∫ h, (X m h - X l h) ^ 2 ∂ν) =
        ∫ u, (replayRowLeftSum W β hβ δ hδ r₀ q V i m u -
          replayRowLeftSum W β hβ δ hδ r₀ q V i l u) ^ 2 ∂μ := by
      have ht := hR.integral_comp
        (((measurable_historyDLeftSum W β V m).sub
          (measurable_historyDLeftSum W β V l)).pow_const 2).aestronglyMeasurable
      dsimp only [Function.comp_def, Pi.sub_apply] at ht
      refine ht.symm.trans ?_
      apply integral_congr_ae
      filter_upwards [he m, he l] with u hm hl
      dsimp only [Function.comp_def, X, R]
      rw [← hm, ← hl]
    have hb := hN m hm l hl
    change (∫ u, (replayRowLeftSum W β hβ δ hδ r₀ q V i m u -
      replayRowLeftSum W β hβ δ hδ r₀ q V i l u) ^ 2 ∂μ) < ε ^ 2 at hb
    rw [← htransport, ← hd] at hb
    nlinarith [dist_nonneg (x := F m) (y := F l)]
  obtain ⟨J, hJ⟩ := cauchySeq_tendsto_of_complete hcauchy
  let K := (Lp.memLp J).aestronglyMeasurable.mk (fun h => J h)
  have hJK : (fun h => J h) =ᵐ[ν] K := (Lp.memLp J).aestronglyMeasurable.ae_eq_mk
  refine ⟨K, (Lp.memLp J).aestronglyMeasurable.measurable_mk,
    (Lp.memLp J).ae_eq hJK, ?_, ?_⟩
  · intro l
    exact (((hmem l).sub (Lp.memLp J)).integrable_sq).congr
      (hJK.mono (fun h hh => by
        change J h = K h at hh
        dsimp only [X, Pi.sub_apply]
        rw [hh]))
  · have hn : Tendsto (fun l => ‖F l - J‖ ^ 2) atTop (𝓝 0) := by
      simpa using ((hJ.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => J) atTop (𝓝 J))).norm).pow 2
    convert hn using 1
    funext l
    calc
      _ = ∫ h, (X l h - J h) ^ 2 ∂ν := integral_congr_ae (hJK.mono (fun h hh => by
        change J h = K h at hh
        dsimp only [X, Pi.sub_apply]
        rw [hh]))
      _ = _ := (norm_toLp_sub_sq_eq_integral (hmem l) J).symm

end SKConstants.Completion.N7

module

public import SKConstants.Completion.NDH.FullRows
public import SKConstants.Completion.LM3.RowHistory
public import SKConstants.Completion.LM1b.SourceTrace
public import SKConstants.Completion.LGram.SourceMeasurable

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.NDH
open SKConstantsOAI.ZeroTemperatureSK M1 GaussianProposal LC5 LM3 LGram
variable {Ω : Type*} [MeasurableSpace Ω]

def historyMixedRow (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K : ℕ)
    (u : ScalarDriverHistory (Horizon δ K)) : EuclideanSpace ℝ (Fin (K+(K+1))) :=
  WithLp.toLp 2 (Fin.append
    (fun j : Fin K =>
      (actualParisiFullMagnetization β (growingQueryTime δ (j.val+1))
          (historyPathAt (Horizon δ K) u.2.1 (growingQueryTime δ (j.val+1))) -
       actualParisiFullMagnetization β (growingQueryTime δ j.val)
          (historyPathAt (Horizon δ K) u.2.1 (growingQueryTime δ j.val))) /
        (actualParisiPosteriorIntervalScale W β
          (growingQueryTime δ j.val) (growingQueryTime δ (j.val+1)) : ℝ))
    (Fin.append
      (fun j : Fin K =>
        (historyPathAt (Horizon δ K) u.2.2.1 (growingQueryTime δ (j.val+2)) -
         historyPathAt (Horizon δ K) u.2.2.1 (growingQueryTime δ (j.val+1))) /
            Real.sqrt (growingQueryDuration δ (j.val+1)))
      (fun _ : Fin 1 => scalarHiddenSign u.1)))

theorem measurable_historyMixedRow (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K : ℕ) :
    Measurable (historyMixedRow W β δ K) := by
  have hY (t : ℝ) : Measurable (fun u : ScalarDriverHistory (Horizon δ K) =>
      historyPathAt (Horizon δ K) u.2.1 t) :=
    (ContinuousMap.measurable_eval _).comp measurable_snd.fst
  have hB (t : ℝ) : Measurable (fun u : ScalarDriverHistory (Horizon δ K) =>
      historyPathAt (Horizon δ K) u.2.2.1 t) :=
    (ContinuousMap.measurable_eval _).comp measurable_snd.snd.fst
  have hm (t : ℝ) : Measurable (fun u : ScalarDriverHistory (Horizon δ K) =>
      actualParisiFullMagnetization β t (historyPathAt (Horizon δ K) u.2.1 t)) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp (hY t)
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [Fin.append_left, Pi.sub_apply] using
      ((hm (growingQueryTime δ (j.val+1))).sub (hm (growingQueryTime δ j.val))).div_const
        (actualParisiPosteriorIntervalScale W β (growingQueryTime δ j.val)
          (growingQueryTime δ (j.val+1)) : ℝ)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [Fin.append_right, Fin.append_left, Pi.sub_apply] using
        ((hB (growingQueryTime δ (j.val+2))).sub
          (hB (growingQueryTime δ (j.val+1)))).div_const
            (Real.sqrt (growingQueryDuration δ (j.val+1)))
    · simpa only [Fin.append_right, Function.comp_def] using
        (measurable_of_finite scalarHiddenSign).comp
          (measurable_fst : Measurable (fun u : ScalarDriverHistory (Horizon δ K) => u.1))

theorem paperEndpointTrace_eq_noiseTrace (n K : ℕ) (z : StoppedNoise (Fin n) K) :
    paperEndpointTrace n K z = paperNoiseTrace n K z := by
  induction K with
  | zero => rfl
  | succ K ih =>
    funext e
    exact Fin.cases rfl (fun e => congrFun (ih z.2) e) e

theorem literalSourceRows_eq_historyMixedRows (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) :
    literalSourceRows W β hβ δ r K =
      (fun a i => historyMixedRow W β δ K (a i)) ∘ SourceHistories W β hβ δ r K := by
  funext u i
  apply WithLp.ofLp_injective
  funext c
  refine Fin.addCases (fun j => ?_) (fun j => ?_) c
  · simp only [literalSourceRows, paperRows, historyMixedRow, Function.comp_apply,
      WithLp.ofLp_toLp, Fin.append_left]
    exact targetTraceIdentification_holds W β hβ δ hδ r K u.2 j i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [literalSourceRows, paperRows, historyMixedRow, Function.comp_apply,
        WithLp.ofLp_toLp, Fin.append_right, Fin.append_left,
        paperEndpointTrace_eq_noiseTrace]
      exact endpointTraceIdentification_holds δ hδ r K u.2 j i
    · simp only [literalSourceRows, paperRows, historyMixedRow, Function.comp_apply,
        WithLp.ofLp_toLp, Fin.append_right, SourceHistories]

theorem historyMixedRow_model_ae (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) :
    (historyMixedRow W β δ K ∘ modelFullHistory W W β hβ (Horizon δ K)) =ᵐ[
      actualParisiFullQuerySpinLaw W W β (Horizon δ K)]
      actualParisiFullMixedRow W W β hβ (growingQueryTime δ)
        (fun l => growingQueryTime δ (l+1)) K := by
  let H := Horizon δ K
  have hY := ((actualParisiFullQuerySpinLaw_path_hasLaw W W β H).measurePreserving
    measurable_fst.snd).quasiMeasurePreserving.ae
      (boundedDriftPastPath_version W (actualParisiFullScalarDrift β) H)
  have hB := ((actualParisiFullQuerySpinLaw_drivers_hasLaw W W β H).measurePreserving
    (measurable_fst.snd.prodMk measurable_snd)).quasiMeasurePreserving.ae
      (brownianFinitePath_version (actualParisiQueryBrownianSystem W W β hβ) H)
  filter_upwards [hY,hB] with u huY huB
  have ht (j : ℕ) (hj : j ≤ K+1) : growingQueryTime δ j ≤ H :=
    (growingQueryTime_strictMono δ hδ).monotone hj
  have hYat (j : ℕ) (hj : j ≤ K+1) :
      historyPathAt H (boundedDriftPastPath W (actualParisiFullScalarDrift β) H u.1.2)
        (growingQueryTime δ j) = actualParisiFullScalarProcess W β (growingQueryTime δ j) u.1.2 := by
    rw [historyPathAt, projIcc_of_mem _ ⟨(growingQueryTime δ j).coe_nonneg,
      NNReal.coe_le_coe.mpr (ht j hj)⟩]
    exact huY _
  have hBat (j : ℕ) (hj : j ≤ K+1) :
      historyPathAt H (brownianFinitePath (actualParisiQueryBrownianSystem W W β hβ) H
        (u.1.2,u.2)) (growingQueryTime δ j) =
      (actualParisiQueryBrownianSystem W W β hβ).B (growingQueryTime δ j) (u.1.2,u.2) := by
    rw [historyPathAt, projIcc_of_mem _ ⟨(growingQueryTime δ j).coe_nonneg,
      NNReal.coe_le_coe.mpr (ht j hj)⟩]
    exact huB _
  apply WithLp.ofLp_injective
  funext c
  refine Fin.addCases (fun j => ?_) (fun j => ?_) c
  · simp only [Function.comp_apply, historyMixedRow, modelFullHistory,
      actualParisiFullMixedRow, actualParisiNormalizedPosteriorRow, WithLp.ofLp_toLp,
      Fin.append_left, actualParisiMagnetizationIncrement, actualParisiMagnetizationObservable]
    rw [hYat _ (by omega), hYat _ (by omega)]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Function.comp_apply, historyMixedRow, modelFullHistory,
        actualParisiFullMixedRow, scalarNormalizedBrownianRow, WithLp.ofLp_toLp,
        Fin.append_right, Fin.append_left]
      rw [hBat _ (by omega), hBat _ (by omega)]
      rw [show j.val+1+1 = j.val+2 by omega, growingQueryTime_sub]
    · simp only [Function.comp_apply, historyMixedRow, modelFullHistory,
        actualParisiFullMixedRow, WithLp.ofLp_toLp, Fin.append_right]

theorem sourceMixedRows_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) :
    (SourceLinkedLaw W β hβ δ r K).map (literalSourceRows W β hβ δ r K) =
      mixedVectorRowsLaw W W β hβ (growingQueryTime δ) (fun l => growingQueryTime δ (l+1))
        K (growingQueryTime δ (K+1)) (r+K) := by
  let H := Horizon δ K
  let P : (Fin (r+K) → ScalarDriverHistory H) →
      Fin (r+K) → EuclideanSpace ℝ (Fin (K+(K+1))) :=
    fun a i => historyMixedRow W β δ K (a i)
  have hP : Measurable P := Measurable.of_eval
    (fun i => (measurable_historyMixedRow W β δ K).comp (measurable_pi_apply i))
  have hS : Measurable (SourceHistories W β hβ δ r K) := by
    rw [sourceHistories_eq_driverHistories W β hβ δ r K]
    exact (measurable_DriverHistories W β hβ δ (Size r K) K).comp
      (measurable_id.prodMap (measurable_SourceDrivers δ r K))
  rw [literalSourceRows_eq_historyMixedRows W β hβ δ hδ r K,
    ← Measure.map_map hP hS, literal_linked_source_full_histories_law W β hβ δ hδ r K,
    Measure.pi_map_pi (fun _ => (measurable_historyMixedRow W β δ K).aemeasurable)]
  have hrow : ((actualParisiFullQuerySpinLaw W W β H).map (modelFullHistory W W β hβ H)).map
      (historyMixedRow W β δ K) =
      (actualParisiFullQuerySpinLaw W W β H).map
        (actualParisiFullMixedRow W W β hβ (growingQueryTime δ)
          (fun l => growingQueryTime δ (l+1)) K) := by
    rw [Measure.map_map (measurable_historyMixedRow W β δ K)
      (measurable_modelFullHistory W W β hβ H)]
    exact Measure.map_congr (historyMixedRow_model_ae W β hβ δ hδ K)
  rw [hrow]
  exact (Measure.pi_map_pi (fun _ =>
    (measurable_actualParisiFullMixedRow W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1)) K).aemeasurable)).symm

end SKConstants.Completion.NDH

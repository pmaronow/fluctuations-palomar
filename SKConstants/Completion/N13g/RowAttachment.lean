module

public import SKConstants.Completion.N13g.EnergyEvent
public import SKConstants.Completion.N13g.Psi
public import SKConstants.Completion.LJ.ActualTaylor

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology RealInnerProductSpace

namespace SKConstants.Completion.N13g
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC4a LM3 N13t N13e LM4b LGram LC5 LM5
variable {Ω : Type} [MeasurableSpace Ω]

theorem rowLinearEnergy_eq_taylorRow {k : ℕ} (s b T g : Fin k → ℝ) (x : ℝ) :
    rowLinearEnergy b s T g x (LJ.rowPair s b) = LJ.taylorRow s b T g x := by
  simp only [rowLinearEnergy,LJ.taylorRow,LJ.rowPair,LJ.rowMatrixPair,
    Finset.mul_sum,mul_assoc]

def historyLinearRow (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (q : ℕ) (u : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q)) : ℝ :=
  let s := populationTargetSpin W W β hβ (growingQueryTime δ)
    (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1))
  let b := populationQuerySpin W W β hβ (growingQueryTime δ)
    (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1))
  let z := NDH.historyMixedRow W β δ q u
  rowLinearEnergy (fun j => b j) (fun j => s j)
    (fun j => z (posteriorIndex q j)) (fun j => z (queryIndex q j))
    (scalarHiddenSign u.1) (actualCoarseEnergy W β (growingQueryTime δ) q)

theorem measurable_historyLinearRow
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (q : ℕ) :
    Measurable (historyLinearRow W β hβ δ q) := by
  have hz := NDH.measurable_historyMixedRow W β δ q
  have hc (j : Fin (q+(q+1))) : Measurable (fun u => NDH.historyMixedRow W β δ q u j) :=
    (EuclideanSpace.proj j).continuous.measurable.comp hz
  have hx : Measurable (fun u : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q) =>
      scalarHiddenSign u.1) := (measurable_of_finite scalarHiddenSign).comp measurable_fst
  have hh (i j : Fin q) : Measurable (fun u => halfUpperTruncation
      (fun a b => NDH.historyMixedRow W β δ q u (posteriorIndex q a) *
        NDH.historyMixedRow W β δ q u (posteriorIndex q b)) i j) := by
    unfold halfUpperTruncation
    split_ifs <;> fun_prop
  have ht (i j : Fin q) : Measurable (fun u => fullUpperTruncation
      (fun a b => NDH.historyMixedRow W β δ q u (posteriorIndex q a) *
        NDH.historyMixedRow W β δ q u (queryIndex q b)) i j) := by
    unfold fullUpperTruncation
    split_ifs <;> fun_prop
  unfold historyLinearRow rowLinearEnergy
  dsimp only
  fun_prop

theorem historyLinearRow_model_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ) :
    (historyLinearRow W β hβ δ q ∘ modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q)) =ᵐ[
      actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)]
      LJ.actualTaylorRow W W β hβ (growingQueryTime δ) q := by
  have hs (j : Fin q) := populationTargetSpin_eq_scale W W β hβ (growingQueryTime δ)
    (growingQueryTime_strictMono δ hδ) (fun l => growingQueryTime δ (l+1)) q
    (growingQueryTime δ (q+1)) ((growingQueryTime_strictMono δ hδ).monotone (by omega)) j
  have hb (j : Fin q) : populationQuerySpin W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1)) q (growingQueryTime δ (q+1)) j =
      LJ.gridQueryMean W β (growingQueryTime δ) j := by
    rw [gridQueryMean_eq_coarseSpinMean]
    exact populationQuerySpin_eq_integral W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1))
      ((growingQueryTime_strictMono δ hδ).monotone.comp (fun _ _ h => Nat.add_le_add_right h 1))
      q (growingQueryTime δ (q+1)) le_rfl j
  have he : actualCoarseEnergy W β (growingQueryTime δ) q =
      LJ.rowPair (fun j : Fin q => LJ.gridPosteriorScale W β (growingQueryTime δ) j)
        (fun j => LJ.gridQueryMean W β (growingQueryTime δ) j) := by
    change _ = LJ.gridEnergy W β (growingQueryTime δ) q
    rw [LJ.gridEnergy_growing_eq, N13f.actualCoarseEnergy_eq_growingEnergySum]
  filter_upwards [NDH.historyMixedRow_model_ae W β hβ δ hδ q] with u hu
  change NDH.historyMixedRow W β δ q
      (modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q) u) =
    actualParisiFullMixedRow W W β hβ (growingQueryTime δ)
      (fun l => growingQueryTime δ (l+1)) q u at hu
  dsimp only [Function.comp_apply, historyLinearRow]
  rw [hu]
  simp only [mixedRow_posterior,mixedRow_query]
  simp_rw [hs,hb]
  rw [he]
  simpa only [LJ.gridPosteriorScale,LJ.actualTaylorRow,LJ.gridQuery,modelFullHistory] using
    rowLinearEnergy_eq_taylorRow
      (fun j : Fin q => LJ.gridPosteriorScale W β (growingQueryTime δ) j)
      (fun j : Fin q => LJ.gridQueryMean W β (growingQueryTime δ) j)
      (fun j => actualParisiNormalizedPosteriorRow W β (growingQueryTime δ) q u.1.2 j)
      (fun j => LJ.gridQuery W W β hβ (growingQueryTime δ) q j u) (scalarHiddenSign u.1.1)

theorem historyLinearRow_eq_finite_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ) :
    historyLinearRow W β hβ δ q =ᵐ[fullHistoryLinkedLaw W W β hβ (scalarGrowingSourceHorizon δ q)]
      finiteHistoryRow W β (scalarGrowingSourceHorizon δ q) (growingQueryTime δ) q := by
  have ha := historyLinearRow_model_ae W β hβ δ hδ q
  have hb := LJ.actualTaylorRow_eq_finite W W β hβ (growingQueryTime δ)
    (growingQueryTime_strictMono δ hδ) (by simp [growingQueryTime]) q (scalarGrowingSourceHorizon δ q)
  have hc := (actualRowLinked_absolutelyContinuous W W β (scalarGrowingSourceHorizon δ q)).ae_le
    (finiteHistoryRow_model_ae W W β hβ (scalarGrowingSourceHorizon δ q) (growingQueryTime δ)
      (growingQueryTime_strictMono δ hδ).monotone q le_rfl)
  apply (ae_map_iff (measurable_modelFullHistory W W β hβ _).aemeasurable
    (measurableSet_eq_fun (measurable_historyLinearRow W β hβ δ q)
      (measurable_finiteHistoryRow W β _ _ q))).mpr
  filter_upwards [ha,hb,hc] with u hu hv hw
  exact hu.trans (hv.trans hw.symm)

theorem statisticsEnergy_eq_historyLinearAverage
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r q : ℕ) (hN : 0 < r+q) (z : CoarseStatistics δ r q)
    (hrows : ∀ i, statisticsRows z i = NDH.historyMixedRow W β δ q (z.2.2.2.2 i)) :
    actualCoarseEnergy W β (growingQueryTime δ) q +
      rowEnergyLinearPart W β hβ δ r q (statisticsRows z) =
      (∑ i, historyLinearRow W β hβ δ q (z.2.2.2.2 i))/(r+q : ℕ) := by
  let t := growingQueryTime δ
  let s := populationTargetSpin W W β hβ t (fun l => t (l+1)) q (t (q+1))
  let b := populationQuerySpin W W β hβ t (fun l => t (l+1)) q (t (q+1))
  let H0 := populationCross W W β hβ t (fun l => t (l+1)) q (t (q+1))
  let v := statisticsRows z
  have hH0 : ∀ i j, i ≤ j → H0 i j = 0 :=
    populationCross_shifted_upper W W β hβ t (growingQueryTime_strictMono δ hδ).monotone q _
  have h := empiricalLinearEnergy_eq_rowAverage hN
    (fun i j => v i (posteriorIndex q j)) (fun i j => v i (queryIndex q j))
    (fun i => v i (spinIndex q)) s b H0 hH0
  have he : actualCoarseEnergy W β t q = inner (𝕜 := ℝ) s b :=
    actualCoarseEnergy_eq_population_pairing W W β hβ t (growingQueryTime_strictMono δ hδ) q
  rw [he]
  change inner (𝕜 := ℝ) s b + _ = _
  convert h using 1
  · rfl
  · apply congrArg (fun a : ℝ => a/(r+q : ℕ))
    apply Finset.sum_congr rfl
    intro i _
    have hx : v i (spinIndex q) = scalarHiddenSign (z.2.2.2.2 i).1 := by
      change statisticsRows z i (spinIndex q) = _
      rw [hrows i]
      simp only [NDH.historyMixedRow,spinIndex,WithLp.ofLp_toLp,Fin.append_right]
    dsimp only [historyLinearRow]
    rw [← hrows i, ← hx]
    change rowLinearEnergy (fun j => b j) (fun j => s j)
      (fun j => v i (posteriorIndex q j)) (fun j => v i (queryIndex q j))
      (v i (spinIndex q)) (actualCoarseEnergy W β t q) = _
    rw [he]

theorem rawEnergy_eq_finiteRowAverage_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r q : ℕ) (hN : 0 < r+q) :
    ∀ᵐ u ∂growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q),
      actualCoarseEnergy W β (growingQueryTime δ) q +
        rowEnergyLinearPart W β hβ δ r q (statisticsRows (rawStatistics W β hβ δ r q u)) =
        (∑ i, finiteHistoryRow W β (scalarGrowingSourceHorizon δ q) (growingQueryTime δ) q
          (replayFullHistories W β hβ δ r q u i))/(r+q : ℕ) := by
  let H := scalarGrowingSourceHorizon δ q
  let μ := M1.SourceLinkedLaw W β hβ δ r q
  let ν := growingReplayLinkedLaw W β hβ δ r q H
  let G := fun u : (Fin (r+q) → Bool) × M1.SourceInput δ r q =>
    (u.1,M1.ToReplay W β hβ δ r q u.2)
  have hG : Measurable G :=
    measurable_fst.prodMk ((M1.measurable_ToReplay W β hβ δ r q).comp measurable_snd)
  have hsrcm : Measurable (sourceStatistics W β hβ δ r q) := by
    rw [← replayStatistics_toReplay W β hβ δ r q hN]
    exact (measurable_replayStatistics W β hβ δ r q).comp hG
  have hhistm : Measurable (M1.SourceHistories W β hβ δ r q) := by
    rw [← M1.replayHistories_toReplay W β hβ δ r q hN]
    exact (M1.measurable_ReplayHistories W β hβ δ r q).comp hG
  have hprod : ∀ᵐ a ∂Measure.pi (fun _ : Fin (r+q) => fullHistoryLinkedLaw W W β hβ H),
      ∀ i, historyLinearRow W β hβ δ q (a i) =
        finiteHistoryRow W β H (growingQueryTime δ) q (a i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin (r+q) => fullHistoryLinkedLaw W W β hβ H) i).ae
      (historyLinearRow_eq_finite_ae W β hβ δ hδ q)
  have hsource : ∀ᵐ u ∂μ, ∀ i,
      historyLinearRow W β hβ δ q (M1.SourceHistories W β hβ δ r q u i) =
      finiteHistoryRow W β H (growingQueryTime δ) q (M1.SourceHistories W β hβ δ r q u i) := by
    have hhmap : μ.map (M1.SourceHistories W β hβ δ r q) =
        Measure.pi (fun _ : Fin (r+q) => fullHistoryLinkedLaw W W β hβ H) :=
      NDH.literal_linked_source_full_histories_law W β hβ δ hδ r q
    exact ae_of_ae_map (μ := μ) hhistm.aemeasurable (hhmap.symm ▸ hprod)
  let P : CoarseStatistics δ r q → Prop := fun z =>
    actualCoarseEnergy W β (growingQueryTime δ) q +
      rowEnergyLinearPart W β hβ δ r q (statisticsRows z) =
      (∑ i, finiteHistoryRow W β H (growingQueryTime δ) q (z.2.2.2.2 i))/(r+q : ℕ)
  have hPm : MeasurableSet {z | P z} := by
    exact measurableSet_eq_fun
      (measurable_const.add ((measurable_rowEnergyLinearPart W β hβ δ r q).comp
        (measurable_statisticsRows δ r q)))
      ((Finset.measurable_fun_sum _ fun i _ =>
        (measurable_finiteHistoryRow W β H (growingQueryTime δ) q).comp
          ((measurable_pi_apply i).comp measurable_snd.snd.snd.snd)).div_const _)
  have hPa : ∀ᵐ u ∂μ, P (sourceStatistics W β hβ δ r q u) := by
    filter_upwards [hsource] with u hu
    have hrows (i : Fin (r+q)) : statisticsRows (sourceStatistics W β hβ δ r q u) i =
        NDH.historyMixedRow W β δ q (M1.SourceHistories W β hβ δ r q u i) := by
      rw [sourceStatistics_rows, NDH.literalSourceRows_eq_historyMixedRows W β hβ δ hδ r q]
      rfl
    have he := statisticsEnergy_eq_historyLinearAverage W β hβ δ hδ r q hN
      (sourceStatistics W β hβ δ r q u) hrows
    exact he.trans (congrArg (fun a : ℝ => a/(r+q : ℕ))
      (Finset.sum_congr rfl (fun i _ => hu i)))
  have hd : IdentDistrib (sourceStatistics W β hβ δ r q) (rawStatistics W β hβ δ r q) μ ν :=
    ⟨hsrcm.aemeasurable,(measurable_rawStatistics W β hβ δ r q).aemeasurable,
      source_raw_joint_statistics_law W β hβ δ r q hN⟩
  exact hd.ae_snd hPm hPa

end SKConstants.Completion.N13g

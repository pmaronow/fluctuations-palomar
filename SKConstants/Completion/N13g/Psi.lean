module

public import SKConstants.Completion.N13g.History

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13g
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 LM4 LM4b N13t
variable {Ω : Type} [MeasurableSpace Ω]

theorem gridQueryMean_eq_coarseSpinMean (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (j : ℕ) :
    LJ.gridQueryMean W β t j = actualCoarseSpinMean W β t j := by
  unfold LJ.gridQueryMean LQ.actualParisiQueryIntervalSpinMean
    actualCoarseSpinMean actualQueryCellMean
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  exact mul_comm _ _

theorem actualFiniteRow_eq_coarseZeta (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β) (t : ℕ → ℝ≥0) (k : ℕ) (u : (Bool × Ω) × Ω) :
    LJ.actualFiniteRow W W β hβ t k u =
      actualZeta W W β hβ t (actualCoarseWeight W β t)
        (actualCoarseNoiseWeight W β t) k (actualCoarseEnergy W β t k) u := by
  have he : LJ.gridEnergy W β t k = actualCoarseEnergy W β t k := by
    unfold LJ.gridEnergy actualCoarseEnergy
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [gridQueryMean_eq_coarseSpinMean]
    exact mul_comm _ _
  unfold LJ.actualFiniteRow actualZeta
  rw [he, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  congr 2
  · apply Finset.sum_congr rfl
    intro j _
    rw [gridQueryMean_eq_coarseSpinMean]
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    simp only [LJ.gridPosteriorScale, actualCoarseNoiseWeight, actualCoarseScale,
      LJ.gridQuery, scalarNormalizedBrownianRow, actualRowQueryIncrement,
      actualParisiMagnetizationObservable, actualParisiFullPosteriorMean]
    ring

def replayPsiAverage (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ)
    (I : GrowingReplaySpace Ω δ r q → ℝ) (u : GrowingReplaySpace Ω δ r q) : ℝ :=
  (growingReplayInformation W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I u -
    β * ∑ i, finiteHistoryRow W β (scalarGrowingSourceHorizon δ q) (growingQueryTime δ) q
      (replayFullHistories W β hβ δ r q u i)) / (r+q : ℕ)

theorem replayPsiAverage_tail
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hN : 0 < r+q)
    (hsmall : ∀ j < q, (growingQueryDuration δ (j+1) : ℝ) ≤ 1/8)
    (I : GrowingReplaySpace Ω δ r q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I)
    (η : ℝ) (hη : 0 < η) :
    (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).real
      {u | η ≤ |replayPsiAverage W β hβ δ hδ r q I u -
        (actualParisiEntropyReference W β (scalarGrowingSourceHorizon δ q) -
          β * actualCoarseEnergy W β (growingQueryTime δ) q)|} ≤
      2 * Real.exp (-((r+q : ℕ) : ℝ) * min
        (η^2/(8*(psiMomentConstant β*(1+(scalarGrowingSourceHorizon δ q : ℝ)))^2))
        (η/(4*(psiMomentConstant β*(1+(scalarGrowingSourceHorizon δ q : ℝ)))))) := by
  let V := scalarGrowingSourceHorizon δ q
  have hh := replayFullHistoryLaw W β hβ δ hδ r q hN
  have hHist := hh.observationD W β hβ δ r q
  obtain ⟨J,hJm,hJ⟩ := historyDIntegral_exists_of_fullHistoryLaw W β hβ δ hδ r q hN hh
  let Jm := J ∘ modelObservationDHistory W β hβ V
  have hJmm : Measurable Jm := hJm.comp (measurable_modelObservationDHistory W β hβ V)
  have hJmod := N7.historyDIntegral_model W β hβ V J hJ
  have hid := replayInformation_sub_finiteRow_identDistrib W β hβ δ hδ r q hh J hJm hJ I hI
  let ψ := N13e.coarsePsi W W β hβ δ q Jm
  let ν := actualParisiFullQuerySpinLaw W W β V
  let a := actualParisiEntropyReference W β V - β*actualCoarseEnergy W β (growingQueryTime δ) q
  have hmean : (∫ u, ψ u ∂ν) = a := N13f.coarsePsi_mean W W β hβ δ hδ q Jm hJmod
  have heq (u : (Bool × Ω) × Ω) :
      Blueprint4.rowInformationV W β V Jm u - β*LJ.actualFiniteRow W W β hβ (growingQueryTime δ) q u =
        ψ u := by
    rw [actualFiniteRow_eq_coarseZeta]
    rfl
  have hbound := N13f.coarsePsi_iid_abs_of_historyLaw W β hβ δ hδ r q ⟨0,hN⟩
    hHist Jm hJmm hJmod hsmall hN hη
  have hmeas : MeasurableSet {v : ℝ | η ≤ |v-a|} :=
    measurableSet_le measurable_const ((measurable_id.sub_const a).abs)
  have he := congrArg ENNReal.toReal (hid.measure_mem_eq hmeas)
  change _ = (Measure.pi fun _ : Fin (r+q) => ν).real {ω | η ≤
    |(∑ i, (Blueprint4.rowInformationV W β V Jm (ω i) -
      β*LJ.actualFiniteRow W W β hβ (growingQueryTime δ) q (ω i)))/(r+q : ℕ)-a|} at he
  simp_rw [heq] at he
  have hNr : (0 : ℝ) < (r+q : ℕ) := Nat.cast_pos.mpr hN
  have hset : {ω : Fin (r+q) → (Bool × Ω) × Ω | η ≤ |(∑ i, ψ (ω i))/(r+q : ℕ)-a|} =
      {ω | ((r+q : ℕ) : ℝ)*η ≤ |∑ i, Concentration.centeredObservable ν ψ (ω i)|} := by
    ext ω
    have halg : (∑ i, ψ (ω i))/(r+q : ℕ)-a =
        (∑ i, Concentration.centeredObservable ν ψ (ω i))/(r+q : ℕ) := by
      simp only [Concentration.centeredObservable, hmean, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    simp only [mem_setOf_eq, halg, abs_div, abs_of_pos hNr]
    rw [le_div_iff₀ hNr, mul_comm η]
  change _ = (Measure.pi fun _ : Fin (r+q) => ν).real _ at he
  rw [hset] at he
  exact he.trans_le hbound

end SKConstants.Completion.N13g

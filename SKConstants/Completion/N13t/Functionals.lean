module

public import SKConstants.Completion.N13t.History
public import SKConstants.Completion.N13t.L2Transport
public import SKConstants.Completion.Blueprint4.SharpEngine

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13t
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 Blueprint4

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def historyMean (β : ℝ) (V : ℝ≥0) (t : ℝ≥0) (u : M1.ScalarDriverHistory V) : ℝ :=
  actualParisiFullMagnetization β t (historyPathAt V u.2.1 t)

def historyPotential (β : ℝ) (V : ℝ≥0) (t : ℝ≥0) (u : M1.ScalarDriverHistory V) : ℝ :=
  LJ.rowPotential (scalarHiddenSign u.1) (historyMean β V t u)

def historyQuery (V : ℝ≥0) (t : ℕ → ℝ≥0) (j : ℕ)
    (u : M1.ScalarDriverHistory V) : ℝ :=
  (historyPathAt V u.2.2.1 (t (j + 2)) - historyPathAt V u.2.2.1 (t (j + 1))) /
    Real.sqrt ((t (j + 2) : ℝ) - t (j + 1))

def finiteHistoryRow (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0)
    (t : ℕ → ℝ≥0) (K : ℕ) (u : M1.ScalarDriverHistory V) : ℝ :=
  (∑ j : Fin K, (LJ.gridQueryMean W β t j / LJ.gridPosteriorScale W β t j) *
    (historyPotential β V (t (j + 1)) u - historyPotential β V (t j) u)) +
  (∑ j : Fin K, LJ.gridPosteriorScale W β t j *
    ((scalarHiddenSign u.1 - historyMean β V (t (j + 1)) u) * historyQuery V t j u)) -
    LJ.gridEnergy W β t K / 2

def jointHistoryLeftSum (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0)
    (l : ℕ) (u : M1.ScalarDriverHistory V) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    (β * actualParisiFullSusceptibilityExpected W β ((brownianDyadicGrid V).time l k) *
      (historyPotential β V ((brownianDyadicGrid V).time l (k + 1)) u -
        historyPotential β V ((brownianDyadicGrid V).time l k) u) +
    Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β
        ((brownianDyadicGrid V).time l k)) *
      (scalarHiddenSign u.1 - historyMean β V ((brownianDyadicGrid V).time l k) u) *
      (historyPathAt V u.2.2.1 ((brownianDyadicGrid V).time l (k + 1)) -
        historyPathAt V u.2.2.1 ((brownianDyadicGrid V).time l k)))

def fullHistoryDLeftSum (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) :
    M1.ScalarDriverHistory V → ℝ :=
  historyDLeftSum W β V l ∘ observationDProjection V

def fullHistoryDBracket (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) :
    M1.ScalarDriverHistory V → ℝ :=
  historyDBracket W β V ∘ observationDProjection V

def fullHistoryInformation (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0)
    (J : M1.ScalarDriverHistory V → ℝ) (u : M1.ScalarDriverHistory V) : ℝ :=
  Real.log (historyLinkDensity β V (observationDProjection V u)) - J u +
    fullHistoryDBracket W β V u / 2

theorem measurable_historyMean (β : ℝ) (V : ℝ≥0) (t : ℝ≥0) :
    Measurable (historyMean β V t) := by
  have he : Measurable (fun p : ScalarContinuousPath V =>
      p (projIcc 0 (V : ℝ) V.coe_nonneg (t : ℝ))) := ContinuousMap.measurable_eval _
  have hy : Measurable (fun u : M1.ScalarDriverHistory V => historyPathAt V u.2.1 t) :=
    he.comp (measurable_snd.fst : Measurable (fun u : M1.ScalarDriverHistory V => u.2.1))
  have hm : Measurable (fun y : ℝ => actualParisiFullMagnetization β (t : ℝ) y) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  exact hm.comp hy

theorem measurable_historyPotential (β : ℝ) (V : ℝ≥0) (t : ℝ≥0) :
    Measurable (historyPotential β V t) := by
  unfold historyPotential LJ.rowPotential
  exact (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul
    (measurable_historyMean β V t)).sub ((measurable_historyMean β V t).pow_const 2 |>.div_const 2)

theorem measurable_historyQuery (V : ℝ≥0) (t : ℕ → ℝ≥0) (j : ℕ) :
    Measurable (historyQuery V t j) :=
  (((ContinuousMap.measurable_eval _).comp measurable_snd.snd.fst).sub
    ((ContinuousMap.measurable_eval _).comp measurable_snd.snd.fst)).div_const _

theorem measurable_finiteHistoryRow (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0)
    (t : ℕ → ℝ≥0) (K : ℕ) : Measurable (finiteHistoryRow W β V t K) := by
  unfold finiteHistoryRow
  refine ((Finset.measurable_fun_sum _ fun j _ => ?_).add
    (Finset.measurable_fun_sum _ fun j _ => ?_)).sub measurable_const
  · exact ((measurable_historyPotential β V _).sub (measurable_historyPotential β V _)).const_mul _
  · exact ((((measurable_of_finite scalarHiddenSign).comp measurable_fst).sub
      (measurable_historyMean β V _)).mul (measurable_historyQuery V t j)).const_mul _

theorem measurable_jointHistoryLeftSum (W : BrownianSystem Ω) (β : ℝ)
    (V : ℝ≥0) (l : ℕ) : Measurable (jointHistoryLeftSum W β V l) := by
  apply Finset.measurable_fun_sum
  intro k _
  exact (((measurable_historyPotential β V _).sub (measurable_historyPotential β V _)).const_mul _).add
    (((((measurable_of_finite scalarHiddenSign).comp measurable_fst).sub
      (measurable_historyMean β V _)).const_mul _).mul
        (((ContinuousMap.measurable_eval _).comp measurable_snd.snd.fst).sub
          ((ContinuousMap.measurable_eval _).comp measurable_snd.snd.fst)))

theorem measurable_fullHistoryDLeftSum (W : BrownianSystem Ω) (β : ℝ)
    (V : ℝ≥0) (l : ℕ) : Measurable (fullHistoryDLeftSum W β V l) :=
  (measurable_historyDLeftSum W β V l).comp (measurable_observationDProjection V)

theorem modelFullHistory_paths (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z, ∀ s : ℝ≥0, s ≤ V →
      historyPathAt V (modelFullHistory W Z β hβ V u).2.1 s =
        actualParisiFullScalarProcess W β s u.1.2 ∧
      historyPathAt V (modelFullHistory W Z β hβ V u).2.2.1 s =
        (actualParisiQueryBrownianSystem W Z β hβ).B s (u.1.2, u.2) ∧
      historyPathAt V (modelFullHistory W Z β hβ V u).2.2.2 s =
        (actualParisiAuxBrownianSystem W Z β hβ).B s (u.1.2, u.2) := by
  filter_upwards [modelFullHistory_version W Z β hβ V] with u hu
  intro s hs
  dsimp only [historyPathAt]
  rw [projIcc_of_mem _ ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩]
  exact hu ⟨s, s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩

theorem fullHistoryDLeftSum_model_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    (fun u => fullHistoryDLeftSum W β V l (modelFullHistory W Z β hβ V u))
      =ᵐ[LM4.actualRowBaseLaw W Z] LM4b.actualRowDLeftSum W Z β hβ V l := by
  filter_upwards [modelFullHistory_paths W Z β hβ V] with u hu
  simp only [fullHistoryDLeftSum, Function.comp_apply, historyDLeftSum,
    predictableGaussianSum_eq_fin_sum, LM4b.actualRowDLeftSum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [historyDCoefficient, observationDProjection, LM4b.actualRowDCoefficient]
  rw [(hu _ (dyadic_time_le_horizon V l k k.isLt.le)).1,
    (hu _ (dyadic_time_le_horizon V l (k + 1) k.isLt)).2.2,
    (hu _ (dyadic_time_le_horizon V l k k.isLt.le)).2.2]
  rfl

theorem fullHistoryDBracket_model_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (fun u => fullHistoryDBracket W β V (modelFullHistory W Z β hβ V u))
      =ᵐ[LM4.actualRowBaseLaw W Z] LM4b.actualRowDBracket W β V := by
  filter_upwards [modelFullHistory_paths W Z β hβ V] with u hu
  simp only [fullHistoryDBracket, Function.comp_apply, historyDBracket, LM4b.actualRowDBracket]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le V.coe_nonneg] at ht
  have htV : t.toNNReal ≤ V := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal t ht.1]
    exact ht.2
  dsimp only [historyDCoefficient, observationDProjection, LM4b.actualRowDCoefficient]
  rw [← Real.coe_toNNReal t ht.1, (hu _ htV).1]
  simp only [Real.toNNReal_coe]
  rfl

theorem jointHistoryLeftSum_model_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    (fun u => jointHistoryLeftSum W β V l (modelFullHistory W Z β hβ V u))
      =ᵐ[LM4.actualRowBaseLaw W Z] jointRowLeftSum W Z β hβ V l := by
  filter_upwards [modelFullHistory_paths W Z β hβ V] with u hu
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  dsimp only [jointHistoryLeftSum, jointRowLeftSum, historyPotential, historyMean,
    LJ.actualRowPotential, actualParisiFullPosteriorMean]
  rw [(hu _ (dyadic_time_le_horizon V l (k + 1) hk')).1,
    (hu _ (dyadic_time_le_horizon V l k hk'.le)).1,
    (hu _ (dyadic_time_le_horizon V l (k + 1) hk')).2.1,
    (hu _ (dyadic_time_le_horizon V l k hk'.le)).2.1]
  rfl

theorem finiteHistoryRow_model_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (K : ℕ) (hKV : t (K + 1) ≤ V) :
    (fun u => finiteHistoryRow W β V t K (modelFullHistory W Z β hβ V u))
      =ᵐ[LM4.actualRowBaseLaw W Z] LJ.actualFiniteRow W Z β hβ t K := by
  filter_upwards [modelFullHistory_paths W Z β hβ V] with u hu
  have htime (j : ℕ) (hj : j ≤ K + 1) : t j ≤ V := (ht hj).trans hKV
  have hm (j : ℕ) (hj : j ≤ K + 1) :
      historyMean β V (t j) (modelFullHistory W Z β hβ V u) =
        actualParisiFullPosteriorMean W β (t j) u.1.2 := by
    dsimp only [historyMean, actualParisiFullPosteriorMean]
    rw [(hu _ (htime j hj)).1]
  have hp (j : ℕ) (hj : j ≤ K + 1) :
      historyPotential β V (t j) (modelFullHistory W Z β hβ V u) =
        LJ.actualRowPotential W β (t j) u.1 := by
    dsimp only [historyPotential, LJ.actualRowPotential]
    rw [hm j hj]
    rfl
  unfold finiteHistoryRow LJ.actualFiniteRow
  congr 2
  · apply Finset.sum_congr rfl
    intro j _
    rw [hp (j + 1) (by omega), hp j (by omega)]
  · apply Finset.sum_congr rfl
    intro j _
    dsimp only [historyQuery, LJ.gridQuery, scalarNormalizedBrownianRow]
    rw [hm (j + 1) (by omega), (hu _ (htime (j + 2) (by omega))).2.1,
      (hu _ (htime (j + 1) (by omega))).2.1]
    rfl

end SKConstants.Completion.N13t

module

public import SKConstants.Completion.S33aA.DriverRotation
public import SKConstants.Completion.SJ3.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S33aA
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def originalRowLeftSum (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ)
    (u : (Bool × Ω) × A) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β
      ((brownianDyadicGrid V).time l k) u.1.2) *
    (W.B ((brownianDyadicGrid V).time l (k + 1)) u.1.2 -
      W.B ((brownianDyadicGrid V).time l k) u.1.2)

def actualRotationLeftSumError (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  β * SJ3.queryRowLeftSum W Z β hβ V l u + LM4b.actualRowDLeftSum W Z β hβ V l u -
    originalRowLeftSum W β V l u

theorem rotatedQuery_actual (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℝ≥0) (u : Ω × A) :
    rotatedQuery (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (fun s => W.driver s.toNNReal u.1) (fun s => Z.driver s.toNNReal u.2) t =
      (actualParisiQueryBrownianSystem W Z β hβ).B t u := by
  simp only [rotatedQuery, bvTransform, Real.toNNReal_coe]
  rfl

theorem rotatedAux_actual (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℝ≥0) (u : Ω × A) :
    rotatedAux (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (fun s => W.driver s.toNNReal u.1) (fun s => Z.driver s.toNNReal u.2) t =
      (actualParisiAuxBrownianSystem W Z β hβ).B t u := by
  simp only [rotatedAux, bvTransform, Real.toNNReal_coe]
  rfl

theorem actualRotationLeftSumError_eq (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) (u : (Bool × Ω) × A)
    (hdriver : ∀ t, W.driver t u.1.2 = W.B t u.1.2) :
    actualRotationLeftSumError W Z β hβ V l u =
      rotationLeftSumError
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (fun s => W.driver s.toNNReal u.1.2) (fun s => Z.driver s.toNNReal u.2)
        (fun k => scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β
          ((brownianDyadicGrid V).time l k) u.1.2)
        (fun k => ((brownianDyadicGrid V).time l k : ℝ)) (2 ^ l) := by
  simp only [actualRotationLeftSumError, SJ3.queryRowLeftSum, LM4b.actualRowDLeftSum,
    originalRowLeftSum, rotationLeftSumError, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [rotatedQuery_actual W Z β hβ ((brownianDyadicGrid V).time l (k + 1)) (u.1.2, u.2),
    rotatedQuery_actual W Z β hβ ((brownianDyadicGrid V).time l k) (u.1.2, u.2),
    rotatedAux_actual W Z β hβ ((brownianDyadicGrid V).time l (k + 1)) (u.1.2, u.2),
    rotatedAux_actual W Z β hβ ((brownianDyadicGrid V).time l k) (u.1.2, u.2),
    Real.toNNReal_coe, Real.toNNReal_coe, hdriver, hdriver,
    LM4b.actualRowDCoefficient_eq_defect W β hβ]
  have hr := LQ.actual_rho_eq W β hβ ((brownianDyadicGrid V).time l k)
    ((brownianDyadicGrid V).time l k).coe_nonneg
  change _ = (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β
      ((brownianDyadicGrid V).time l k) u.1.2) *
    (-(-actualParisiQueryRho W β ((brownianDyadicGrid V).time l k)) * _ +
      actualParisiQuerySigma W β ((brownianDyadicGrid V).time l k) * _ - _)
  rw [hr, show actualParisiMagnetizationObservable W β ((brownianDyadicGrid V).time l k) u.1.2 =
    actualParisiFullPosteriorMean W β ((brownianDyadicGrid V).time l k) u.1.2 from rfl]
  ring

theorem actualRotationLeftSumError_tendsto_of_continuous
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (u : (Bool × Ω) × A)
    (hW : Continuous (fun s : ℝ => W.driver s.toNNReal u.1.2))
    (hZ : Continuous (fun s : ℝ => Z.driver s.toNNReal u.2))
    (hdriver : ∀ t, W.driver t u.1.2 = W.B t u.1.2) :
    Tendsto (fun l => actualRotationLeftSumError W Z β hβ V l u) atTop (𝓝 0) := by
  have hend (l : ℕ) : (brownianDyadicGrid V).time l (2 ^ l) = V := by
    simp [brownianDyadicGrid]
  simp_rw [actualRotationLeftSumError_eq W Z β hβ V _ u hdriver]
  apply rotationLeftSumError_tendsto _ _ _ _ hW hZ 0 V V.coe_nonneg
    (fun l k => ((brownianDyadicGrid V).time l k : ℝ)) (fun l => 2 ^ l)
    (brownianDyadicWidth V) _ 2 (by norm_num)
    (fun l => by simp [brownianDyadicGrid]) (fun l => by rw [hend l])
    (fun l k hk => ⟨((brownianDyadicGrid V).time l k).coe_nonneg,
      NNReal.coe_le_coe.mpr (((brownianDyadicGrid V).monotone l hk).trans_eq (hend l))⟩)
    (fun l k _ => NNReal.coe_le_coe.mpr ((brownianDyadicGrid V).monotone l (Nat.le_succ k)))
    (fun l k _ => brownianDyadicGrid_width_le V l k) (brownianDyadicWidth_tendsto V)
  · intro l k _
    have hm := actualParisiMagnetizationObservable_abs_le W β ((brownianDyadicGrid V).time l k) u.1.2
    change |actualParisiFullPosteriorMean W β ((brownianDyadicGrid V).time l k) u.1.2| ≤ 1 at hm
    have hx : |scalarHiddenSign u.1.1| = 1 := by cases u.1.1 <;> norm_num [scalarHiddenSign]
    exact (abs_sub _ _).trans (by rw [hx]; linarith)
  · intro t _
    exact actualParisiStieltjesCoefficients_unit W β hβ t
  · intro t _
    change |-actualParisiQueryRho W β t| ≤ 1
    rw [abs_neg, abs_of_nonneg (actualParisiQueryRho_bounds W β hβ t).1]
    exact (actualParisiQueryRho_bounds W β hβ t).2
  · intro t _
    change |actualParisiQuerySigma W β t| ≤ 1
    rw [abs_of_nonneg (actualParisiQuerySigma_bounds W β hβ t).1]
    exact (actualParisiQuerySigma_bounds W β hβ t).2

theorem actualRotationLeftSumError_tendsto_ae
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
      Tendsto (fun l => actualRotationLeftSumError W Z β hβ V l u) atTop (𝓝 0) := by
  let := W.isProbability
  let := Z.isProbability
  have hpW : MeasurePreserving (fun u : (Bool × Ω) × A => u.1.2)
      (LM4.actualRowBaseLaw W Z) W.law :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
      (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law))
  have hpZ : MeasurePreserving (fun u : (Bool × Ω) × A => u.2)
      (LM4.actualRowBaseLaw W Z) Z.law :=
    measurePreserving_snd (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law)
  filter_upwards [hpW.quasiMeasurePreserving.ae W.driver_continuous,
    hpZ.quasiMeasurePreserving.ae Z.driver_continuous,
    hpW.quasiMeasurePreserving.ae W.driver_indistinguishable] with u hW hZ hd
  exact actualRotationLeftSumError_tendsto_of_continuous W Z β hβ V u
    (hW.comp continuous_real_toNNReal) (hZ.comp continuous_real_toNNReal) hd

end SKConstants.Completion.S33aA

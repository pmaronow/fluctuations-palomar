module

public import SKConstants.Completion.LM4b.ActualZetaMean
public import SKConstants.Completion.LM4b.ActualRowReference
public import SKConstants.Completion.LM3.RowScalarReduction

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N7
open SKConstantsOAI.ZeroTemperatureSK LC1 LM4b
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

theorem actualPastMagnetization_aux_moment_zero
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ u : Ω × A, actualParisiMagnetizationObservable W β S u.1 *
      ((actualParisiAuxBrownianSystem W Z β hβ).B T u -
        (actualParisiAuxBrownianSystem W Z β hβ).B S u) ∂W.law.prod Z.law) = 0 := by
  let f := actualParisiSigmaStieltjes W β hβ
  let g := actualParisiNegativeRhoStieltjes W β hβ
  let M := actualParisiMagnetizationObservable W β S
  let X : Ω → ℝ := fun w => scalarGlobalStieltjesWeightedProcess f W.driver T w -
    scalarGlobalStieltjesWeightedProcess f W.driver S w
  let Y : A → ℝ := fun z => scalarGlobalStieltjesWeightedProcess g Z.driver T z -
    scalarGlobalStieltjesWeightedProcess g Z.driver S z
  have hiX := (bounded_brownian_stieltjes_integrable W f S T hST M
    (measurable_actualParisiMagnetizationObservable W β S) 1
    (actualParisiMagnetizationObservable_abs_le W β S)).2
  have hiY : Integrable Y Z.law := by
    simpa only [one_mul] using (bounded_brownian_stieltjes_integrable Z g S T hST
      (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num)).2
  have he (u : Ω × A) : M u.1 *
      ((actualParisiAuxBrownianSystem W Z β hβ).B T u -
        (actualParisiAuxBrownianSystem W Z β hβ).B S u) =
      M u.1 * X u.1 + M u.1 * Y u.2 := by
    change M u.1 * ((_ + _) - (_ + _)) = _
    dsimp only [X, Y]
    ring
  change (∫ u : Ω × A, M u.1 *
    ((actualParisiAuxBrownianSystem W Z β hβ).B T u -
      (actualParisiAuxBrownianSystem W Z β hβ).B S u) ∂W.law.prod Z.law) = 0
  simp_rw [he]
  rw [integral_add (hiX.comp_fst Z.law)
    ((integrable_actualParisiMagnetizationObservable W β S).mul_prod hiY),
    integral_fun_fst (μ := W.law) (ν := Z.law) (fun w => M w * X w),
    probReal_univ, one_smul,
    actualPastMagnetization_stieltjes_moment_zero W β f S T hST,
    integral_prod_mul, brownianStieltjes_increment_mean_zero Z g S T hST,
    mul_zero, add_zero]

theorem integrable_actual_aux_defect
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T H : ℝ≥0) :
    Integrable (fun u : (Bool × Ω) × A =>
      (scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β S u.1.2) *
      ((actualParisiAuxBrownianSystem W Z β hβ).B T (u.1.2, u.2) -
        (actualParisiAuxBrownianSystem W Z β hβ).B S (u.1.2, u.2)))
      (actualParisiFullQuerySpinLaw W Z β H) := by
  have hI := (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integrable_comp
    (((actualParisiAuxBrownianSystem W Z β hβ).brownian.integrable_eval T).sub
      ((actualParisiAuxBrownianSystem W Z β hβ).brownian.integrable_eval S))
  apply hI.bdd_mul (c := 2)
    ((((measurable_of_finite scalarHiddenSign).comp measurable_fst.fst).sub
      ((measurable_actualParisiMagnetizationObservable W β S).comp
        measurable_fst.snd)).aestronglyMeasurable)
  apply ae_of_all
  intro u
  change ‖scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β S u.1.2‖ ≤ 2
  rw [Real.norm_eq_abs]
  have hs : |scalarHiddenSign u.1.1| = 1 := by
    cases u.1.1 <;> norm_num [scalarHiddenSign]
  exact (abs_sub _ _).trans (by
    rw [hs]
    linarith [actualParisiMagnetizationObservable_abs_le W β S u.1.2])

theorem actual_aux_defect_mean
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ u : (Bool × Ω) × A,
      (scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β S u.1.2) *
      ((actualParisiAuxBrownianSystem W Z β hβ).B T (u.1.2, u.2) -
        (actualParisiAuxBrownianSystem W Z β hβ).B S (u.1.2, u.2))
      ∂actualParisiFullQuerySpinLaw W Z β H) =
      ∫ r in (S : ℝ)..(T : ℝ), actualParisiQuerySigma W β r *
        actualParisiFullSusceptibilityExpected W β r := by
  let D := actualParisiAuxBrownianSystem W Z β hβ
  let F : Ω × A → ℝ := fun u => D.B T u - D.B S u
  have hF : Measurable F := (D.measurable T).sub (D.measurable S)
  have hFi : Integrable F (W.law.prod Z.law) :=
    (D.brownian.integrable_eval T).sub (D.brownian.integrable_eval S)
  have hIi := (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integrable_comp hFi
  have hI1 : Integrable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1 * F (u.1.2, u.2))
      (actualParisiFullQuerySpinLaw W Z β H) :=
    hIi.bdd_mul (c := 1)
      (((measurable_of_finite scalarHiddenSign).comp measurable_fst.fst).aestronglyMeasurable)
      (ae_of_all _ (fun u => by cases u.1.1 <;> norm_num [scalarHiddenSign]))
  have hI2 : Integrable (fun u : (Bool × Ω) × A =>
      actualParisiMagnetizationObservable W β S u.1.2 * F (u.1.2, u.2))
      (actualParisiFullQuerySpinLaw W Z β H) :=
    hIi.bdd_mul (c := 1)
      (((measurable_actualParisiMagnetizationObservable W β S).comp
        measurable_fst.snd).aestronglyMeasurable)
      (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs]
        exact actualParisiMagnetizationObservable_abs_le W β S u.1.2))
  change (∫ u : (Bool × Ω) × A,
    (scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β S u.1.2) *
      F (u.1.2, u.2) ∂actualParisiFullQuerySpinLaw W Z β H) = _
  simp only [sub_mul]
  rw [integral_sub hI1 hI2,
    actualQuerySpinLaw_sign_test_integrable W Z β H F hF hFi]
  have hz : (∫ u : (Bool × Ω) × A,
      actualParisiMagnetizationObservable W β S u.1.2 * F (u.1.2, u.2)
      ∂actualParisiFullQuerySpinLaw W Z β H) = 0 :=
    ((actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integral_comp
      (((measurable_actualParisiMagnetizationObservable W β S).comp
        measurable_fst).mul hF).aestronglyMeasurable).trans
      (actualPastMagnetization_aux_moment_zero W Z β hβ S T hST)
  rw [hz, sub_zero]
  exact actualFullProcess_aux_brownian_cross_moment W Z β hβ S T H hST hTH

theorem actualRowDLeftSum_mean
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (l : ℕ) :
    (∫ u, actualRowDLeftSum W Z β hβ V l u ∂actualParisiFullQuerySpinLaw W Z β V) =
      ∑ k ∈ Finset.range (2 ^ l), actualParisiQuerySigma W β ((brownianDyadicGrid V).time l k) *
        (∫ r in ((brownianDyadicGrid V).time l k : ℝ)..((brownianDyadicGrid V).time l (k + 1) : ℝ),
          actualParisiQuerySigma W β r * actualParisiFullSusceptibilityExpected W β r) := by
  unfold actualRowDLeftSum
  simp_rw [actualRowDCoefficient_eq_defect W β hβ, mul_assoc]
  rw [integral_finsetSum _ (fun k _ =>
    (integrable_actual_aux_defect W Z β hβ _ _ V).const_mul _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, actual_aux_defect_mean W Z β hβ _ _ V
    ((brownianDyadicGrid V).monotone l (Nat.le_succ k))
    (LM3.dyadic_time_le_horizon V l (k + 1) (Finset.mem_range.mp hk))]

end SKConstants.Completion.N7

module

public import SKConstants.Completion.LC1.StieltjesCrossMoment
public import SKConstants.Completion.LC1.PopulationSpin

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualFullProcess_two_driver_stieltjes_moment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (c d : ℝ)
    (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ u : Ω × A, actualParisiMagnetizationObservable W β H u.1 *
      (c * (scalarGlobalStieltjesWeightedProcess f W.driver T u.1 -
          scalarGlobalStieltjesWeightedProcess f W.driver S u.1) +
       d * (scalarGlobalStieltjesWeightedProcess g Z.driver T u.2 -
          scalarGlobalStieltjesWeightedProcess g Z.driver S u.2)) ∂W.law.prod Z.law) =
    c * (∫ r in (S:ℝ)..(T:ℝ), f r * actualParisiFullSusceptibilityExpected W β r) := by
  let := W.isProbability
  let := Z.isProbability
  let M := actualParisiMagnetizationObservable W β H
  let X : Ω → ℝ := fun w => scalarGlobalStieltjesWeightedProcess f W.driver T w -
    scalarGlobalStieltjesWeightedProcess f W.driver S w
  let Y : A → ℝ := fun z => scalarGlobalStieltjesWeightedProcess g Z.driver T z -
    scalarGlobalStieltjesWeightedProcess g Z.driver S z
  have hM := measurable_actualParisiMagnetizationObservable W β H
  have hiM : Integrable M W.law := Integrable.of_bound hM.aestronglyMeasurable 1
    (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact actualParisiMagnetizationObservable_abs_le W β H w))
  have hiX : Integrable (fun w => M w * X w) W.law :=
    (bounded_brownian_stieltjes_integrable W f S T hST M hM 1
      (actualParisiMagnetizationObservable_abs_le W β H)).2
  have hiY : Integrable Y Z.law := by
    simpa only [one_mul] using
      (bounded_brownian_stieltjes_integrable Z g S T hST (fun _ => (1:ℝ)) measurable_const 1 (fun _ => by norm_num)).2
  have hYzero : (∫ z, Y z ∂Z.law) = 0 := brownianStieltjes_increment_mean_zero Z g S T hST
  have he (u : Ω × A) : M u.1 * (c*X u.1+d*Y u.2) =
      c*(M u.1*X u.1)+d*(M u.1*Y u.2) := by ring
  change (∫ u : Ω × A, M u.1 * (c*X u.1+d*Y u.2) ∂W.law.prod Z.law) = _
  simp_rw [he]
  rw [integral_add ((hiX.comp_fst Z.law).const_mul c) ((hiM.mul_prod hiY).const_mul d),
    integral_const_mul, integral_const_mul,
    integral_fun_fst (μ:=W.law) (ν:=Z.law) (fun w => M w * X w), probReal_univ, one_smul,
    integral_prod_mul M Y, hYzero,
    mul_zero, mul_zero, add_zero]
  exact congrArg (fun x : ℝ => c*x) (actualFullProcess_stieltjes_cross_moment W β hβ f hf S T H hST hTH)

theorem actualFullProcess_query_brownian_cross_moment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ u : Ω × A, actualParisiMagnetizationObservable W β H u.1 *
      ((actualParisiQueryBrownianSystem W Z β hβ).B T u -
        (actualParisiQueryBrownianSystem W Z β hβ).B S u) ∂W.law.prod Z.law) =
    ∫ r in (S:ℝ)..(T:ℝ), actualParisiQueryRho W β r * actualParisiFullSusceptibilityExpected W β r := by
  let f := actualParisiNegativeRhoStieltjes W β hβ
  let g := actualParisiSigmaStieltjes W β hβ
  have hh := actualFullProcess_two_driver_stieltjes_moment W Z β hβ f g
    (continuous_actualParisiNegativeRhoStieltjes W β hβ) (-1) 1 S T H hST hTH
  have he (u : Ω × A) : (actualParisiQueryBrownianSystem W Z β hβ).B T u -
      (actualParisiQueryBrownianSystem W Z β hβ).B S u =
      -1 * (scalarGlobalStieltjesWeightedProcess f W.driver T u.1 -
        scalarGlobalStieltjesWeightedProcess f W.driver S u.1) +
      1 * (scalarGlobalStieltjesWeightedProcess g Z.driver T u.2 -
        scalarGlobalStieltjesWeightedProcess g Z.driver S u.2) := by
    change (-scalarGlobalStieltjesWeightedProcess f W.driver T u.1 +
      scalarGlobalStieltjesWeightedProcess g Z.driver T u.2) -
      (-scalarGlobalStieltjesWeightedProcess f W.driver S u.1 +
        scalarGlobalStieltjesWeightedProcess g Z.driver S u.2) = _
    ring
  simp_rw [he]
  rw [hh, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  change -1 * (-actualParisiQueryRho W β r * actualParisiFullSusceptibilityExpected W β r) = _
  ring

theorem actualFullProcess_aux_brownian_cross_moment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ u : Ω × A, actualParisiMagnetizationObservable W β H u.1 *
      ((actualParisiAuxBrownianSystem W Z β hβ).B T u -
        (actualParisiAuxBrownianSystem W Z β hβ).B S u) ∂W.law.prod Z.law) =
    ∫ r in (S:ℝ)..(T:ℝ), actualParisiQuerySigma W β r * actualParisiFullSusceptibilityExpected W β r := by
  let f := actualParisiSigmaStieltjes W β hβ
  let g := actualParisiNegativeRhoStieltjes W β hβ
  have hh := actualFullProcess_two_driver_stieltjes_moment W Z β hβ f g
    (continuous_actualParisiSigmaStieltjes W β hβ) 1 1 S T H hST hTH
  have he (u : Ω × A) : (actualParisiAuxBrownianSystem W Z β hβ).B T u -
      (actualParisiAuxBrownianSystem W Z β hβ).B S u =
      1 * (scalarGlobalStieltjesWeightedProcess f W.driver T u.1 -
        scalarGlobalStieltjesWeightedProcess f W.driver S u.1) +
      1 * (scalarGlobalStieltjesWeightedProcess g Z.driver T u.2 -
        scalarGlobalStieltjesWeightedProcess g Z.driver S u.2) := by
    change (scalarGlobalStieltjesWeightedProcess f W.driver T u.1 +
      scalarGlobalStieltjesWeightedProcess g Z.driver T u.2) -
      (scalarGlobalStieltjesWeightedProcess f W.driver S u.1 +
        scalarGlobalStieltjesWeightedProcess g Z.driver S u.2) = _
    ring
  simp_rw [he]
  exact hh.trans (by rw [one_mul]; rfl)

theorem actualQuerySpinLaw_query_spin_moment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ u, ((actualParisiQueryBrownianSystem W Z β hβ).B T (u.1.2,u.2) -
      (actualParisiQueryBrownianSystem W Z β hβ).B S (u.1.2,u.2)) * scalarHiddenSign u.1.1
      ∂actualParisiFullQuerySpinLaw W Z β H) =
    ∫ r in (S:ℝ)..(T:ℝ), actualParisiQueryRho W β r * actualParisiFullSusceptibilityExpected W β r :=
  (actualQuerySpinLaw_query_spin_moment_as_driver_moment W Z β hβ S T H).trans
    (actualFullProcess_query_brownian_cross_moment W Z β hβ S T H hST hTH)

theorem actualQuerySpinLaw_normalized_query_spin_moment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (q : ℕ → ℝ≥0) (d : ℕ) (j : Fin d) (H : ℝ≥0)
    (hq : q j ≤ q (j+1)) (hTH : q (j+1) ≤ H) :
    (∫ u, scalarNormalizedBrownianRow (d:=d) (actualParisiQueryBrownianSystem W Z β hβ).B q
      (u.1.2,u.2) j * scalarHiddenSign u.1.1 ∂actualParisiFullQuerySpinLaw W Z β H) =
    (∫ r in (q j:ℝ)..(q (j+1):ℝ), actualParisiQueryRho W β r * actualParisiFullSusceptibilityExpected W β r) /
      Real.sqrt ((q (j+1):ℝ)-(q j:ℝ)) := by
  have he (u : (Bool × Ω) × A) : scalarNormalizedBrownianRow (d:=d)
      (actualParisiQueryBrownianSystem W Z β hβ).B q (u.1.2,u.2) j * scalarHiddenSign u.1.1 =
      (((actualParisiQueryBrownianSystem W Z β hβ).B (q (j+1)) (u.1.2,u.2) -
        (actualParisiQueryBrownianSystem W Z β hβ).B (q j) (u.1.2,u.2)) * scalarHiddenSign u.1.1) /
        Real.sqrt ((q (j+1):ℝ)-(q j:ℝ)) := by
    simp only [scalarNormalizedBrownianRow]
    ring
  simp_rw [he]
  rw [integral_div,actualQuerySpinLaw_query_spin_moment W Z β hβ (q j) (q (j+1)) H hq hTH]

theorem actualQuerySpinLaw_normalized_query_mean_zero
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (q : ℕ → ℝ≥0) (d : ℕ) (j : Fin d) (H : ℝ≥0) :
    (∫ u, scalarNormalizedBrownianRow (d:=d) (actualParisiQueryBrownianSystem W Z β hβ).B q
      (u.1.2,u.2) j ∂actualParisiFullQuerySpinLaw W Z β H) = 0 := by
  let Q := actualParisiQueryBrownianSystem W Z β hβ
  have hm : Measurable (fun u => scalarNormalizedBrownianRow (d:=d) Q.B q u j) :=
    ((Q.measurable _).sub (Q.measurable _)).div_const _
  calc
    _ = ∫ u : Ω × A, scalarNormalizedBrownianRow (d:=d) Q.B q u j ∂Q.law :=
      (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integral_comp hm.aestronglyMeasurable
    _ = 0 := by
      change (∫ u, (Q.B (q (j+1)) u-Q.B (q j) u) / Real.sqrt ((q (j+1):ℝ)-(q j:ℝ)) ∂Q.law) = 0
      rw [integral_div,integral_sub (Q.brownian.integrable_eval _) (Q.brownian.integrable_eval _),
        Q.brownian.integral_eval,Q.brownian.integral_eval,sub_self,zero_div]

theorem actualQuerySpinLaw_spin_mean_zero
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    (∫ u, scalarHiddenSign u.1.1 ∂actualParisiFullQuerySpinLaw W Z β H) = 0 := by
  have hm : Measurable (fun u : Bool × Ω => scalarHiddenSign u.1) :=
    (measurable_of_finite scalarHiddenSign).comp measurable_fst
  exact ((actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β H).integral_comp hm.aestronglyMeasurable).trans
    (actualParisiFullTerminalSpinLaw_spin_mean_zero W β hβ H)

theorem actualQuerySpinLaw_normalized_query_spin_covariance
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (q : ℕ → ℝ≥0) (d : ℕ) (j : Fin d) (H : ℝ≥0)
    (hq : q j ≤ q (j+1)) (hTH : q (j+1) ≤ H) :
    cov[fun u => scalarNormalizedBrownianRow (d:=d) (actualParisiQueryBrownianSystem W Z β hβ).B q
        (u.1.2,u.2) j, fun u => scalarHiddenSign u.1.1; actualParisiFullQuerySpinLaw W Z β H] =
    (∫ r in (q j:ℝ)..(q (j+1):ℝ), actualParisiQueryRho W β r * actualParisiFullSusceptibilityExpected W β r) /
      Real.sqrt ((q (j+1):ℝ)-(q j:ℝ)) := by
  rw [covariance,actualQuerySpinLaw_normalized_query_mean_zero W Z β hβ q d j H,
    actualQuerySpinLaw_spin_mean_zero W Z β hβ H]
  simp only [sub_zero]
  exact actualQuerySpinLaw_normalized_query_spin_moment W Z β hβ q d j H hq hTH

end SKConstants.Completion.LC1

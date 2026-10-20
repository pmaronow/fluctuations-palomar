module

public import SKConstants.Completion.X32B.Limits

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X32B
open SKConstantsOAI.ZeroTemperatureSK Blueprint5a

variable {Ω : Type*} [MeasurableSpace Ω]

theorem supportIto_error_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (l : ℕ) :
    ∀ᵐ w ∂W.law,
      S32bA.supportItoLeftSum W β l w - S32bA.supportItoPrimitive W β w =
        -(J3B.potentialTaylorError W β (parisiEquilibriumPhysicalEndpoint β) l w +
          driftError W β (parisiEquilibriumPhysicalEndpoint β) l w +
          (1 / 2 : ℝ) * quadraticReplacement W (actualParisiFullScalarDrift β)
            (LJ.actualCurvature W β) (parisiEquilibriumPhysicalEndpoint β) l w +
          (1 / 2 : ℝ) * S32bB.curvatureQuadraticError W β
            (parisiEquilibriumPhysicalEndpoint β) l w +
          (1 / 2 : ℝ) * curvatureError W β (parisiEquilibriumPhysicalEndpoint β) l w) := by
  let S := parisiEquilibriumPhysicalEndpoint β
  let t := (brownianDyadicGrid S).time l
  have hcell (k : ℕ) := S32bB.solution_increment_eq W (actualParisiFullScalarDrift β)
    (t k) (t (k + 1)) ((brownianDyadicGrid S).monotone l (Nat.le_succ k))
  filter_upwards [ae_all_iff.mpr hcell] with w hw
  have hlin :
      (∑ k ∈ Finset.range (2 ^ l), actualParisiFullPosteriorMean W β (t k) w *
        (actualParisiFullScalarProcess W β (t (k + 1)) w -
          actualParisiFullScalarProcess W β (t k) w)) =
      S32bA.supportItoLeftSum W β l w +
        ∑ k ∈ Finset.range (2 ^ l), actualParisiFullPosteriorMean W β (t k) w *
          (actualParisiFullScalarDrift β).displacement W (t k) (t (k + 1)) w := by
    simp only [S32bA.supportItoLeftSum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    change actualParisiFullPosteriorMean W β (t k) w *
      ((actualParisiFullScalarDrift β).solution W.driver (t (k + 1)) w -
        (actualParisiFullScalarDrift β).solution W.driver (t k) w) = _
    rw [hw k, mul_add]
  rw [support_driftError_eq W β hβ, curvatureError_eq]
  unfold J3B.potentialTaylorError quadraticReplacement quadraticReplacementCell
    S32bB.curvatureQuadraticError S32bA.supportItoPrimitive
  simp only [S32bB.fullScalar_zero, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.sum_div]
  rw [support_rate_integral_eq]
  change S32bA.supportItoLeftSum W β l w - _ = _
  have hlin' := hlin
  dsimp only [actualParisiFullPosteriorMean, S, t] at hlin'
  simp only [mul_sub, Finset.sum_sub_distrib] at hlin'
  rw [hlin']
  change S32bA.supportItoLeftSum W β l w - _ = _
  dsimp only [LJ.actualCurvature, actualParisiFullPosteriorMean, actualParisiFullScalarProcess]
  ring

theorem five_error_sq_le (a b c d e : ℝ) :
    (-(a + b + (1 / 2 : ℝ) * c + (1 / 2 : ℝ) * d + (1 / 2 : ℝ) * e)) ^ 2 ≤
      5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c / 2), sq_nonneg (a - d / 2),
    sq_nonneg (a - e / 2), sq_nonneg (b - c / 2), sq_nonneg (b - d / 2),
    sq_nonneg (b - e / 2), sq_nonneg (c / 2 - d / 2),
    sq_nonneg (c / 2 - e / 2), sq_nonneg (d / 2 - e / 2),
    sq_nonneg c, sq_nonneg d, sq_nonneg e]

theorem supportItoLeftSum_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Tendsto (fun l => ∫ w,
      (S32bA.supportItoLeftSum W β l w - S32bA.supportItoPrimitive W β w) ^ 2 ∂W.law)
      atTop (𝓝 0) := by
  let S := parisiEquilibriumPhysicalEndpoint β
  let T := J3B.potentialTaylorError W β S
  let D := driftError W β S
  let R := quadraticReplacement W (actualParisiFullScalarDrift β) (LJ.actualCurvature W β) S
  let Q := S32bB.curvatureQuadraticError W β S
  let C := curvatureError W β S
  have hS : (S : ℝ) < β ^ 2 :=
    (div_lt_one (sq_pos_of_pos (zero_lt_one.trans hβ))).mp
      (S32bA.physicalTime_pre_mem β hβ S le_rfl).2
  have hT := J3B.potentialTaylorError_tendsto_L2 W β (zero_lt_one.trans hβ).ne' S hS
  have hD := driftError_tendsto_L2 W β S
  have hR := quadraticReplacement_tendsto_L2 W (actualParisiFullScalarDrift β)
    (LJ.actualCurvature W β) (LJ.measurable_actualCurvature W β) (LJ.actualCurvature_abs_le W β) S
  have hQ := S32bB.curvatureQuadraticError_tendsto_L2 W β S
  have hC := curvatureError_tendsto_L2 W β S
  have hi (l : ℕ) : Integrable (fun w => 5 *
      (T l w ^ 2 + D l w ^ 2 + R l w ^ 2 + Q l w ^ 2 + C l w ^ 2)) W.law :=
    (((((hT.1 l).add (hD.1 l)).add (hR.1 l)).add
      (S32bB.curvatureQuadraticError_meanSquare_le W β S l).1).add (hC.1 l)).const_mul 5
  have hlim := (((hT.2.add hD.2).add hR.2).add hQ).add hC.2 |>.const_mul 5
  apply squeeze_zero (fun l => integral_nonneg (fun w => sq_nonneg _))
    (g := fun l => ∫ w, 5 * (T l w ^ 2 + D l w ^ 2 + R l w ^ 2 + Q l w ^ 2 + C l w ^ 2) ∂W.law)
    (fun l => integral_mono_of_nonneg (ae_of_all _ (fun w => sq_nonneg _)) (hi l) (by
      filter_upwards [supportIto_error_eq W β hβ l] with w hw
      rw [hw]
      exact five_error_sq_le _ _ _ _ _))
  have he (l : ℕ) : (∫ w, 5 *
      (T l w ^ 2 + D l w ^ 2 + R l w ^ 2 + Q l w ^ 2 + C l w ^ 2) ∂W.law) =
      5 * ((∫ w, T l w ^ 2 ∂W.law) + (∫ w, D l w ^ 2 ∂W.law) +
        (∫ w, R l w ^ 2 ∂W.law) + (∫ w, Q l w ^ 2 ∂W.law) +
        ∫ w, C l w ^ 2 ∂W.law) := by
    have hiT : Integrable (fun w => T l w ^ 2) W.law := hT.1 l
    have hiD : Integrable (fun w => D l w ^ 2) W.law := hD.1 l
    have hiR : Integrable (fun w => R l w ^ 2) W.law := hR.1 l
    have hiQ : Integrable (fun w => Q l w ^ 2) W.law :=
      (S32bB.curvatureQuadraticError_meanSquare_le W β S l).1
    have hiC : Integrable (fun w => C l w ^ 2) W.law := hC.1 l
    have h2 := integral_add hiT hiD
    have h3 := integral_add (hiT.add hiD) hiR
    have h4 := integral_add ((hiT.add hiD).add hiR) hiQ
    have h5 := integral_add (((hiT.add hiD).add hiR).add hiQ) hiC
    simp only [Pi.add_apply] at h2 h3 h4 h5
    rw [integral_const_mul, h5, h4, h3, h2]
  simp_rw [he]
  simpa only [zero_add, mul_zero] using hlim

theorem supportFieldIto_holds : SupportFieldItoStatement := by
  intro Ω A _ _ W Z β hβ
  refine ⟨S32bB.supportFieldIto_integrable W Z β hβ, ?_⟩
  simp_rw [S32bA.supportField_meanSquare_eq W Z β hβ]
  exact supportItoLeftSum_tendsto_L2 W β hβ

end SKConstants.Completion.X32B

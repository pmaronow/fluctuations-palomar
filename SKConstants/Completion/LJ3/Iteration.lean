module

public import SKConstants.Completion.LJ3.ConditionalExpectation
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LJ3
open SKConstantsOAI.ZeroTemperatureSK LJ
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem integrable_exp_sum (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k))
    (hi : ∀ k θ, Integrable (fun w => Real.exp (θ * X k w)) μ) (n : ℕ) (θ : ℝ)
    [IsFiniteMeasure μ] :
    Integrable (fun w => Real.exp (θ * ∑ k ∈ Finset.range n, X k w)) μ := by
  induction n generalizing θ with
  | zero => simp
  | succ n ih =>
    have hdom := ((ih (2 * θ)).add (hi n (2 * θ))).div_const 2
    have hm : Measurable (fun w => Real.exp (θ * ∑ k ∈ Finset.range (n + 1), X k w)) :=
      ((Finset.measurable_sum _ (fun k _ => hX k)).const_mul θ).exp
    refine hdom.mono' hm.aestronglyMeasurable (ae_of_all _ (fun w => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Finset.sum_range_succ]
    have ha : Real.exp (2 * θ * ∑ k ∈ Finset.range n, X k w) =
        Real.exp (θ * ∑ k ∈ Finset.range n, X k w) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; ring
    have hb : Real.exp (2 * θ * X n w) = Real.exp (θ * X n w) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    simp only [Pi.add_apply]
    rw [ha, hb, mul_add, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp (θ * ∑ k ∈ Finset.range n, X k w) - Real.exp (θ * X n w))]

theorem mgf_sum_of_condExp_bounds (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace Ω) (hm : ∀ k, m k ≤ mΩ)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hi : ∀ k θ, Integrable (fun w => Real.exp (θ * X k w)) μ)
    (hpast : ∀ k, AEStronglyMeasurable[m k] (fun w => ∑ i ∈ Finset.range k, X i w) μ)
    (θ : ℝ) (B : ℕ → ℝ)
    (hcond : ∀ k, μ[fun w => Real.exp (θ * X k w) | m k] ≤ᵐ[μ] (fun _ => Real.exp (B k)))
    (n : ℕ) :
    mgf (fun w => ∑ k ∈ Finset.range n, X k w) μ θ ≤
      Real.exp (∑ k ∈ Finset.range n, B k) := by
  induction n with
  | zero => simp [mgf]
  | succ n ih =>
    let F := fun w => Real.exp (θ * ∑ i ∈ Finset.range n, X i w)
    let G := fun w => Real.exp (θ * X n w)
    have hFi : Integrable F μ := integrable_exp_sum μ X hX hi n θ
    have hGi : Integrable G μ := hi n θ
    have hFG : Integrable (F * G) μ :=
      (integrable_exp_sum μ X hX hi (n + 1) θ).congr
        (ae_of_all _ (fun w => by simp [F, G, Finset.sum_range_succ, mul_add, Real.exp_add]))
    have hFm : AEStronglyMeasurable[m n] F μ :=
      Real.continuous_exp.comp_aestronglyMeasurable ((hpast n).const_mul θ)
    have hpull := condExp_mul_of_aestronglyMeasurable_left hFm hFG hGi
    have hFC : Integrable (F * μ[G | m n]) μ := integrable_condExp.congr hpull
    calc
      _ = ∫ w, F w * G w ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun w => by simp [F, G, Finset.sum_range_succ, mul_add, Real.exp_add])
      _ = ∫ w, F w * μ[G | m n] w ∂μ := by
        change (∫ w, (F * G) w ∂μ) = _
        rw [← integral_condExp (μ := μ) (hm n) (f := F * G)]
        exact integral_congr_ae hpull
      _ ≤ ∫ w, F w * Real.exp (B n) ∂μ := by
        apply integral_mono_ae hFC (hFi.mul_const _)
        filter_upwards [hcond n] with w hw
        exact mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
      _ = Real.exp (B n) * mgf (fun w => ∑ k ∈ Finset.range n, X k w) μ θ := by
        rw [integral_mul_const, mul_comm]
        rfl
      _ ≤ Real.exp (B n) * Real.exp (∑ k ∈ Finset.range n, B k) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, Finset.sum_range_succ, add_comm]

theorem originalLagSum_measurable_past (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (q : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (hT : t n ≤ T) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) T) inferInstance]
      (originalLagSum W β t q n) W.law := by
  let b := actualParisiFullScalarDrift β
  let H : OriginalFieldCoefficient t := fun k p => q k * lagPastDisplacement β t ht k p
  have hH (k : ℕ) : Measurable (H k) := (measurable_lagPastDisplacement β t ht k).const_mul (q k)
  let F := fun p : ScalarContinuousPath T => originalFieldPastSum b t ht H n
    (scalarContinuousPathRestrict (t n) T hT p)
  have hF : Measurable F := (measurable_originalFieldPastSum b t ht H hH n).comp
    (measurable_scalarContinuousPathRestrict _ _ _)
  have he : (fun w => F (boundedDriftPastPath W b T w)) =ᵐ[W.law]
      originalLagSum W β t q n := by
    filter_upwards [boundedDriftPastPath_restrict W b (t n) T hT,
      originalFieldPastSum_actual W b t ht H n,
      originalLagSum_fieldSum W β t ht q n] with w hr hs hj
    dsimp only [F]
    rw [hr, hs]
    exact hj
  exact ((hF.comp (comap_measurable _)).stronglyMeasurable.aestronglyMeasurable).congr he

end SKConstants.Completion.LJ3

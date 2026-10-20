module

public import SKConstants.Completion.LC1.TerminalCrossMoment

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem actualFullProcess_terminal_cross_moment_earlier_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a S T H : ℝ≥0)
    (haS : a ≤ S) (hST : S ≤ T) (hTH : T ≤ H)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      actualParisiMagnetizationObservable W β H w * (W.B T w-W.B S w) ∂W.law) =
    ∫ r in (S:ℝ)..(T:ℝ), ∫ w,
      F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
        actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law := by
  let b := actualParisiFullScalarDrift β
  let G := F ∘ scalarContinuousPathRestrict a S haS
  have hG : Measurable G := hF.comp (measurable_scalarContinuousPathRestrict a S haS)
  have he : (fun w => G (boundedDriftPastPath W b S w)) =ᵐ[W.law]
      (fun w => F (boundedDriftPastPath W b a w)) := by
    filter_upwards [boundedDriftPastPath_restrict W b a S haS] with w hw
    dsimp only [G,Function.comp_apply]
    rw [hw]
  calc
    _ = ∫ w, G (boundedDriftPastPath W b S w) * actualParisiMagnetizationObservable W β H w *
        (W.B T w-W.B S w) ∂W.law :=
      integral_congr_ae (he.symm.mono (fun w hw => congrArg
        (fun x : ℝ => x * actualParisiMagnetizationObservable W β H w * (W.B T w-W.B S w)) hw))
    _ = ∫ r in (S:ℝ)..(T:ℝ), ∫ w, G (boundedDriftPastPath W b S w) *
        actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law :=
      actualFullProcess_terminal_brownian_cross_moment_test W β hβ S T H hST hTH G hG C (fun p => hFC _)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r _
      exact integral_congr_ae (he.mono (fun w hw => congrArg (fun x : ℝ => x *
        actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w)) hw))

theorem actualFullProcess_finite_weight_cross_moment_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a H : ℝ≥0)
    (s : Finset ι) (S T : ι → ℝ≥0) (c : ι → ℝ)
    (haS : ∀ i ∈ s, a ≤ S i) (hST : ∀ i ∈ s, S i ≤ T i) (hTH : ∀ i ∈ s, T i ≤ H)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      actualParisiMagnetizationObservable W β H w *
        (∑ i ∈ s, c i * (W.B (T i) w-W.B (S i) w)) ∂W.law) =
    ∑ i ∈ s, c i * (∫ r in (S i:ℝ)..(T i:ℝ), ∫ w,
      F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
        actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law) := by
  let f := F ∘ boundedDriftPastPath W (actualParisiFullScalarDrift β) a
  have hf := hF.comp (measurable_boundedDriftPastPath W (actualParisiFullScalarDrift β) a)
  have hm := measurable_actualParisiMagnetizationObservable W β H
  have hBound (w : Ω) : |f w * actualParisiMagnetizationObservable W β H w| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul (hFC _) (actualParisiMagnetizationObservable_abs_le W β H w)
      (abs_nonneg _) C.coe_nonneg).trans_eq (mul_one _)
  have hi (i : ι) : Integrable (fun w => c i *
      (f w * actualParisiMagnetizationObservable W β H w * (W.B (T i) w-W.B (S i) w))) W.law := by
    exact (((W.brownian.integrable_eval (T i)).sub (W.brownian.integrable_eval (S i))).bdd_mul
      (hf.mul hm).aestronglyMeasurable
      (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hBound w))).const_mul (c i)
  have he (w : Ω) : f w * actualParisiMagnetizationObservable W β H w *
      (∑ i ∈ s, c i * (W.B (T i) w-W.B (S i) w)) =
      ∑ i ∈ s, c i * (f w * actualParisiMagnetizationObservable W β H w * (W.B (T i) w-W.B (S i) w)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∫ w, f w * actualParisiMagnetizationObservable W β H w *
    (∑ i ∈ s, c i * (W.B (T i) w-W.B (S i) w)) ∂W.law) = _
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul]
  congr 1
  exact actualFullProcess_terminal_cross_moment_earlier_test W β hβ a (S i) (T i) H
    (haS i hi) (hST i hi) (hTH i hi) F hF C hFC

theorem actualFullProcess_finite_weight_cross_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (H : ℝ≥0)
    (s : Finset ι) (S T : ι → ℝ≥0) (c : ι → ℝ)
    (hST : ∀ i ∈ s, S i ≤ T i) (hTH : ∀ i ∈ s, T i ≤ H) :
    (∫ w, actualParisiMagnetizationObservable W β H w *
      (∑ i ∈ s, c i * (W.B (T i) w-W.B (S i) w)) ∂W.law) =
    ∑ i ∈ s, c i * (∫ r in (S i:ℝ)..(T i:ℝ), ∫ w, actualParisiFullCurvature β r.toNNReal
      (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law) := by
  simpa only [one_mul] using actualFullProcess_finite_weight_cross_moment_test W β hβ 0 H s S T c
    (fun _ _ => bot_le) hST hTH (fun _ => (1:ℝ)) measurable_const 1 (fun _ => by norm_num)

end SKConstants.Completion.LC1

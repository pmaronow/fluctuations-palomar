module
public import SKConstants.ParisiFullTerminalSpinLaw
public import SKConstants.ParisiFullMartingale

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport

lemma integral_scalarHiddenPriorBool_zero_fullPosterior (f : Bool → ℝ) :
    (∫ b, f b ∂scalarHiddenPriorBool 0) = f true/2+f false/2 := by
  rw [scalarHiddenPriorBool,integral_add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure,integral_smul_measure,integral_dirac,integral_dirac]
  norm_num [scalarPlusWeight,scalarMinusWeight]
  ring

lemma actualParisiSpinLinkDensity_le_two (β : ℝ) (b : Bool) (v y : ℝ) :
    actualParisiSpinLinkDensity β b v y ≤ 2 := by
  have h := actualParisiFullMagnetization_curvature_bounds β v y
  have hm := abs_le.mp h.1
  cases b <;> simp only [actualParisiSpinLinkDensity,scalarHiddenSign,Bool.false_eq_true,
    ↓reduceIte,one_mul,neg_mul] <;> linarith

lemma measurable_actualParisiFullTerminalMagnetization {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (W : BrownianSystem Ω) (T : ℝ≥0) : Measurable (fun w =>
      actualParisiFullMagnetization β T (actualParisiFullTerminalField β W T w)) :=
  ((continuous_actualParisiFullMagnetization β).comp
    ((continuous_const : Continuous (fun _ : ℝ => (T : ℝ))).prodMk continuous_id)).measurable.comp
      ((actualParisiFullScalarDrift β).solution_measurable W T)

theorem actualParisiFullTerminalSpinLaw_sign_test {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (W : BrownianSystem Ω) (T : ℝ≥0) (F : Ω → ℝ) (hF : Measurable F)
    (C : ℝ) (hFC : ∀ w, |F w| ≤ C) :
    (∫ u, scalarHiddenSign u.1*F u.2 ∂actualParisiFullTerminalSpinLaw β W T) =
      ∫ w, actualParisiFullMagnetization β T (actualParisiFullTerminalField β W T w)*F w ∂W.law := by
  let := W.isProbability
  let G : Bool × Ω → ℝ := fun u => actualParisiFullTerminalSpinDensity β W T u*
    (scalarHiddenSign u.1*F u.2)
  have hG : Measurable G := (measurable_actualParisiFullTerminalSpinDensity β W T).mul
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul (hF.comp measurable_snd))
  have hGi : Integrable G ((scalarHiddenPriorBool 0).prod W.law) := by
    apply Integrable.of_bound hG.aestronglyMeasurable (2*C)
    apply ae_of_all
    intro u
    have hd := actualParisiSpinLinkDensity_le_two β u.1 T (actualParisiFullTerminalField β W T u.2)
    have hp := actualParisiFullTerminalSpinDensity_pos β W T u
    have hs : |scalarHiddenSign u.1|=1 := by cases u.1 <;> norm_num [scalarHiddenSign]
    dsimp only [G]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos hp,abs_mul,hs,one_mul]
    exact mul_le_mul hd (hFC u.2) (abs_nonneg _) (by norm_num)
  have hw := integral_withDensity_eq_integral_toReal_smul
    (μ := (scalarHiddenPriorBool 0).prod W.law)
    (measurable_actualParisiFullTerminalSpinDensity β W T).ennreal_ofReal
    (ae_of_all _ (fun u => ENNReal.ofReal_lt_top)) (fun u => scalarHiddenSign u.1*F u.2)
  change (∫ u, scalarHiddenSign u.1*F u.2 ∂actualParisiFullTerminalSpinLaw β W T) = _ at hw
  have he : (fun u => (ENNReal.ofReal (actualParisiFullTerminalSpinDensity β W T u)).toReal •
      (scalarHiddenSign u.1*F u.2)) = G := by
    funext u
    rw [ENNReal.toReal_ofReal (actualParisiFullTerminalSpinDensity_pos β W T u).le]
    rfl
  rw [he,integral_prod_symm G hGi] at hw
  rw [hw]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  change (∫ b, G (b,w) ∂scalarHiddenPriorBool 0) =
    actualParisiFullMagnetization β T (actualParisiFullTerminalField β W T w)*F w
  rw [integral_scalarHiddenPriorBool_zero_fullPosterior]
  simp only [G,actualParisiFullTerminalSpinDensity,actualParisiSpinLinkDensity,
    scalarHiddenSign,Bool.false_eq_true,↓reduceIte]
  ring

theorem actualParisiFullTerminalSpinLaw_whole_past_posterior {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ) (hFC : ∀ p, |F p| ≤ C) :
    (∫ u, scalarHiddenSign u.1*
      F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a u.2)
        ∂actualParisiFullTerminalSpinLaw β W (a+v)) =
      ∫ w, actualParisiFullMagnetization β a (actualParisiFullTerminalField β W a w)*
        F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) ∂W.law := by
  let := W.isProbability
  let f : Ω → ℝ := fun w => F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)
  have hf : Measurable f := hF.comp (measurable_boundedDriftPastPath W _ a)
  have hfb : ∀ w, |f w| ≤ C := fun w => hFC _
  rw [actualParisiFullTerminalSpinLaw_sign_test β W (a+v) f hf C hfb]
  have hi (t : ℝ≥0) : Integrable (fun w => actualParisiFullMagnetization β t
      (actualParisiFullTerminalField β W t w)*f w) W.law := by
    apply Integrable.of_bound ((measurable_actualParisiFullTerminalMagnetization β W t).mul hf).aestronglyMeasurable C
    apply ae_of_all
    intro w
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul (actualParisiFullMagnetization_curvature_bounds β t _).1 (hfb w)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hm := actualParisiFullProcess_martingale_test W β hβ a v F hF C hFC
  have he : (fun w => f w*(actualParisiFullMagnetization β (a+v)
      (actualParisiFullTerminalField β W (a+v) w)-actualParisiFullMagnetization β a
        (actualParisiFullTerminalField β W a w))) =
      (fun w => actualParisiFullMagnetization β (a+v) (actualParisiFullTerminalField β W (a+v) w)*f w-
        actualParisiFullMagnetization β a (actualParisiFullTerminalField β W a w)*f w) := by
    funext w
    ring
  change (∫ w, f w*(actualParisiFullMagnetization β (a+v)
    (actualParisiFullTerminalField β W (a+v) w)-actualParisiFullMagnetization β a
      (actualParisiFullTerminalField β W a w)) ∂W.law)=0 at hm
  have hit := hi (a+v)
  simp only [NNReal.coe_add] at hit
  rw [he,integral_sub hit (hi a)] at hm
  exact sub_eq_zero.mp hm

end SKConstants

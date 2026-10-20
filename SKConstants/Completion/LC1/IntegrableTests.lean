module

public import SKConstants.ParisiActualRestartCoordinate
public import SKConstants.ParisiRestartObservable
public import SKConstants.ParisiFullRowSecondMoment
public import SKConstants.ParisiFullSpinPosterior

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actualFullProcess_martingale_test_integrable
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun w => F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)) W.law) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      actualParisiMagnetizationIncrement W β a (a+v) w ∂W.law) = 0 := by
  let P := boundedDriftPastPath W (actualParisiFullScalarDrift β) a
  let Fn : ℕ → ScalarContinuousPath a → ℝ := fun n p =>
    if |F p| ≤ (n : ℝ) then F p else 0
  have hFn (n : ℕ) : Measurable (Fn n) :=
    Measurable.ite (measurableSet_le hF.abs measurable_const) hF measurable_const
  have hB (n : ℕ) (p : ScalarContinuousPath a) : |Fn n p| ≤ (n : ℝ) := by
    dsimp [Fn]
    split_ifs with h
    · exact h
    · simpa only [abs_zero] using (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hz (n : ℕ) : (∫ w, Fn n (P w) *
      actualParisiMagnetizationIncrement W β a (a+v) w ∂W.law) = 0 :=
    actualParisiFullProcess_martingale_test W β hβ a v (Fn n) (hFn n) n (hB n)
  have hlim : Tendsto (fun n => ∫ w, Fn n (P w) *
      actualParisiMagnetizationIncrement W β a (a+v) w ∂W.law) atTop
      (𝓝 (∫ w, F (P w) * actualParisiMagnetizationIncrement W β a (a+v) w ∂W.law)) := by
    apply tendsto_integral_of_dominated_convergence (fun w => 2 * |F (P w)|)
    · intro n
      exact ((hFn n).comp (measurable_boundedDriftPastPath W _ a)).mul
        (measurable_actualParisiMagnetizationIncrement W β a (a+v)) |>.aestronglyMeasurable
    · exact hFi.abs.const_mul 2
    · intro n
      apply ae_of_all
      intro w
      rw [Real.norm_eq_abs, abs_mul]
      have hf : |Fn n (P w)| ≤ |F (P w)| := by
        dsimp [Fn]
        split_ifs
        · exact le_rfl
        · exact (abs_zero).le.trans (abs_nonneg _)
      nlinarith [mul_le_mul hf (actualParisiMagnetizationIncrement_abs_le W β a (a+v) w)
        (abs_nonneg _) (abs_nonneg (F (P w)))]
    · apply ae_of_all
      intro w
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (⌈|F (P w)|⌉₊ : ℕ)] with n hn
      have hle : |F (P w)| ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
      simp only [Fn, ite_eq_left hle]
  apply tendsto_nhds_unique hlim
  simpa only [hz] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem actualTerminalSpinLaw_sign_test_integrable
    (W : BrownianSystem Ω) (β : ℝ) (H : ℝ≥0) (F : Ω → ℝ)
    (hF : Measurable F) (hFi : Integrable F W.law) :
    (∫ u, scalarHiddenSign u.1 * F u.2 ∂actualParisiFullTerminalSpinLaw β W H) =
      ∫ w, actualParisiMagnetizationObservable W β H w * F w ∂W.law := by
  let := W.isProbability
  let G : Bool × Ω → ℝ := fun u => actualParisiFullTerminalSpinDensity β W H u *
    (scalarHiddenSign u.1 * F u.2)
  have hG : Measurable G := (measurable_actualParisiFullTerminalSpinDensity β W H).mul
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul (hF.comp measurable_snd))
  have hGi : Integrable G ((scalarHiddenPriorBool 0).prod W.law) := by
    apply ((hFi.comp_snd (scalarHiddenPriorBool 0)).abs.const_mul 2).mono'
      hG.aestronglyMeasurable
    apply ae_of_all
    intro u
    have hd := actualParisiSpinLinkDensity_le_two β u.1 H (actualParisiFullTerminalField β W H u.2)
    have hp := actualParisiFullTerminalSpinDensity_pos β W H u
    have hs : |scalarHiddenSign u.1| = 1 := by cases u.1 <;> norm_num [scalarHiddenSign]
    dsimp only [G]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp, abs_mul, hs, one_mul]
    exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
  have hw := integral_withDensity_eq_integral_toReal_smul
    (μ := (scalarHiddenPriorBool 0).prod W.law)
    (measurable_actualParisiFullTerminalSpinDensity β W H).ennreal_ofReal
    (ae_of_all _ (fun u => ENNReal.ofReal_lt_top)) (fun u => scalarHiddenSign u.1 * F u.2)
  change (∫ u, scalarHiddenSign u.1 * F u.2 ∂actualParisiFullTerminalSpinLaw β W H) = _ at hw
  have he : (fun u => (ENNReal.ofReal (actualParisiFullTerminalSpinDensity β W H u)).toReal •
      (scalarHiddenSign u.1 * F u.2)) = G := by
    funext u
    rw [ENNReal.toReal_ofReal (actualParisiFullTerminalSpinDensity_pos β W H u).le]
    rfl
  rw [he, integral_prod_symm G hGi] at hw
  rw [hw]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  change (∫ b, G (b,w) ∂scalarHiddenPriorBool 0) = _
  rw [integral_scalarHiddenPriorBool_zero_fullPosterior]
  simp only [G, actualParisiFullTerminalSpinDensity, actualParisiSpinLinkDensity,
    scalarHiddenSign, Bool.false_eq_true, ↓reduceIte]
  change ((1 + 1 * actualParisiMagnetizationObservable W β H w) * (1 * F w)) / 2 +
    ((1 + -1 * actualParisiMagnetizationObservable W β H w) * (-1 * F w)) / 2 = _
  ring

end SKConstants.Completion.LC1

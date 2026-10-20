module

public import SKConstants.Completion.N9c.FreshDriverLaw
public import SKConstants.Completion.Blueprint5.FineStatements

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators

namespace SKConstants.Completion.N9Q2
open SKConstantsOAI.ZeroTemperatureSK FineInformation M1 LFine
variable {Ω : Type*} [MeasurableSpace Ω]

def restartedField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a v : ℝ≥0) (B D : ScalarContinuousPath a)
    (p : ScalarContinuousPath v × ScalarContinuousPath v) : ℝ :=
  scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) (a+v)
    (0,(scalarConcatPath a v (B,p.1),scalarConcatPath a v (D,p.2)))
      ⟨a+v,(a+v).coe_nonneg,le_rfl⟩

theorem measurable_restartedField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a v : ℝ≥0) (B D : ScalarContinuousPath a) :
    Measurable (restartedField W β hβ a v B D) := by
  apply (ContinuousMap.measurable_eval _).comp
  apply (measurable_scalarTwoDriverPicardPath _ _ _ _ _ _).comp
  apply Measurable.prodMk measurable_const
  exact ((measurable_scalarConcatPath a v).comp
    (measurable_const.prodMk measurable_fst)).prodMk
      ((measurable_scalarConcatPath a v).comp (measurable_const.prodMk measurable_snd))

theorem meanSpin_eq_row (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (n : ℕ) (B D : Fin n → ScalarContinuousPath a) (i : Fin n) :
    meanSpin (freshRowsLaw W h f n)
      (gaussianSignRows (fun j => freshRowSign W β hβ a h f (B j) (D j))) i =
    ∫ z, scalarHiddenSign (freshRowSign W β hβ a h f (B i) (D i) z)
      ∂(gaussianReal 0 1).prod (freshRowSeedLaw W h f) := by
  change (∫ z : Fin n → ℝ × FreshRowSeed h f,
    (if freshRowSign W β hβ a h f (B i) (D i) (z i) then (1 : ℝ) else -1)
      ∂Measure.pi (fun _ : Fin n => (gaussianReal 0 1).prod (freshRowSeedLaw W h f))) = _
  exact integral_comp_eval (μ := fun _ : Fin n =>
    (gaussianReal 0 1).prod (freshRowSeedLaw W h f)) (i := i)
    ((measurable_of_finite scalarHiddenSign).comp
      (measurable_freshRowSign W β hβ a h f (B i) (D i))).aestronglyMeasurable

theorem freshRowSign_mean_eq_wiener (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (hh : 0 < h) (B D : ScalarContinuousPath a) :
    (∫ z, scalarHiddenSign (freshRowSign W β hβ a h f B D z)
      ∂(gaussianReal 0 1).prod (freshRowSeedLaw W h f)) =
    ∫ p, actualParisiFullMagnetization β (a+(h+f))
      (restartedField W β hβ a (h+f) B D p)
      ∂(scalarPrimitiveBrownianPathLaw W (h+f)).prod
        (scalarPrimitiveBrownianPathLaw W (h+f)) := by
  let P := ScalarContinuousPath (h+f) × ScalarContinuousPath (h+f)
  let m : P → ℝ := fun p => actualParisiFullMagnetization β (a+(h+f))
    (restartedField W β hβ a (h+f) B D p)
  have hm : Measurable m :=
    (((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable).comp
        (measurable_restartedField W β hβ a (h+f) B D)
  let S : P × ℝ → ℝ := fun p => if p.2 ≤ (1+m p.1)/2 then 1 else -1
  have hS : Measurable S := Measurable.ite
    (measurableSet_le measurable_snd ((measurable_const.add (hm.comp measurable_fst)).div_const 2))
      measurable_const measurable_const
  have hB (p : P × ℝ) : ‖S p‖ ≤ 1 := by dsimp [S]; split <;> norm_num
  let Q := (scalarPrimitiveBrownianPathLaw W (h+f)).prod
    (scalarPrimitiveBrownianPathLaw W (h+f))
  have hi : Integrable S (Q.prod SKConstantsOAI.SK.unitIntervalLaw) :=
    Integrable.of_bound hS.aestronglyMeasurable 1 (ae_of_all _ hB)
  have hl := N9c.freshFutureDrivers_threshold_law W h f hh
  have hF : Measurable (fun z : ℝ × FreshRowSeed h f =>
      (N9c.freshFutureDrivers h f z,z.2.2.2.2)) :=
    (N9c.measurable_freshFutureDrivers h f).prodMk measurable_snd.snd.snd.snd
  have he (z : ℝ × FreshRowSeed h f) :
      scalarHiddenSign (freshRowSign W β hβ a h f B D z) =
        S (N9c.freshFutureDrivers h f z,z.2.2.2.2) := by
    change scalarHiddenSign (if z.2.2.2.2 ≤
      (1+actualParisiFullMagnetization β (a+(h+f))
        (freshRowTerminalField W β hβ a h f B D z))/2 then true else false) =
      if z.2.2.2.2 ≤ (1+actualParisiFullMagnetization β (a+(h+f))
        (freshRowTerminalField W β hβ a h f B D z))/2 then 1 else -1
    split <;> rfl
  simp_rw [he]
  rw [← integral_map hF.aemeasurable hS.aestronglyMeasurable,hl,integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  exact N9b.integral_realThresholdSign (m p)
    (actualParisiFullMagnetization_curvature_bounds β _ _).1

theorem freshPosteriorMean_iff_wiener (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (hh : 0 < h) (n : ℕ) (B D : Fin n → ScalarContinuousPath a) :
    FreshPosteriorMeanStatement W β hβ a h f n B D ↔
      ∀ i, (∫ p, actualParisiFullMagnetization β (a+(h+f))
        (restartedField W β hβ a (h+f) (B i) (D i) p)
        ∂(scalarPrimitiveBrownianPathLaw W (h+f)).prod
          (scalarPrimitiveBrownianPathLaw W (h+f))) =
        fixedPastPosterior W β hβ a (B i) (D i) := by
  unfold FreshPosteriorMeanStatement
  simp_rw [meanSpin_eq_row, freshRowSign_mean_eq_wiener W β hβ a h f hh]

end SKConstants.Completion.N9Q2

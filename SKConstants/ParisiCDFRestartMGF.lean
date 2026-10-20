module

public import SKConstants.ParisiTimeFieldTranslate
public import SKConstants.ParisiPicardRestart

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.SK.Analytic

lemma translatedCDFDrift_path_right_continuous
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (a x0 : ℝ) :
    ∀ᵐ w ∂W.law, ∀ s : ℝ,
      ContinuousWithinAt (fun r =>
        (SKConstants.BoundedLipschitzDrift.translated
          (finiteTemperatureCDFDrift β α ha h1) a x0).pathDrift W r w) (Ioi s) s := by
  let b := SKConstants.BoundedLipschitzDrift.translated
    (finiteTemperatureCDFDrift β α ha h1) a x0
  let g : ℝ → ℝ := fun r => (a+(Real.toNNReal r : ℝ))/β^2
  have hg : Continuous g := by
    exact (continuous_const.add (continuous_subtype_val.comp continuous_real_toNNReal)).div_const _
  have hm : Monotone g := by
    intro r t hrt
    exact div_le_div_of_nonneg_right
      (add_le_add le_rfl (Real.toNNReal_mono hrt)) (sq_nonneg β)
  have hcg : Continuous (fun r => cdfTimeClamp (g r)) :=
    continuous_cdfTimeClamp.comp hg
  have hcm : Monotone (fun r => cdfTimeClamp (g r)) := cdfTimeClamp_monotone.comp hm
  filter_upwards [b.solution_continuous_ae W] with w hw
  have hx : Continuous (fun r => x0+b.solution W.driver (Real.toNNReal r) w) :=
    continuous_const.add (hw.comp continuous_real_toNNReal)
  have hG := continuous_along_path
    (F := fun t x => scalarCDFGradient β α (cdfTimeClamp t)
      (Real.toNNReal (1-cdfTimeClamp t)) x)
    (continuous_clamped_CDFGradient β α ha h1) hg hx
  intro s
  exact (stieltjes_comp_right_continuous α hcg hcm s).mul
    hG.continuousAt.continuousWithinAt

lemma physicalCDFJetField_spatial_bound (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    |deriv ((physicalCDFJetField β α ha h1 hβ hT0 hT1 0).f t) x| ≤ 1 := by
  change |deriv (compactCDFJet β α T 0 ((1/β^2)*t)) x| ≤ 1
  rw [deriv_compactCDFJet β α ha h1 hβ hT0 hT1]
  exact compactCDFJet_one_abs_le_one β α ha hT0 hT1.le _ x

theorem physicalCDFGradient_restart_mgf
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (a : ℝ) (ha0 : 0 ≤ a) (x0 : ℝ) (v : ℝ≥0)
    (hv : (a+(v : ℝ))/β^2 < T) (θ : ℝ) :
    (∫ w, Real.exp (θ *
      (compactCDFJet β α T 0 ((a+(v : ℝ))/β^2)
        (x0+(SKConstants.BoundedLipschitzDrift.translated
          (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver v w) -
        compactCDFJet β α T 0 (a/β^2) x0)) ∂W.law) ≤
      Real.exp (θ^2 * (v : ℝ) / 2) := by
  let F := physicalCDFJetField β α ha h1 hβ hT0 hT1 0
  let b := finiteTemperatureCDFDrift β α ha h1
  let b' := SKConstants.BoundedLipschitzDrift.translated b a x0
  have hvT : a+(v : ℝ) < T/(1/β^2) := by
    simp only [one_div, div_inv_eq_mul]
    exact (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mp hv
  have hbr : ∀ r ∈ Ico (0 : ℝ) (v : ℝ), ∀ᵐ w ∂W.law,
      ContinuousWithinAt (fun s => b'.pathDrift W s w) (Ioi r) r := by
    intro r hr
    exact (translatedCDFDrift_path_right_continuous W β α ha h1 a x0).mono
      (fun w hw => hw r)
  have hgen : ∀ r ∈ Icc a (a+(v : ℝ)), ∀ x, F.generator b.f r x = 0 := by
    intro r hr x
    have hrT : r/β^2 ∈ Icc (0 : ℝ) T :=
      ⟨div_nonneg (ha0.trans hr.1) (sq_nonneg β),
        (div_le_div_of_nonneg_right hr.2 (sq_nonneg β)).trans hv.le⟩
    have hbf : b.f r = physicalCDFCompactDrift β α T r := by
      funext z
      exact finiteTemperatureCDFDrift_eq_compact β α ha h1 hβ hT1.le hrT z
    unfold TimeField.generator
    rw [hbf]
    exact physicalCDFGradient_generator_zero β α ha h1 hβ hT0 hT1 r x
  have H := centeredTranslatedTimeField_mgf F a x0 ha0 b.f b' (fun _ _ => rfl)
    W v hvT θ hbr hgen (fun r hr x => physicalCDFJetField_spatial_bound
      β α ha h1 hβ hT0 hT1 r x)
  change (∫ w, Real.exp (θ *
    (compactCDFJet β α T 0 ((1/β^2)*(a+(v : ℝ)))
      (x0+b'.solution W.driver v w) - compactCDFJet β α T 0 ((1/β^2)*a) x0)) ∂W.law) ≤ _ at H
  rw [show (1/β^2)*(a+(v : ℝ))=(a+(v : ℝ))/β^2 by ring,
    show (1/β^2)*a=a/β^2 by ring] at H
  exact H

end SKConstants.ParisiFullSupport

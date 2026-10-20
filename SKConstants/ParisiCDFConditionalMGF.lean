module

public import SKConstants.ParisiCDFSubGaussian
public import SKConstants.ParisiBrownianMarkov

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option maxHeartbeats 1000000

namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK

theorem boundedDrift_restart_integral {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) (a v : ℝ≥0)
    (H : ScalarContinuousPath a × ScalarContinuousPath v → ℝ) (hH : Measurable H)
    (C : ℝ) (hbound : ∀ p, |H p| ≤ C) :
    (∫ w, H (boundedDriftPastPath W b a w,boundedDriftRestartPath W b a v w) ∂W.law) =
      ∫ past, ∫ w, H (past,boundedDriftRestartCallback b a v
        (past,brownianFinitePath W v w)) ∂W.law
        ∂W.law.map (boundedDriftPastPath W b a) := by
  let := W.isProbability
  let μ := W.law.map (boundedDriftPastPath W b a)
  let ν := W.law.map (brownianFinitePath W v)
  let J : ScalarContinuousPath a × ScalarContinuousPath v →
      ScalarContinuousPath a × ScalarContinuousPath v :=
    fun p => (p.1,boundedDriftRestartCallback b a v p)
  have hJ : Measurable J := measurable_fst.prodMk (measurable_boundedDriftRestartCallback b a v)
  have hi : Integrable (H ∘ J) (μ.prod ν) :=
    Integrable.of_mem_Icc (-C) C (hH.comp hJ).aemeasurable
      (ae_of_all _ (fun p => abs_le.mp (hbound (J p))))
  rw [← integral_map ((measurable_boundedDriftPastPath W b a).prodMk
    (measurable_boundedDriftRestartPath W b a v)).aemeasurable hH.aestronglyMeasurable,
    boundedDriftPast_restart_jointLaw, integral_map hJ.aemeasurable hH.aestronglyMeasurable]
  change (∫ p, (H ∘ J) p ∂μ.prod ν) = _
  rw [integral_prod (H ∘ J) hi]
  apply integral_congr_ae
  exact ae_of_all _ fun past =>
    integral_map (measurable_brownianFinitePath W v).aemeasurable
      ((hH.comp (measurable_const.prodMk
        ((measurable_boundedDriftRestartCallback b a v).comp
          (measurable_const.prodMk measurable_id)))).aestronglyMeasurable)

end SKConstants

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def preCDFGradientProcess {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (T : ℝ) (t : ℝ≥0) (w : Ω) : ℝ :=
  compactCDFJet β α T 0 ((t : ℝ)/β^2)
    (finiteTemperatureCDFProcess W β α ha h1 t w)

theorem preCDFGradient_conditional_mgf_test
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (a v : ℝ≥0) (hv : ((a : ℝ)+(v : ℝ))/β^2 < T)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (hF0 : ∀ p, 0 ≤ F p) (C : ℝ) (hFC : ∀ p, F p ≤ C) (θ : ℝ) :
    (∫ w, F (boundedDriftPastPath W (finiteTemperatureCDFDrift β α ha h1) a w) *
      Real.exp (θ * (preCDFGradientProcess W β α ha h1 T (a+v) w -
        preCDFGradientProcess W β α ha h1 T a w)) ∂W.law) ≤
      Real.exp (θ^2*(v : ℝ)/2) *
        ∫ w, F (boundedDriftPastPath W (finiteTemperatureCDFDrift β α ha h1) a w) ∂W.law := by
  let := W.isProbability
  let b := finiteTemperatureCDFDrift β α ha h1
  let endpoint (r : ℝ≥0) : Icc (0:ℝ) (r:ℝ) := ⟨r,r.coe_nonneg,le_rfl⟩
  let H : ScalarContinuousPath a × ScalarContinuousPath v → ℝ := fun p =>
    F p.1 * Real.exp (θ * (compactCDFJet β α T 0 (((a : ℝ)+(v : ℝ))/β^2)
      (p.2 (endpoint v)) - compactCDFJet β α T 0 ((a : ℝ)/β^2) (p.1 (endpoint a))))
  have hg (r : ℝ) : Measurable (compactCDFJet β α T 0 r) :=
    ((compactCDFJetField β α ha h1 hβ hT0 hT1 0).smooth.regular r).smooth.continuous.measurable
  have hH : Measurable H := (hF.comp measurable_fst).mul
    (Real.continuous_exp.measurable.comp (measurable_const.mul
      ((hg _ |>.comp ((ContinuousMap.measurable_eval _).comp measurable_snd)).sub
        (hg _ |>.comp ((ContinuousMap.measurable_eval _).comp measurable_fst)))))
  have hb (p : ScalarContinuousPath a × ScalarContinuousPath v) : |H p| ≤ C*Real.exp (2*|θ|) := by
    have hD : |compactCDFJet β α T 0 (((a : ℝ)+(v : ℝ))/β^2) (p.2 (endpoint v)) -
        compactCDFJet β α T 0 ((a : ℝ)/β^2) (p.1 (endpoint a))| ≤ 2 := by
      have hA := abs_le.mp (compactCDFJet_zero_abs_le_one β α ha hT0 hT1.le
        (((a : ℝ)+(v : ℝ))/β^2) (p.2 (endpoint v)))
      have hB := abs_le.mp (compactCDFJet_zero_abs_le_one β α ha hT0 hT1.le
        ((a : ℝ)/β^2) (p.1 (endpoint a)))
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    dsimp only [H]
    rw [abs_mul, abs_of_nonneg (hF0 _), abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul (hFC p.1) (Real.exp_le_exp.mpr ?_) (by positivity)
      ((hF0 p.1).trans (hFC p.1))
    calc θ * _ ≤ |θ * _| := le_abs_self _
      _ = |θ| * |_| := abs_mul _ _
      _ ≤ |θ| * 2 := mul_le_mul_of_nonneg_left hD (abs_nonneg _)
      _ = 2*|θ| := mul_comm _ _
  have he := boundedDrift_restart_integral W b a v H hH _ hb
  have hactual : (∫ w, F (boundedDriftPastPath W b a w) *
      Real.exp (θ * (preCDFGradientProcess W β α ha h1 T (a+v) w -
        preCDFGradientProcess W β α ha h1 T a w)) ∂W.law) =
      ∫ w, H (boundedDriftPastPath W b a w,boundedDriftRestartPath W b a v w) ∂W.law := by
    apply integral_congr_ae
    filter_upwards [boundedDriftPastPath_version W b a,boundedDriftRestartPath_version W b a v]
      with w hp hr
    simp only [H,endpoint,hp,hr,preCDFGradientProcess,finiteTemperatureCDFProcess,NNReal.coe_add]
    rfl
  rw [hactual,he]
  have hFi : Integrable F (W.law.map (boundedDriftPastPath W b a)) :=
    Integrable.of_mem_Icc 0 C hF.aemeasurable (ae_of_all _ (fun p => ⟨hF0 p,hFC p⟩))
  calc
    _ ≤ ∫ past, F past * Real.exp (θ^2*(v : ℝ)/2)
        ∂W.law.map (boundedDriftPastPath W b a) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun past => integral_nonneg (fun w =>
          mul_nonneg (hF0 past) (Real.exp_pos _).le))
      · exact hFi.mul_const _
      · apply ae_of_all
        intro past
        have hv' := physicalCDFGradient_restart_mgf W β α ha h1 hβ hT0 hT1
          a a.coe_nonneg (past (endpoint a)) v hv θ
        have hfresh : (∫ w, H (past,boundedDriftRestartCallback b a v
            (past,brownianFinitePath W v w)) ∂W.law) =
            F past * ∫ w, Real.exp (θ * (compactCDFJet β α T 0
              (((a : ℝ)+(v : ℝ))/β^2) (past (endpoint a)+
                (SKConstants.BoundedLipschitzDrift.translated b a (past (endpoint a))).solution
                  W.driver v w) - compactCDFJet β α T 0 ((a : ℝ)/β^2) (past (endpoint a)))) ∂W.law := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [boundedDriftRestartCallback_fresh_version W b a v past] with w hw
          simp only [H,hw,endpoint]
          rfl
        change (∫ w, H (past,boundedDriftRestartCallback b a v
          (past,brownianFinitePath W v w)) ∂W.law) ≤ F past * Real.exp (θ^2*(v : ℝ)/2)
        rw [hfresh]
        exact mul_le_mul_of_nonneg_left hv' (hF0 past)
    _ = Real.exp (θ^2*(v : ℝ)/2) *
        ∫ w, F (boundedDriftPastPath W b a w) ∂W.law := by
      rw [integral_mul_const,integral_map
        (measurable_boundedDriftPastPath W b a).aemeasurable hF.aestronglyMeasurable,mul_comm]

end SKConstants.ParisiFullSupport

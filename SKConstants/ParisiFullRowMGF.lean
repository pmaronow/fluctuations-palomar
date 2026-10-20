module

public import SKConstants.ParisiFullWeightedMGF

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option maxHeartbeats 1000000

namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport

def actualParisiFullWeightedForm {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ)
    (q : ℕ → ℝ≥0) (d : ℕ → ℝ) (m : ℕ) (w : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, c i *
    (actualParisiFullMagnetization β (t (i+1)) (actualParisiFullScalarProcess W β (t (i+1)) w) -
      actualParisiFullMagnetization β (t i) (actualParisiFullScalarProcess W β (t i) w))) +
  ∑ i ∈ Finset.range m, d i *
    (actualParisiFullMagnetization β (parisiEquilibriumPhysicalEndpoint β+q (i+1) : ℝ≥0)
        (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β+q (i+1)) w) -
      actualParisiFullMagnetization β (parisiEquilibriumPhysicalEndpoint β+q i : ℝ≥0)
        (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β+q i) w))

theorem actualParisiFullMagnetization_eq_compact_before_support (β : ℝ) (hβ : 1 < β)
    {T : ℝ} (hQT : parisiEquilibriumSupportEndpoint β < T) (hT1 : T ≤ 1)
    (t : ℝ≥0) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (x : ℝ) :
    actualParisiFullMagnetization β t x =
      compactCDFJet β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) T 0 ((t : ℝ)/β^2) x := by
  have hb : 0 < β^2 := sq_pos_of_pos (lt_trans zero_lt_one hβ)
  have htime : (t : ℝ)/β^2 ≤ parisiEquilibriumSupportEndpoint β := by
    apply (div_le_iff₀ hb).mpr
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ,mul_comm] using NNReal.coe_le_coe.mpr ht
  have ht0 : 0 ≤ (t : ℝ)/β^2 := div_nonneg t.coe_nonneg hb.le
  have hr : (t : ℝ)/β^2 ∈ Icc (0:ℝ) T := ⟨ht0,htime.trans hQT.le⟩
  simp only [actualParisiFullMagnetization,compactCDFJet,iteratedDeriv_zero,compactCDFGradient,
    cdfStripTime_eq hr,cdfTimeClamp_eq ⟨ht0,hr.2.trans hT1⟩]

theorem actualParisiFullWeightedForm_mgf {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (n : ℕ)
    (htn : t n = parisiEquilibriumPhysicalEndpoint β)
    (q : ℕ → ℝ≥0) (hq : Monotone q) (d : ℕ → ℝ) (m : ℕ) (θ : ℝ) :
    (∫ w, Real.exp (θ*actualParisiFullWeightedForm W β t c n q d m w) ∂W.law) ≤
      Real.exp (((preCDFWeightedProxy t c n+preCDFWeightedProxy q d m : ℝ≥0) : ℝ)*θ^2/2) := by
  let := W.isProbability
  let α := cdf (parisiEquilibriumMeasure β : Measure ℝ)
  have ha : ∀ z, α z ∈ Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1 = 1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hb : β ≠ 0 := ne_of_gt (lt_trans zero_lt_one hβ)
  let T := (parisiEquilibriumSupportEndpoint β+1)/2
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hT0 : 0 ≤ T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T < 1 := by dsimp [T]; linarith [hQ.2]
  have hQT : parisiEquilibriumSupportEndpoint β < T := by dsimp [T]; linarith [hQ.2]
  have hn : (t n : ℝ)/β^2 < T := by
    rw [htn,parisiEquilibriumPhysicalEndpoint_coe β hβ]
    simpa only [mul_div_cancel_left₀ _ (pow_ne_zero 2 hb)] using hQT
  let V := parisiEquilibriumPhysicalEndpoint β
  let F : ScalarContinuousPath V → ℝ := preCDFWeightedPast β α T t c n V
  have hFm : Measurable F := measurable_preCDFWeightedPast β α ha h1 hb hT0 hT1 t c n V
  have hFc (p : ScalarContinuousPath V) : |F p| ≤ 2*∑ i ∈ Finset.range n, |c i| :=
    preCDFWeightedPast_abs_le β α ha hT0 hT1.le t c n V p
  have hp := preCDFWeightedPast_version W β α ha h1 T t ht c n
  rw [htn] at hp
  have hpre : HasSubgaussianMGF (fun w => F (actualParisiEndpointPastPath W β w))
      (preCDFWeightedProxy t c n) W.law :=
    (preCDFWeightedIncrements_hasSubgaussianMGF W β α ha h1 hb hT0 hT1 t ht c n hn).congr hp.symm
  have H := actualParisi_past_post_mgf W β hβ F hFm _ hFc (preCDFWeightedProxy t c n)
    hpre q hq d m θ
  have he (w : Ω) : actualParisiFullWeightedForm W β t c n q d m w =
      preCDFWeightedIncrements W β α ha h1 T t c n w+actualParisiPostWeighted W β q d m w := by
    apply congrArg₂ (fun x y : ℝ => x+y)
    · apply Finset.sum_congr rfl
      intro i hi
      have hin := Finset.mem_range.mp hi
      have h0 : t i ≤ V := by
        change t i ≤ parisiEquilibriumPhysicalEndpoint β
        rw [←htn]
        exact ht (by omega)
      have hnext : t (i+1) ≤ V := by
        change t (i+1) ≤ parisiEquilibriumPhysicalEndpoint β
        rw [←htn]
        exact ht (by omega)
      rw [actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le _ h0,
        actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le _ hnext]
      rfl
    · apply Finset.sum_congr rfl
      intro i hi
      have hafter (r : ℝ≥0) : β^2*parisiEquilibriumSupportEndpoint β ≤
          (parisiEquilibriumPhysicalEndpoint β : ℝ)+(r : ℝ) := by
        rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
        exact le_add_of_nonneg_right r.coe_nonneg
      simp only [NNReal.coe_add]
      rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ _ (hafter (q (i+1))),
        actualParisiFullMagnetization_eq_tanh_after_support β hβ _ (hafter (q i))]
  calc
    _ = ∫ w, Real.exp (θ*(F (actualParisiEndpointPastPath W β w)+actualParisiPostWeighted W β q d m w)) ∂W.law := by
      apply integral_congr_ae
      filter_upwards [hp] with w hw
      rw [he]
      exact congrArg (fun x => Real.exp (θ*(x+actualParisiPostWeighted W β q d m w))) hw.symm
    _ ≤ _ := H

theorem actualParisiFullWeightedForm_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (n : ℕ)
    (htn : t n = parisiEquilibriumPhysicalEndpoint β)
    (q : ℕ → ℝ≥0) (hq : Monotone q) (d : ℕ → ℝ) (m : ℕ) :
    HasSubgaussianMGF (actualParisiFullWeightedForm W β t c n q d m)
      (preCDFWeightedProxy t c n+preCDFWeightedProxy q d m) W.law := by
  let := W.isProbability
  have hm (r : ℝ≥0) : Measurable (fun w => actualParisiFullMagnetization β r
      (actualParisiFullScalarProcess W β r w)) := by
    have hg : Continuous (actualParisiFullMagnetization β (r : ℝ)) :=
      continuous_iff_continuousAt.mpr (fun x =>
        (actualParisiFullMagnetization_hasDerivAt β r x).continuousAt)
    exact hg.measurable.comp ((actualParisiFullScalarDrift β).solution_measurable W r)
  have hX : Measurable (actualParisiFullWeightedForm W β t c n q d m) :=
    (Finset.measurable_fun_sum _ fun i hi => measurable_const.mul ((hm (t (i+1))).sub (hm (t i)))).add
      (Finset.measurable_fun_sum _ fun i hi => measurable_const.mul
        ((hm (parisiEquilibriumPhysicalEndpoint β+q (i+1))).sub
          (hm (parisiEquilibriumPhysicalEndpoint β+q i))))
  have hbound (w : Ω) : |actualParisiFullWeightedForm W β t c n q d m w| ≤
      2*∑ i ∈ Finset.range n, |c i| + 2*∑ i ∈ Finset.range m, |d i| := by
    have hA := abs_weighted_differences
      (fun i => actualParisiFullMagnetization β (t (i+1)) (actualParisiFullScalarProcess W β (t (i+1)) w))
      (fun i => actualParisiFullMagnetization β (t i) (actualParisiFullScalarProcess W β (t i) w)) c n
      (fun i => (actualParisiFullMagnetization_curvature_bounds β _ _).1)
      (fun i => (actualParisiFullMagnetization_curvature_bounds β _ _).1)
    have hB := abs_weighted_differences
      (fun i => actualParisiFullMagnetization β (parisiEquilibriumPhysicalEndpoint β+q (i+1) : ℝ≥0)
        (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β+q (i+1)) w))
      (fun i => actualParisiFullMagnetization β (parisiEquilibriumPhysicalEndpoint β+q i : ℝ≥0)
        (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β+q i) w)) d m
      (fun i => (actualParisiFullMagnetization_curvature_bounds β _ _).1)
      (fun i => (actualParisiFullMagnetization_curvature_bounds β _ _).1)
    exact (abs_add_le _ _).trans (add_le_add hA hB)
  refine ⟨fun θ => integrable_exp_mul_of_mem_Icc
    (a := -(2*∑ i ∈ Finset.range n, |c i| + 2*∑ i ∈ Finset.range m, |d i|))
    (b := 2*∑ i ∈ Finset.range n, |c i| + 2*∑ i ∈ Finset.range m, |d i|)
      hX.aemeasurable (ae_of_all _ fun w => abs_le.mp (hbound w)), fun θ => ?_⟩
  exact actualParisiFullWeightedForm_mgf W β hβ t ht c n htn q hq d m θ

end SKConstants

module

public import SKConstants.ParisiCDFStripJets
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFTimeContinuity
public import SKConstants.Upstream.OAI.Probability.SKSupport.Diffusion.BoundedDiffusionProperties

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def cdfTimeClamp (t : ℝ) : ℝ := max 0 (min t 1)

lemma cdfTimeClamp_mem (t : ℝ) : cdfTimeClamp t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma cdfTimeClamp_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : cdfTimeClamp t = t := by
  simp [cdfTimeClamp, min_eq_left ht.2, max_eq_right ht.1]

lemma continuous_cdfTimeClamp : Continuous cdfTimeClamp := by
  unfold cdfTimeClamp
  fun_prop

lemma continuous_family_of_uniform_time {F : ℝ → ℝ → ℝ}
    (hF : ∀ t, Continuous (F t))
    (hU : ∀ t, TendstoUniformly F (F t) (𝓝 t)) :
    Continuous (fun p : ℝ × ℝ => F p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have H : TendstoUniformly (fun q : ℝ × ℝ => F q.1) (F p.1) (𝓝 p) := by
    have HU := hU p.1
    rw [Metric.tendstoUniformly_iff] at HU ⊢
    intro ε hε
    exact (continuous_fst.tendsto p).eventually (HU ε hε)
  exact H.tendsto_comp (hF p.1).continuousAt (continuous_snd.tendsto p)

theorem continuous_clamped_CDFGradient (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) :
    Continuous (fun p : ℝ × ℝ => scalarCDFGradient β α (cdfTimeClamp p.1)
      (Real.toNNReal (1 - cdfTimeClamp p.1)) p.2) := by
  have ht1 (t : ℝ) : Real.toNNReal (1 - cdfTimeClamp t) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [(cdfTimeClamp_mem t).1]
  apply continuous_family_of_uniform_time
    (F := fun t => scalarCDFGradient β α (cdfTimeClamp t)
      (Real.toNNReal (1 - cdfTimeClamp t)))
  · intro t
    exact (scalarCDFGradient_lipschitz β ha α.mono _ _ (ht1 t)).continuous
  · intro t
    have hclamp : Tendsto cdfTimeClamp (𝓝 t) (𝓝[Icc (0 : ℝ) 1] cdfTimeClamp t) :=
      tendsto_nhdsWithin_iff.mpr ⟨continuous_cdfTimeClamp.tendsto t,
        Eventually.of_forall cdfTimeClamp_mem⟩
    have HU := scalarCDFGradient_time_uniform β α ha h1 (cdfTimeClamp_mem t)
    rw [Metric.tendstoUniformly_iff] at HU ⊢
    intro ε hε
    exact hclamp.eventually (HU ε hε)

lemma measurable_CDFDrift (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) :
    Measurable (fun p : ℝ × ℝ => α (cdfTimeClamp (p.1 / β ^ 2)) *
      scalarCDFGradient β α (cdfTimeClamp (p.1 / β ^ 2))
        (Real.toNNReal (1 - cdfTimeClamp (p.1 / β ^ 2))) p.2) := by
  have hscale : Measurable (fun p : ℝ × ℝ => p.1 / β ^ 2) :=
    measurable_fst.div_const _
  have ht : Measurable (fun p : ℝ × ℝ => cdfTimeClamp (p.1 / β ^ 2)) :=
    continuous_cdfTimeClamp.measurable.comp hscale
  have hm : Measurable (fun p : ℝ × ℝ => α (cdfTimeClamp (p.1 / β ^ 2))) :=
    α.mono.measurable.comp ht
  have hmap : Measurable (fun p : ℝ × ℝ => (p.1 / β ^ 2, p.2)) :=
    hscale.prodMk (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
  have H : Measurable ((fun q : ℝ × ℝ =>
      scalarCDFGradient β α (cdfTimeClamp q.1)
        (Real.toNNReal (1 - cdfTimeClamp q.1)) q.2) ∘
      (fun p : ℝ × ℝ => (p.1 / β ^ 2, p.2))) :=
    (continuous_clamped_CDFGradient β α ha h1).measurable.comp hmap
  have hg : Measurable (fun p : ℝ × ℝ =>
      scalarCDFGradient β α (cdfTimeClamp (p.1 / β ^ 2))
        (Real.toNNReal (1 - cdfTimeClamp (p.1 / β ^ 2))) p.2) :=
    H
  exact hm.mul hg

set_option maxHeartbeats 1000000 in
def finiteTemperatureCDFDrift (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) : BoundedLipschitzDrift where
  f v x := α (cdfTimeClamp (v / β ^ 2)) *
    scalarCDFGradient β α (cdfTimeClamp (v / β ^ 2))
      (Real.toNNReal (1 - cdfTimeClamp (v / β ^ 2))) x
  bound := 1
  lip := 1
  measurable := measurable_CDFDrift β α ha h1
  bounded := by
    intro v x
    have ht : Real.toNNReal (1 - cdfTimeClamp (v / β ^ 2)) ≤ 1 := by
      rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
      linarith [(cdfTimeClamp_mem (v / β ^ 2)).1]
    rw [abs_mul, abs_of_nonneg (ha _).1]
    have HG := (scalarCDF_derivative_bounds β ha α.mono
      (cdfTimeClamp (v / β ^ 2)) _ ht x).1
    exact (mul_le_mul_of_nonneg_left HG (ha _).1).trans (by simpa using (ha _).2)
  lipschitz := by
    intro v
    have ht : Real.toNNReal (1 - cdfTimeClamp (v / β ^ 2)) ≤ 1 := by
      rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
      linarith [(cdfTimeClamp_mem (v / β ^ 2)).1]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have H := (scalarCDFGradient_lipschitz β ha α.mono
      (cdfTimeClamp (v / β ^ 2)) _ ht).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at H ⊢
    rw [← mul_sub, abs_mul, abs_of_nonneg (ha _).1]
    exact (mul_le_mul_of_nonneg_left H (ha _).1).trans
      (mul_le_of_le_one_left (abs_nonneg _) (ha _).2)

def finiteTemperatureCDFProcess {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) : ℝ≥0 → Ω → ℝ :=
  (finiteTemperatureCDFDrift β α ha h1).solution W.driver

theorem finiteTemperatureCDFProcess_measurable {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (v : ℝ≥0) :
    Measurable (finiteTemperatureCDFProcess W β α ha h1 v) :=
  (finiteTemperatureCDFDrift β α ha h1).solution_measurable W v

theorem finiteTemperatureCDFProcess_continuous_ae {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) :
    ∀ᵐ w ∂W.law, Continuous (fun v => finiteTemperatureCDFProcess W β α ha h1 v w) :=
  (finiteTemperatureCDFDrift β α ha h1).solution_continuous_ae W

theorem finiteTemperatureCDFProcess_integral_equation {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) :
    ∀ᵐ w ∂W.law, ∀ v : ℝ≥0,
      finiteTemperatureCDFProcess W β α ha h1 v w = W.B v w +
        ∫ r in (0 : ℝ)..(v : ℝ),
          α (cdfTimeClamp (r / β ^ 2)) * scalarCDFGradient β α (cdfTimeClamp (r / β ^ 2))
            (Real.toNNReal (1 - cdfTimeClamp (r / β ^ 2)))
            (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal r) w) := by
  filter_upwards [W.driver_indistinguishable] with w hw
  intro v
  rw [finiteTemperatureCDFProcess,
    BoundedLipschitzDrift.solution_eq _ _ W.driver_progressive, hw]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr0 : 0 ≤ r := by simpa only [min_eq_left v.coe_nonneg] using hr.1
  simp only [finiteTemperatureCDFDrift, Real.coe_toNNReal r hr0]

end SKConstants.ParisiFullSupport

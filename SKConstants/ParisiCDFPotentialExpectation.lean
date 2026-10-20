module

public import SKConstants.ParisiCDFValueRegular

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.SK.Analytic
variable {Ω : Type*} [MeasurableSpace Ω]
variable (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
  (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) (hβ : β≠0)
  {T : ℝ} (hT0 : 0≤T) (hT1 : T<1)

def physicalCDFPotential (β : ℝ) (α : ℝ → ℝ) (T v x : ℝ) : ℝ :=
  compactCDFValue β α T (v/β^2) x

def physicalCDFPotentialRate (β : ℝ) (α : ℝ → ℝ) (T v x : ℝ) : ℝ :=
  (1/β^2)*compactCDFValueRate β α T (v/β^2) x

def physicalCDFPotentialExpected (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) (T v : ℝ) : ℝ :=
  ∫ w, physicalCDFPotential β α T v
    (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w) ∂W.law

include ha h1 hβ hT0 hT1 in
lemma physicalCDFPotentialExpected_continuous :
    Continuous (physicalCDFPotentialExpected W β α ha h1 T) := by
  obtain ⟨C,hC⟩ := compactCDFValue_time_lipschitz β α ha h1 hβ hT0 hT1
  apply expected_regular_continuous W (finiteTemperatureCDFDrift β α ha h1) 1
    (Real.toNNReal ((C:ℝ)/β^2))
  · intro t
    exact compactCDFValue_lipschitz β α ha hT0 _
  · intro s t x
    have H := hC (s/β^2) (t/β^2) x
    unfold physicalCDFPotential
    rw [Real.coe_toNNReal _ (div_nonneg C.coe_nonneg (sq_nonneg β))]
    rw [←sub_div,abs_div,abs_of_nonneg (sq_nonneg β)] at H
    convert H using 1 <;> ring

include ha h1 hβ hT1 in
lemma physicalCDFPotential_integral_rate {a b : ℝ}
    (ha0 : 0≤a) (hab : a≤b) (hbT : b≤β^2*T) (x : ℝ) :
    physicalCDFPotential β α T b x-physicalCDFPotential β α T a x=
      ∫ r in a..b, physicalCDFPotentialRate β α T r x := by
  unfold physicalCDFPotential physicalCDFPotentialRate
  rw [compactCDFValue_integral_rate β α ha h1 hβ hT1
    (div_nonneg ha0 (sq_nonneg β)) (div_le_div_of_nonneg_right hab (sq_nonneg β))
    ((div_le_iff₀ (sq_pos_of_ne_zero hβ)).mpr (by simpa only [mul_comm] using hbT))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun r => compactCDFValueRate β α T r x) (pow_ne_zero 2 hβ)]
  simp only [smul_eq_mul]
  field_simp

include hβ hT0 hT1 in
lemma physicalCDFPotential_expected_right_derivative (v : ℝ≥0) (hv : (v:ℝ)/β^2<T) :
    HasDerivWithinAt (physicalCDFPotentialExpected W β α ha h1 T)
      ((1/2:ℝ)*compactCDFCoefficient α T ((v:ℝ)/β^2)*
        physicalCDFJetSquareMoment W β α ha h1 T 0 v) (Ioi (v:ℝ)) v := by
  let := W.isProbability
  let F := physicalCDFPotential β α T
  let D := physicalCDFPotentialRate β α T
  have hF (t : ℝ) : ContDiff ℝ ∞ (F t) := compactCDFValue_smooth β α ha hβ hT0 hT1 _
  have hFd : BoundedSmoothFamily (fun t => deriv (F t)) := by
    have HE : (fun t => deriv (F t))=fun t => compactCDFGradient β α T (t/β^2) := by
      funext t
      exact compactCDFValue_deriv_eq β α ha hT0 _
    rw [HE]
    exact boundedSmoothFamily_time_comp (compactCDFGradient_family β α ha h1 hβ hT0 hT1)
      (measurable_id.div_const _)
  have hD : BoundedSmoothFamily D :=
    (boundedSmoothFamily_time_comp (compactCDFValueRate_family β α ha h1 hβ hT0 hT1)
      (measurable_id.div_const _)).const_mul _
  have hDr (x : ℝ) : ContinuousWithinAt (fun r => D r x) (Ioi (v:ℝ)) v := by
    have HC := compactCDFValueRate_right_smooth β α ha h1 hβ hT0 hT1 0 ((v:ℝ)/β^2) x
    simp only [iteratedDeriv_zero] at HC
    have HM : Tendsto (fun r : ℝ => r/β^2) (𝓝[>] (v:ℝ)) (𝓝[>] ((v:ℝ)/β^2)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuous_id.div_const _).tendsto _ |>.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (div_lt_div_iff_of_pos_right (sq_pos_of_ne_zero hβ)).mpr hr
    exact (HC.tendsto.comp HM).const_mul (1/β^2)
  have hvH : (v:ℝ)<β^2*T := by
    simpa only [mul_comm] using (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mp hv
  have HR := expected_hasDerivWithinAt_right_regular W (finiteTemperatureCDFDrift β α ha h1)
    hF hFd hD (T:=β^2*T) (fun a b ha0 hab hb x =>
      physicalCDFPotential_integral_rate β α ha h1 hβ hT1 ha0 hab hb x)
    v hvH hDr
    ((finiteTemperatureCDFDrift_path_right_continuous W β α ha h1).mono (fun w hw => hw v))
  change HasDerivWithinAt (fun t => ∫ w, F t
    ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal t) w) ∂W.law) _ _ _
  convert HR using 1
  unfold physicalCDFJetSquareMoment
  rw [←integral_const_mul]
  have HG : deriv (F v)=compactCDFGradient β α T ((v:ℝ)/β^2) :=
    compactCDFValue_deriv_eq β α ha hT0 _
  have hGF := compactCDFGradient_family β α ha h1 hβ hT0 hT1
  have hx := (finiteTemperatureCDFDrift β α ha h1).solution_measurable W v
  have hi1 := (integrable_family_comp (P:=W.law) hGF ((v:ℝ)/β^2) hx).mul_bdd
    (((finiteTemperatureCDFDrift β α ha h1).pathDrift_measurable W).comp measurable_prodMk_left).aestronglyMeasurable
    (Eventually.of_forall (fun w => (finiteTemperatureCDFDrift β α ha h1).pathDrift_bound W v w))
  have hi2 := integrable_family_comp (P:=W.law) hGF.deriv ((v:ℝ)/β^2) hx
  have hi3 := integrable_family_comp (P:=W.law) hD v hx
  change Integrable (fun w => compactCDFGradient β α T ((v:ℝ)/β^2)
    ((finiteTemperatureCDFDrift β α ha h1).solution W.driver v w)*
    (finiteTemperatureCDFDrift β α ha h1).pathDrift W (v:ℝ) w) W.law at hi1
  rw [HG]
  rw [←integral_const_mul,←integral_add hi1 (hi2.const_mul (1/2:ℝ))]
  have hi12 := hi1.add (hi2.const_mul (1/2:ℝ))
  change Integrable (fun w => compactCDFGradient β α T ((v:ℝ)/β^2)
    ((finiteTemperatureCDFDrift β α ha h1).solution W.driver v w)*
    (finiteTemperatureCDFDrift β α ha h1).pathDrift W (v:ℝ) w+
    (1/2:ℝ)*deriv (compactCDFGradient β α T ((v:ℝ)/β^2))
      ((finiteTemperatureCDFDrift β α ha h1).solution W.driver v w)) W.law at hi12
  rw [←integral_add hi12 hi3]
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [BoundedLipschitzDrift.pathDrift,Real.toNNReal_coe,HG]
  rw [finiteTemperatureCDFDrift_eq_compact β α ha h1 hβ hT1.le
    ⟨div_nonneg v.coe_nonneg (sq_nonneg β),hv.le⟩]
  unfold D physicalCDFPotentialRate compactCDFValueRate physicalCDFCompactDrift compactCDFJet
    finiteTemperatureCDFProcess
  simp only [iteratedDeriv_zero]
  field_simp
  ring

include hT0 in
lemma physicalCDFPotentialExpected_zero :
    physicalCDFPotentialExpected W β α ha h1 T 0=scalarCDFValue β α 0 1 0 := by
  let := W.isProbability
  unfold physicalCDFPotentialExpected physicalCDFPotential compactCDFValue finiteTemperatureCDFProcess
  simp only [Real.toNNReal_zero,BoundedLipschitzDrift.solution_zero,zero_div,
    cdfStripTime_eq ⟨le_rfl,hT0⟩,sub_zero,Real.toNNReal_one,integral_const,
    probReal_univ,smul_eq_mul,one_mul]

include hβ hT0 hT1 in
lemma physicalCDFPotentialExpected_integral (V : ℝ) (hV0 : 0≤V) (hVT : V/β^2<T) :
    physicalCDFPotentialExpected W β α ha h1 T V=scalarCDFValue β α 0 1 0+
      (1/2:ℝ)*(∫ v in 0..V, compactCDFCoefficient α T (v/β^2)*
        physicalCDFJetSquareMoment W β α ha h1 T 0 v) := by
  have hcm : Monotone (fun v : ℝ => compactCDFCoefficient α T (v/β^2)) :=
    α.mono.comp ((cdfStripTime_monotone T).comp (fun _ _ h =>
      div_le_div_of_nonneg_right h (sq_nonneg β)))
  have hi := (hcm.intervalIntegrable (μ:=volume) (a:=0) (b:=V)).mul_continuousOn
    (physicalCDFJetSquareMoment_continuous W β α ha h1 hβ hT0 hT1 0).continuousOn
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hV0
    (physicalCDFPotentialExpected_continuous W β α ha h1 hβ hT0 hT1).continuousOn
    (fun r hr => ?_) (hi.const_mul (1/2:ℝ))
  · simp only [physicalCDFPotentialExpected_zero W β α ha h1 hT0] at H
    rw [intervalIntegral.integral_const_mul] at H
    linarith
  · have hr0 : 0≤r := hr.1.le
    have hrT : r/β^2<T := (div_le_div_of_nonneg_right hr.2.le (sq_nonneg β)).trans_lt hVT
    have HD := physicalCDFPotential_expected_right_derivative W β α ha h1 hβ hT0 hT1
      (Real.toNNReal r) (by simpa only [Real.coe_toNNReal r hr0] using hrT)
    simp only [Real.coe_toNNReal r hr0] at HD
    convert HD using 1 <;> ring

end SKConstants.ParisiFullSupport

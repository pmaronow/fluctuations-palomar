module

public import SKConstants.ParisiCDFTimeEquation
public import SKConstants.Upstream.OAI.Probability.SKSupport.Regularity.GaussianFlowRegularity
public import SKConstants.Upstream.OAI.Probability.SKSupport.Regularity.FamilyDifferentiation

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

lemma cdfStripTime_eq {T t : ℝ} (ht : t ∈ Icc (0:ℝ) T) : cdfStripTime T t = t := by
  simp [cdfStripTime, min_eq_left ht.2, max_eq_right ht.1]

lemma cdfStripTime_monotone (T : ℝ) : Monotone (cdfStripTime T) := by
  intro a b hab
  exact max_le_max le_rfl (min_le_min hab le_rfl)

def compactCDFGradient (β : ℝ) (α : ℝ → ℝ) (T t : ℝ) : ℝ → ℝ :=
  scalarCDFGradient β α (cdfStripTime T t) (Real.toNNReal (1-cdfStripTime T t))

def compactCDFCoefficient (α : ℝ → ℝ) (T t : ℝ) : ℝ := α (cdfStripTime T t)

def compactCDFValueRate (β : ℝ) (α : ℝ → ℝ) (T t x : ℝ) : ℝ :=
  -(β^2/2)*(deriv (compactCDFGradient β α T t) x +
    compactCDFCoefficient α T t*(compactCDFGradient β α T t x*
      compactCDFGradient β α T t x))

lemma compactCDFGradient_family (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    BoundedSmoothFamily (compactCDFGradient β α T) :=
  scalarCDF_strip_gradient_family β α ha h1 hβ hT0 hT1

lemma compactCDFGradient_continuous (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => compactCDFGradient β α T p.1 p.2) := by
  have hmap : Continuous (fun p : ℝ × ℝ => (cdfStripTime T p.1, p.2)) :=
    ((continuous_cdfStripTime T).comp continuous_fst).prodMk continuous_snd
  have H := (continuous_clamped_CDFGradient β α ha h1).comp hmap
  have he (t : ℝ) : cdfTimeClamp (cdfStripTime T t) = cdfStripTime T t :=
    cdfTimeClamp_eq ⟨(cdfStripTime_mem hT0 t).1, (cdfStripTime_mem hT0 t).2.trans hT1.le⟩
  simpa only [Function.comp_def, he, compactCDFGradient] using H

lemma smoothFamily_jet_continuous {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv n (F p.1) p.2) := by
  have H := hF.continuousOn_iteratedDeriv
    (S := univ) (by simpa only [univ_prod_univ] using hc.continuousOn (s := univ)) n
  simpa only [univ_prod_univ, continuousOn_univ] using H

lemma continuous_fixed_space {F : ℝ → ℝ → ℝ}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (x : ℝ) :
    Continuous (fun r => F r x) := by
  have hmap : Continuous (fun r : ℝ => (r,x)) :=
    continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x))
  exact hF.comp hmap

lemma measurable_fixed_space {F : ℝ → ℝ → ℝ}
    (hF : Measurable (fun p : ℝ × ℝ => F p.1 p.2)) (x : ℝ) :
    Measurable (fun r => F r x) := by
  have hmap : Measurable (fun r : ℝ => (r,x)) :=
    measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => x))
  exact hF.comp hmap

lemma compactCDFCoefficient_right_continuous (α : StieltjesFunction ℝ) (T t : ℝ) :
    ContinuousWithinAt (compactCDFCoefficient α T) (Ioi t) t := by
  have hT : Tendsto (cdfStripTime T) (𝓝[Ici t] t)
      (𝓝[Ici (cdfStripTime T t)] cdfStripTime T t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_cdfStripTime T).tendsto t |>.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact cdfStripTime_monotone T hr
  exact ((α.right_continuous _).tendsto.comp hT).mono_left
    (nhdsWithin_mono _ Ioi_subset_Ici_self)

lemma compactCDFCoefficient_family (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (T : ℝ) :
    BoundedSmoothFamily (fun t (_x : ℝ) => compactCDFCoefficient α T t) := by
  apply BoundedSmoothFamily.timeConst (C := 1)
  · exact α.mono.measurable.comp (continuous_cdfStripTime T).measurable
  · intro t
    simpa only [compactCDFCoefficient, abs_of_nonneg (ha _).1, NNReal.coe_one] using (ha _).2

lemma compactCDFValueRate_family (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    BoundedSmoothFamily (compactCDFValueRate β α T) :=
  ((compactCDFGradient_family β α ha h1 hβ hT0 hT1).deriv.add
    ((compactCDFCoefficient_family α ha T).mul
      ((compactCDFGradient_family β α ha h1 hβ hT0 hT1).mul
        (compactCDFGradient_family β α ha h1 hβ hT0 hT1)))).const_mul (-(β^2/2))

lemma compactCDFValueRate_jet (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) (t x : ℝ) :
    iteratedDeriv n (compactCDFValueRate β α T t) x =
      -(β^2/2)*(iteratedDeriv (n+1) (compactCDFGradient β α T t) x +
        compactCDFCoefficient α T t*
          iteratedDeriv n (fun y => compactCDFGradient β α T t y*
            compactCDFGradient β α T t y) x) := by
  have hF := compactCDFGradient_family β α ha h1 hβ hT0 hT1
  have hd := ((hF.deriv.regular t).smooth.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt (x := x)
  have hp : ContDiffAt ℝ n (fun y => compactCDFCoefficient α T t *
      (compactCDFGradient β α T t y*compactCDFGradient β α T t y)) x :=
    ((contDiff_const.mul ((hF.mul hF).regular t).smooth).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
  unfold compactCDFValueRate
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add hd hp,
    iteratedDeriv_const_mul_field, ← iteratedDeriv_succ']

lemma compactCDFValueRate_right_smooth (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) (t x : ℝ) :
    ContinuousWithinAt (fun r => iteratedDeriv n (compactCDFValueRate β α T r) x)
      (Ioi t) t := by
  have hF := compactCDFGradient_family β α ha h1 hβ hT0 hT1
  have hFc := compactCDFGradient_continuous β α ha h1 hT0 hT1
  have hD := smoothFamily_jet_continuous hF hFc (n+1)
  have hP := smoothFamily_jet_continuous (hF.mul hF) (hFc.mul hFc) n
  have hd : Continuous (fun r => iteratedDeriv (n+1) (compactCDFGradient β α T r) x) :=
    continuous_fixed_space (F := fun r => iteratedDeriv (n+1) (compactCDFGradient β α T r)) hD x
  have hp : Continuous (fun r => iteratedDeriv n
      (fun y => compactCDFGradient β α T r y*compactCDFGradient β α T r y) x) :=
    continuous_fixed_space (F := fun r => iteratedDeriv n
      (fun y => compactCDFGradient β α T r y*compactCDFGradient β α T r y)) hP x
  have H := (hd.continuousAt.continuousWithinAt.add
    ((compactCDFCoefficient_right_continuous α T t).mul hp.continuousAt.continuousWithinAt)).const_mul
      (-(β^2/2))
  simpa only [compactCDFValueRate_jet β α ha h1 hβ hT0 hT1 n,
    Pi.add_apply, Pi.mul_apply] using H

lemma compactCDFValueRate_eq (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) {T r : ℝ} (hT1 : T ≤ 1)
    (hr : r ∈ Icc (0:ℝ) T) (x : ℝ) :
    compactCDFValueRate β α T r x = scalarCDFValueRate β α r x := by
  have ht1 : Real.toNNReal (1-r) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hr.1]
  unfold compactCDFValueRate compactCDFCoefficient compactCDFGradient scalarCDFValueRate
  rw [cdfStripTime_eq hr, (scalarCDFGradient_hasDerivAt β ha α.mono r _ ht1 x).deriv]
  ring

end SKConstants.ParisiFullSupport

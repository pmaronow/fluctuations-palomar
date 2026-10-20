module

public import SKConstants.ParisiCDFTimeJets
public import SKConstants.Upstream.OAI.Probability.SKSupport.Regularity.TimeFields

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def compactCDFJet (β : ℝ) (α : ℝ → ℝ) (T : ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  iteratedDeriv n (compactCDFGradient β α T t) x

lemma compactCDFJet_eq_valueJet (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) {T t : ℝ} (hT1 : T ≤ 1)
    (ht : t ∈ Icc (0:ℝ) T) (n : ℕ) (x : ℝ) :
    compactCDFJet β α T n t x =
      iteratedDeriv (n+1) (scalarCDFValue β α t (Real.toNNReal (1-t))) x := by
  have htt : Real.toNNReal (1-t) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [ht.1]
  unfold compactCDFJet compactCDFGradient
  rw [cdfStripTime_eq ht, scalarCDF_gradient_eq_deriv ha α.mono β t _ htt,
    ← iteratedDeriv_succ']

lemma compactCDFJet_hasDerivAt (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) (t x : ℝ) :
    HasDerivAt (compactCDFJet β α T n t) (compactCDFJet β α T (n+1) t x) x := by
  have hf := (((compactCDFGradient_family β α ha h1 hβ hT0 hT1).iteratedDeriv n).regular t).smooth
  change HasDerivAt (iteratedDeriv n (compactCDFGradient β α T t))
    (iteratedDeriv (n+1) (compactCDFGradient β α T t) x) x
  rw [iteratedDeriv_succ]
  exact (hf.differentiable (by simp) x).hasDerivAt

def compactCDFJetField (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) : TimeField T where
  f := compactCDFJet β α T n
  d := fun t x => iteratedDeriv (n+1) (compactCDFValueRate β α T t) x
  smooth := (compactCDFGradient_family β α ha h1 hβ hT0 hT1).iteratedDeriv n
  rate_smooth := (compactCDFValueRate_family β α ha h1 hβ hT0 hT1).iteratedDeriv (n+1)
  continuous := smoothFamily_jet_continuous
    (compactCDFGradient_family β α ha h1 hβ hT0 hT1)
    (compactCDFGradient_continuous β α ha h1 hT0 hT1) n
  rate_right := compactCDFValueRate_right_smooth β α ha h1 hβ hT0 hT1 (n+1)
  time_deriv := by
    intro t ht0 htT x
    have H := scalarCDFValue_time_derivative_right_jets β α ha h1 hβ hT0 hT1 ht0 htT (n+1) x
    apply H.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with r hr hrT
      exact compactCDFJet_eq_valueJet β α ha hT1.le ⟨ht0.trans hr.le,hrT.le⟩ n x
    · exact compactCDFJet_eq_valueJet β α ha hT1.le ⟨ht0,htT.le⟩ n x

lemma boundedSmoothFamily_time_comp {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) {a : ℝ → ℝ} (ha : Measurable a) :
    BoundedSmoothFamily (fun t => F (a t)) := by
  have hmap : Measurable (fun p : ℝ × ℝ => (a p.1,p.2)) :=
    (ha.comp measurable_fst).prodMk (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
  refine ⟨hF.measurable.comp hmap, fun t => hF.regular (a t), ?_⟩
  intro n
  obtain ⟨C,hC⟩ := hF.bounds n
  exact ⟨C, fun t x => hC (a t) x⟩

def rescaleTimeField {T : ℝ} (F : TimeField T) (a : ℝ) (ha : 0 < a) : TimeField (T/a) where
  f := fun t x => F.f (a*t) x
  d := fun t x => a*F.d (a*t) x
  smooth := boundedSmoothFamily_time_comp F.smooth (measurable_const.mul measurable_id)
  rate_smooth := (boundedSmoothFamily_time_comp F.rate_smooth
    (measurable_const.mul measurable_id)).const_mul a
  continuous := by
    have hmap : Continuous (fun p : ℝ × ℝ => (a*p.1,p.2)) :=
      (continuous_const.mul continuous_fst).prodMk continuous_snd
    exact F.continuous.comp hmap
  rate_right := by
    intro t x
    have hmap : Tendsto (fun r : ℝ => a*r) (𝓝[>] t) (𝓝[>] (a*t)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuous_const.mul continuous_id).tendsto t |>.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_lt_mul_of_pos_left hr ha
    exact ((F.rate_right (a*t) x).tendsto.comp hmap).const_mul a
  time_deriv := by
    intro t ht0 htT x
    have hta : 0 ≤ a*t := mul_nonneg ha.le ht0
    have htaT : a*t < T := by
      have H := (lt_div_iff₀ ha).mp htT
      simpa only [mul_comm] using H
    have H := (F.time_deriv (a*t) hta htaT x).comp t
      (((hasDerivAt_id t).const_mul a).hasDerivWithinAt (s := Ioi t))
      (by intro r hr; exact mul_lt_mul_of_pos_left hr ha)
    simpa only [Function.comp_def, mul_one, mul_comm] using H

def physicalCDFJetField (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) : TimeField (T/(1/β^2)) :=
  rescaleTimeField (compactCDFJetField β α ha h1 hβ hT0 hT1 n) (1/β^2)
    (one_div_pos.mpr (sq_pos_of_ne_zero hβ))

end SKConstants.ParisiFullSupport

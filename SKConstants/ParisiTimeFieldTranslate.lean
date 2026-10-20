module

public import SKConstants.ParisiCDFExponential

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto

lemma boundedSmoothFamily_translate {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (a x0 : ℝ) :
    BoundedSmoothFamily (fun t x => F (a+t) (x0+x)) := by
  have hb : ∀ n : ℕ, ∃ C : ℝ≥0, ∀ t x,
      |iteratedDeriv n (fun x => F (a+t) (x0+x)) x| ≤ C := by
    intro n
    obtain ⟨C, hC⟩ := hF.bounds n
    refine ⟨C, fun t x => ?_⟩
    rw [iteratedDeriv_comp_const_add]
    exact hC (a+t) (x0+x)
  refine ⟨hF.measurable.comp (show Measurable (fun p : ℝ × ℝ => (a+p.1,x0+p.2)) from by fun_prop), ?_, hb⟩
  intro t
  refine ⟨(hF.regular (a+t)).smooth.comp (contDiff_const.add contDiff_id), ?_⟩
  intro n
  obtain ⟨C, hC⟩ := hb n
  exact ⟨C, hC t⟩

def constantTimeField (T c : ℝ) : TimeField T where
  f := fun _ _ => c
  d := fun _ _ => 0
  smooth := BoundedSmoothFamily.timeConst (C := Real.nnabs c) measurable_const (by simp)
  rate_smooth := BoundedSmoothFamily.timeConst (C := 0) measurable_const (by simp)
  continuous := continuous_const
  rate_right := fun _ _ => continuousWithinAt_const
  time_deriv := fun _ _ _ _ => hasDerivWithinAt_const _ _ _

lemma constantTimeField_generator (T c : ℝ) (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (constantTimeField T c).generator b t x = 0 := by
  simp [TimeField.generator, constantTimeField]

def translatedTimeField {T : ℝ} (F : TimeField T) (a x0 : ℝ) (ha : 0 ≤ a) :
    TimeField (T-a) where
  f := fun t x => F.f (a+t) (x0+x)
  d := fun t x => F.d (a+t) (x0+x)
  smooth := boundedSmoothFamily_translate F.smooth a x0
  rate_smooth := boundedSmoothFamily_translate F.rate_smooth a x0
  continuous := F.continuous.comp
    (show Continuous (fun p : ℝ × ℝ => (a+p.1,x0+p.2)) from by fun_prop)
  rate_right := by
    intro t x
    have hm : Tendsto (fun r : ℝ => a+r) (𝓝[>] t) (𝓝[>] (a+t)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuous_const.add continuous_id).tendsto t |>.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with r hr
      change t < r at hr
      change a+t < a+r
      linarith
    exact (F.rate_right (a+t) (x0+x)).tendsto.comp hm
  time_deriv := by
    intro t ht0 htT x
    have H := (F.time_deriv (a+t) (add_nonneg ha ht0) (by linarith) (x0+x)).comp t
      (((hasDerivAt_id t).const_add a).hasDerivWithinAt (s := Ioi t))
      (by intro r hr; change t < r at hr; change a+t < a+r; linarith)
    simpa only [Function.comp_def, add_zero, mul_one] using H

lemma translatedTimeField_generator {T : ℝ} (F : TimeField T) (a x0 : ℝ) (ha : 0 ≤ a)
    (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (translatedTimeField F a x0 ha).generator (fun r y => b (a+r) (x0+y)) t x =
      F.generator b (a+t) (x0+x) := by
  have he : deriv (fun x => F.f (a+t) (x0+x)) =
      fun x => deriv (F.f (a+t)) (x0+x) := funext fun x => deriv_comp_const_add _ _ x
  have he2 : deriv (deriv (fun x => F.f (a+t) (x0+x))) =
      fun x => deriv (deriv (F.f (a+t))) (x0+x) := by
    rw [he]
    exact funext fun x => deriv_comp_const_add _ _ x
  unfold TimeField.generator translatedTimeField
  dsimp only
  rw [he2, he]

def centeredTranslatedTimeField {T : ℝ} (F : TimeField T) (a x0 : ℝ) (ha : 0 ≤ a) :
    TimeField (T-a) :=
  (translatedTimeField F a x0 ha).add (constantTimeField (T-a) (-F.f a x0))

lemma centeredTranslatedTimeField_f {T : ℝ} (F : TimeField T)
    (a x0 : ℝ) (ha : 0 ≤ a) (t x : ℝ) :
    (centeredTranslatedTimeField F a x0 ha).f t x = F.f (a+t) (x0+x) - F.f a x0 := by
  simp only [centeredTranslatedTimeField, TimeField.add, translatedTimeField,
    constantTimeField, sub_eq_add_neg]

lemma centeredTranslatedTimeField_initial {T : ℝ} (F : TimeField T)
    (a x0 : ℝ) (ha : 0 ≤ a) : (centeredTranslatedTimeField F a x0 ha).f 0 0 = 0 := by
  rw [centeredTranslatedTimeField_f]
  simp

lemma centeredTranslatedTimeField_generator {T : ℝ} (F : TimeField T)
    (a x0 : ℝ) (ha : 0 ≤ a) (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (centeredTranslatedTimeField F a x0 ha).generator (fun r y => b (a+r) (x0+y)) t x =
      F.generator b (a+t) (x0+x) := by
  rw [centeredTranslatedTimeField, TimeField.generator_add, constantTimeField_generator,
    add_zero, translatedTimeField_generator]

lemma centeredTranslatedTimeField_spatial_deriv {T : ℝ} (F : TimeField T)
    (a x0 : ℝ) (ha : 0 ≤ a) (t x : ℝ) :
    deriv ((centeredTranslatedTimeField F a x0 ha).f t) x =
      deriv (F.f (a+t)) (x0+x) := by
  have he : (centeredTranslatedTimeField F a x0 ha).f t =
      fun x => F.f (a+t) (x0+x) - F.f a x0 := funext fun x =>
    centeredTranslatedTimeField_f F a x0 ha t x
  rw [he, deriv_sub_const, deriv_comp_const_add]

theorem centeredTranslatedTimeField_mgf
    {Ω : Type*} [MeasurableSpace Ω] {T : ℝ} (F : TimeField T)
    (a x0 : ℝ) (ha : 0 ≤ a) (b : ℝ → ℝ → ℝ)
    (b' : BoundedLipschitzDrift) (hb' : ∀ t x, b'.f t x = b (a+t) (x0+x))
    (W : BrownianSystem Ω) (v : ℝ≥0) (hv : a+(v : ℝ) < T) (θ : ℝ)
    (hbr : ∀ r ∈ Ico (0 : ℝ) (v : ℝ), ∀ᵐ w ∂W.law,
      ContinuousWithinAt (fun s => b'.pathDrift W s w) (Ioi r) r)
    (hgen : ∀ r ∈ Icc a (a+(v : ℝ)), ∀ x, F.generator b r x = 0)
    (hspatial : ∀ r ∈ Icc a (a+(v : ℝ)), ∀ x, |deriv (F.f r) x| ≤ 1) :
    (∫ w, Real.exp (θ * (F.f (a+(v : ℝ))
      (x0+b'.solution W.driver v w) - F.f a x0)) ∂W.law) ≤
        Real.exp (θ^2 * (v : ℝ) / 2) := by
  let G := centeredTranslatedTimeField F a x0 ha
  have H := exponentialTimeField_expected_le_of_generator_bounds G θ b' W v (θ^2/2)
    v.coe_nonneg (by linarith) (by positivity) hbr (by
      intro r hr x
      have hshift : a+r ∈ Icc a (a+(v : ℝ)) := by constructor <;> linarith [hr.1,hr.2]
      have hbf : b'.f = fun t x => b (a+t) (x0+x) := funext fun t => funext (hb' t)
      rw [exponentialTimeField_generator, hbf,
        centeredTranslatedTimeField_generator, hgen _ hshift,
        centeredTranslatedTimeField_spatial_deriv, mul_zero, zero_add]
      refine ⟨by positivity, ?_⟩
      have hs := hspatial _ hshift (x0+x)
      have hs2 : (deriv (F.f (a+r)) (x0+x))^2 ≤ 1 := by
        nlinarith [sq_abs (deriv (F.f (a+r)) (x0+x)), abs_nonneg (deriv (F.f (a+r)) (x0+x))]
      change (θ^2/2) * (deriv (F.f (a+r)) (x0+x))^2 * Real.exp (θ * G.f r x) ≤
        (θ^2/2) * Real.exp (θ * G.f r x)
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 (by positivity))
        (Real.exp_pos _).le).trans_eq (by ring))
  rw [centeredTranslatedTimeField_initial, mul_zero, Real.exp_zero, one_mul] at H
  simp only [TimeField.expected, Real.toNNReal_coe] at H
  change (∫ w, Real.exp (θ * G.f (v : ℝ) (b'.solution W.driver v w)) ∂W.law) ≤ _ at H
  have he : θ^2/2*(v : ℝ) = θ^2*(v : ℝ)/2 := by ring
  rw [he] at H
  simpa only [G, centeredTranslatedTimeField_f] using H

end SKConstants.ParisiFullSupport

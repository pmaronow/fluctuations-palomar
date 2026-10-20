module

public import SKConstants.ParisiEquilibriumMoments

@[expose] public section

/-!
First-order growth version of the expected time generator.  Adapted from
OpenAI math Regularity/IntegralTimeStep.lean and Foundations/RightGenerator.lean,
Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
The value need not be bounded; its spatial derivatives and time rate are bounded.
Integrability is proved from the actual Brownian state rather than postulated.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma integrable_regular_family_comp [IsFiniteMeasure P] {F : ℝ → ℝ → ℝ}
    (hF : ∀ t, ContDiff ℝ ∞ (F t))
    (hFd : BoundedSmoothFamily (fun t => deriv (F t))) (t : ℝ) {Y : Ω → ℝ}
    (hY : Integrable Y P) : Integrable (fun w => F t (Y w)) P := by
  obtain ⟨C,hC⟩ := hFd.bound
  exact integrable_comp_of_bounded_deriv ((hF t).differentiable (by simp)) C (hC t) hY

lemma expected_integral_time_step_regular {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0)
    {Y A : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) (hA : Measurable A) (M : ℝ≥0)
    (hAb : ∀ w, |A w| ≤ (M:ℝ)*(h:ℝ)) {F D : ℝ → ℝ → ℝ}
    (hF : ∀ t, ContDiff ℝ ∞ (F t))
    (hFd : BoundedSmoothFamily (fun t => deriv (F t))) (hD : BoundedSmoothFamily D)
    (C₁ C₂ C₃ L : ℝ≥0) (hC₁ : ∀ x, |deriv (F s) x| ≤ C₁)
    (hC₂ : ∀ x, |deriv (deriv (F s)) x| ≤ C₂)
    (hC₃ : ∀ x, |iteratedDeriv 3 (F s) x| ≤ C₃)
    (hL : ∀ r, LipschitzWith L (D r))
    (he : ∀ x, F ((s:ℝ)+(h:ℝ)) x-F s x = ∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r x) :
    |(∫ w, F ((s:ℝ)+(h:ℝ)) (Y w+(B (s+h) w-B s w)+A w) ∂P)-
      (∫ w, F s (Y w) ∂P)-(∫ w, deriv (F s) (Y w)*A w ∂P)-
      (h:ℝ)/2*(∫ w, deriv (deriv (F s)) (Y w) ∂P)-
      (∫ w, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y w)) ∂P)| ≤
      (C₃:ℝ)/6*((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment)+
      (C₂:ℝ)*(M:ℝ)*(h:ℝ)*(Real.sqrt (h:ℝ)*normalFirstMoment+(M:ℝ)*(h:ℝ))+
      (L:ℝ)*(h:ℝ)*(Real.sqrt (h:ℝ)*normalFirstMoment+(M:ℝ)*(h:ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  let Z (w : Ω) := Y w+(B (s+h) w-B s w)+A w
  have hZm : Measurable Z := (hYm.add ((hm _).sub (hm _))).add hA
  have hAi : Integrable A P := Integrable.of_bound hA.aestronglyMeasurable
    ((M:ℝ)*(h:ℝ)) (Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs] using hAb w))
  have hd : Integrable (fun w => B (s+h) w-B s w) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  have hZi : Integrable Z P := (hYi.add hd).add hAi
  let R (w : Ω) := F ((s:ℝ)+(h:ℝ)) (Z w)-F s (Z w)-
    ∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y w)
  have hiR : Integrable R P :=
    ((integrable_regular_family_comp hF hFd _ hZi).sub (integrable_regular_family_comp hF hFd _ hZi)).sub
      (integrable_family_integral_comp hD _ _ hYm)
  have hRb (w : Ω) : |R w| ≤ (L:ℝ)*(h:ℝ)*(|B (s+h) w-B s w|+(M:ℝ)*(h:ℝ)) := by
    dsimp only [R]
    rw [he]
    have hi := time_integral_spatial_bound hD hL (s:ℝ) ((s:ℝ)+(h:ℝ)) (Y w) (Z w)
    rw [add_sub_cancel_left,abs_of_nonneg h.coe_nonneg] at hi
    apply hi.trans
    have hz : |Z w-Y w| ≤ |B (s+h) w-B s w|+(M:ℝ)*(h:ℝ) := by
      have heq : Z w-Y w = (B (s+h) w-B s w)+A w := by dsimp [Z]; ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add_right (hAb w) _)
    exact mul_le_mul_of_nonneg_left hz (mul_nonneg L.coe_nonneg h.coe_nonneg)
  have hRe : |∫ w, R w ∂P| ≤
      (L:ℝ)*(h:ℝ)*(Real.sqrt (h:ℝ)*normalFirstMoment+(M:ℝ)*(h:ℝ)) := by
    calc
      _ ≤ ∫ w, |R w| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ w, (L:ℝ)*(h:ℝ)*(|B (s+h) w-B s w|+(M:ℝ)*(h:ℝ)) ∂P :=
        integral_mono hiR.abs ((hd.abs.add (integrable_const _)).const_mul _) hRb
      _ = _ := by
        rw [integral_const_mul,integral_add hd.abs (integrable_const _),increment_abs_first hB s h]
        simp
  have hRi : (∫ w, R w ∂P) =
      (∫ w, F ((s:ℝ)+(h:ℝ)) (Z w) ∂P)-(∫ w, F s (Z w) ∂P)-
      (∫ w, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y w)) ∂P) := by
    have h1 := integrable_regular_family_comp (P := P) hF hFd ((s:ℝ)+(h:ℝ)) hZi
    have h0 := integrable_regular_family_comp (P := P) hF hFd (s:ℝ) hZi
    have hdI := integrable_family_integral_comp (P := P) hD (s:ℝ) ((s:ℝ)+(h:ℝ)) hYm
    calc
      _ = (∫ w, F ((s:ℝ)+(h:ℝ)) (Z w)-F s (Z w) ∂P)-
          (∫ w, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y w)) ∂P) :=
        integral_sub (h1.sub h0) hdI
      _ = _ := by rw [integral_sub h1 h0]

  have hS := expected_control_step hB hm s h hY hYi hA M hAb
    ((hF s).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)) C₁ C₂ C₃ hC₁ hC₂ hC₃
  rw [hRi] at hRe
  have ht := (abs_add_le
    ((∫ w, F s (Z w) ∂P)-(∫ w, F s (Y w) ∂P)-
      (∫ w, deriv (F s) (Y w)*A w ∂P)-(h:ℝ)/2*(∫ w, deriv (deriv (F s)) (Y w) ∂P))
    ((∫ w, F ((s:ℝ)+(h:ℝ)) (Z w) ∂P)-(∫ w, F s (Z w) ∂P)-
      (∫ w, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y w)) ∂P))).trans
        (add_le_add hS hRe)
  convert ht using 1
  congr 1
  ring


theorem expected_hasDerivWithinAt_right_regular (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {F D : ℝ → ℝ → ℝ} (hF : ∀ t, ContDiff ℝ ∞ (F t))
    (hFd : BoundedSmoothFamily (fun t => deriv (F t))) (hD : BoundedSmoothFamily D)
    {T : ℝ} (he : ∀ a c, 0 ≤ a → a ≤ c → c ≤ T → ∀ x,
      F c x-F a x = ∫ r in a..c, D r x)
    (s : ℝ≥0) (hsT : (s:ℝ) < T)
    (hDr : ∀ x, ContinuousWithinAt (fun r => D r x) (Ioi (s:ℝ)) s)
    (hbr : ∀ᵐ w ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r w) (Ioi (s:ℝ)) s) :
    HasDerivWithinAt
      (fun t : ℝ => ∫ w, F t (b.solution W.driver (Real.toNNReal t) w) ∂W.law)
      ((∫ w, deriv (F s) (b.solution W.driver s w)*b.pathDrift W s w ∂W.law)+
        (1/2:ℝ)*(∫ w, deriv (deriv (F s)) (b.solution W.driver s w) ∂W.law)+
        (∫ w, D s (b.solution W.driver s w) ∂W.law)) (Ioi (s:ℝ)) s := by
  let := W.isProbability
  let Y := b.solution W.driver s
  have hYm : Measurable Y := b.solution_measurable W s
  obtain ⟨C₁,hC₁⟩ := hFd.bound
  obtain ⟨C₂,hC₂⟩ := hFd.deriv.bound
  obtain ⟨C₃,hC₃⟩ := hFd.bounds 2
  obtain ⟨Ct,hCt⟩ := hD.bound
  obtain ⟨L,hL⟩ := BoundedSmoothFamily_lipschitz hD
  let Q (t : ℝ) := ∫ w, F t (b.solution W.driver (Real.toNNReal t) w) ∂W.law
  let H : ℝ := ∫ w, deriv (deriv (F s)) (Y w) ∂W.law
  let A (t : ℝ) := ∫ w, deriv (F s) (Y w)*b.displacement W s t w ∂W.law
  let J (t : ℝ) := ∫ w, (∫ r in (s:ℝ)..t, D r (Y w)) ∂W.law
  let K (t : ℝ) := A t/(t-s)+(1/2:ℝ)*H+J t/(t-s)
  have hcoeff : Measurable (fun w => deriv (F s) (Y w)) :=
    ((hFd.regular s).smooth.continuous.measurable).comp hYm
  have hma : Measurable (fun p : ℝ × Ω => deriv (F s) (Y p.2)*b.pathDrift W p.1 p.2) :=
    (hcoeff.comp measurable_snd).mul (b.pathDrift_measurable W)
  have halim := expected_time_average_tendsto_right (P := W.law) hma
    (mul_nonneg C₁.coe_nonneg b.bound.coe_nonneg)
    (fun r w => by
      rw [abs_mul]
      exact mul_le_mul (hC₁ s (Y w)) (b.pathDrift_bound W r w) (abs_nonneg _) C₁.coe_nonneg)
    (s:ℝ) (by
      filter_upwards [hbr] with w hw
      exact continuousWithinAt_const.mul hw)
  have hAlim : Tendsto (fun t => A t/(t-s)) (𝓝[>] (s:ℝ))
      (𝓝 (∫ w, deriv (F s) (Y w)*b.pathDrift W s w ∂W.law)) := by
    convert halim using 1
    funext t
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [] with w
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hmj : Measurable (fun p : ℝ × Ω => D p.1 (Y p.2)) :=
    hD.measurable.comp (measurable_fst.prodMk (hYm.comp measurable_snd))
  have hjlim := expected_time_average_tendsto_right (P := W.law) hmj Ct.coe_nonneg
    (fun r w => hCt r (Y w)) (s:ℝ) (Eventually.of_forall (fun w => hDr (Y w)))
  have hJlim : Tendsto (fun t => J t/(t-s)) (𝓝[>] (s:ℝ))
      (𝓝 (∫ w, D s (Y w) ∂W.law)) := by
    convert hjlim using 1
    funext t
    exact (integral_div (t-(s:ℝ)) _).symm
  have hKlim := (hAlim.add_const ((1/2:ℝ)*H)).add hJlim
  let E (t : ℝ) := (C₃:ℝ)/6*(Real.sqrt (t-s)*normalThirdMoment)+
    (C₂:ℝ)*(b.bound:ℝ)*(Real.sqrt (t-s)*normalFirstMoment+(b.bound:ℝ)*(t-s))+
    (L:ℝ)*(Real.sqrt (t-s)*normalFirstMoment+(b.bound:ℝ)*(t-s))
  have hzero : Tendsto (fun t : ℝ => t-(s:ℝ)) (𝓝[>] (s:ℝ)) (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => t) (𝓝[>] (s:ℝ)) (𝓝 (s:ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using hh.sub_const (s:ℝ)
  have hsqrt := hzero.sqrt
  have hElim : Tendsto E (𝓝[>] (s:ℝ)) (𝓝 0) := by
    have hbase := (hsqrt.mul_const normalFirstMoment).add (hzero.const_mul (b.bound:ℝ))
    simpa only [E,Real.sqrt_zero,zero_mul,mul_zero,add_zero] using
      (((hsqrt.mul_const normalThirdMoment).const_mul ((C₃:ℝ)/6)).add
        (hbase.const_mul ((C₂:ℝ)*(b.bound:ℝ)))).add (hbase.const_mul (L:ℝ))
  have hbound : ∀ᶠ t in 𝓝[>] (s:ℝ), |slope Q s t-K t| ≤ E t := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hsT)] with t hst htT
    have hp : 0 < t-(s:ℝ) := sub_pos.mpr hst
    let h := Real.toNNReal (t-(s:ℝ))
    have hcoe : (h:ℝ)=t-(s:ℝ) := Real.coe_toNNReal _ hp.le
    have htime : (s:ℝ)+(h:ℝ)=t := by rw [hcoe]; ring
    have hnn : s+h=Real.toNNReal t := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add,htime,Real.coe_toNNReal _ (s.coe_nonneg.trans hst.le)]
    have hstep := expected_integral_time_step_regular W.brownian.toIsPreBrownianReal W.measurable s h
      (b.solution_adapted W s) (b.solution_integrable W s)
      (b.displacement_measurable W s (s+h)) b.bound
      (fun w => by
        have hb := b.displacement_bound W (s:ℝ) ((s+h:ℝ≥0):ℝ) w
        simpa only [NNReal.coe_add,add_sub_cancel_left,abs_of_nonneg h.coe_nonneg] using hb)
      hF hFd hD C₁ C₂ C₃ L (hC₁ s) (hC₂ s) (by simpa only [iteratedDeriv_succ',iteratedDeriv_one] using hC₃ s) hL
      (he s ((s:ℝ)+(h:ℝ)) s.coe_nonneg (by linarith [h.coe_nonneg]) (by rw [htime]; exact htT.le))
    have hsol : (∫ w, F ((s:ℝ)+(h:ℝ))
        (b.solution W.driver s w+(W.B (s+h) w-W.B s w)+b.displacement W s (s+h) w) ∂W.law) = Q t := by
      unfold Q
      apply integral_congr_ae
      filter_upwards [b.solution_increment W s h] with w hw
      rw [← hw,hnn,htime]
    rw [hsol] at hstep
    have hqs : (∫ w, F s (b.solution W.driver s w) ∂W.law) = Q s := by simp only [Q,Real.toNNReal_coe]
    rw [hqs] at hstep
    have hat : (∫ w, deriv (F s) (b.solution W.driver s w)*b.displacement W s (s+h) w ∂W.law) = A t := by
      simp only [A,Y,htime]
    rw [hat,htime,hcoe] at hstep
    change |Q t-Q s-A t-(t-(s:ℝ))/2*H-J t| ≤ _ at hstep
    have heq : slope Q s t-K t = (Q t-Q s-A t-(t-(s:ℝ))/2*H-J t)/(t-s) := by
      rw [slope_def_field]
      dsimp only [K]
      field_simp
      ring
    rw [heq,abs_div,abs_of_pos hp,div_le_iff₀ hp]
    convert hstep using 1
    all_goals try dsimp only [E]
    all_goals first | rfl | ring
  have herr : Tendsto (fun t => slope Q s t-K t) (𝓝[>] (s:ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hElim
    simpa only [Real.norm_eq_abs] using hbound
  have hh := herr.add hKlim
  apply (hasDerivWithinAt_iff_tendsto_slope' (show (s:ℝ) ∉ Ioi (s:ℝ) by simp)).mpr
  convert hh using 1
  · funext t
    dsimp only [K] at *
    ring
  · simp only [zero_add,H,Y]

end SKConstants.ParisiFullSupport

module

public import SKConstants.ParisiCDFBrownianMoments
public import Mathlib.Analysis.ODE.Gronwall
public import SKConstants.Upstream.OAI.Probability.SKSupport.Regularity.IntegralTimeStep
public import SKConstants.Upstream.OAI.Probability.SKSupport.Diffusion.FiniteTransition
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFEndpoint

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.SK.Analytic

lemma boundedSmoothFamily_exp_weights {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (θ : ℝ) (n : ℕ) :
    ∃ G : ℝ → ℝ → ℝ, BoundedSmoothFamily G ∧
      ∀ t, iteratedDeriv n (fun x => Real.exp (θ * F t x)) =
        fun x => G t x * Real.exp (θ * F t x) := by
  induction n with
  | zero =>
    refine ⟨fun _ _ => 1,
      BoundedSmoothFamily.timeConst measurable_const (C := 1) (by simp), ?_⟩
    intro t
    simp
  | succ n ih =>
    obtain ⟨G, hG, he⟩ := ih
    refine ⟨fun t x => deriv (G t) x + θ * G t x * deriv (F t) x,
      hG.deriv.add ((hG.const_mul θ).mul hF.deriv), ?_⟩
    intro t
    rw [iteratedDeriv_succ, he]
    exact deriv_weightExp ⟨(hF.regular t).smooth, (hF.regular t).deriv⟩ (hG.regular t) θ

lemma boundedSmoothFamily_exp {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (θ : ℝ) :
    BoundedSmoothFamily (fun t x => Real.exp (θ * F t x)) := by
  obtain ⟨C, hC⟩ := hF.bound
  have hb : ∀ t x, Real.exp (θ * F t x) ≤ Real.exp (|θ| * C) := by
    intro t x
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans ((abs_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (hC t x) (abs_nonneg θ)))
  have hbounds : ∀ n : ℕ, ∃ A : ℝ≥0, ∀ t x,
      |iteratedDeriv n (fun x => Real.exp (θ * F t x)) x| ≤ A := by
    intro n
    obtain ⟨G, hG, he⟩ := boundedSmoothFamily_exp_weights hF θ n
    obtain ⟨A, hA⟩ := hG.bound
    refine ⟨A * Real.toNNReal (Real.exp (|θ| * C)), ?_⟩
    intro t x
    rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
    simpa only [NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le] using
      mul_le_mul (hA t x) (hb t x) (Real.exp_pos _).le A.coe_nonneg
  refine ⟨(measurable_const.mul hF.measurable).exp, ?_, hbounds⟩
  intro t
  refine ⟨(contDiff_const.mul (hF.regular t).smooth).exp, ?_⟩
  intro n
  obtain ⟨A, hA⟩ := hbounds n
  exact ⟨A, hA t⟩

def exponentialTimeField {T : ℝ} (F : TimeField T) (θ : ℝ) : TimeField T where
  f := fun t x => Real.exp (θ * F.f t x)
  d := fun t x => θ * F.d t x * Real.exp (θ * F.f t x)
  smooth := boundedSmoothFamily_exp F.smooth θ
  rate_smooth := (F.rate_smooth.const_mul θ).mul (boundedSmoothFamily_exp F.smooth θ)
  continuous := Real.continuous_exp.comp (continuous_const.mul F.continuous)
  rate_right := by
    intro t x
    have hc : Continuous (fun r => Real.exp (θ * F.f r x)) :=
      Real.continuous_exp.comp
        (continuous_const.mul (F.continuous.comp (continuous_id.prodMk continuous_const)))
    exact (continuousWithinAt_const.mul (F.rate_right t x)).mul hc.continuousWithinAt
  time_deriv := by
    intro t ht0 htT x
    convert ((F.time_deriv t ht0 htT x).const_mul θ).exp using 1
    ring

lemma exponentialTimeField_generator {T : ℝ} (F : TimeField T) (θ : ℝ)
    (b : ℝ → ℝ → ℝ) (t x : ℝ) :
    (exponentialTimeField F θ).generator b t x =
      θ * Real.exp (θ * F.f t x) * F.generator b t x +
        (θ ^ 2 / 2) * (deriv (F.f t) x) ^ 2 * Real.exp (θ * F.f t x) := by
  have hf : RegularDatum (F.f t) := ⟨(F.smooth.regular t).smooth, (F.smooth.regular t).deriv⟩
  unfold TimeField.generator exponentialTimeField
  dsimp only
  rw [deriv_deriv_exp_comp hf θ, deriv_exp_comp hf θ]
  simp only [generatorWeight]
  ring

lemma compactCDFJet_one_abs_le_one (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) {T : ℝ} (hT0 : 0 ≤ T)
    (_hT1 : T ≤ 1) (t x : ℝ) : |compactCDFJet β α T 1 t x| ≤ 1 := by
  have hr := cdfStripTime_mem hT0 t
  have hvar : Real.toNNReal (1 - cdfStripTime T t) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hr.1]
  unfold compactCDFJet compactCDFGradient
  rw [iteratedDeriv_one,
    (scalarCDFGradient_hasDerivAt β ha α.mono _ _ hvar x).deriv]
  exact scalarCDFHessian_abs_le_one β ha α.mono _ _ hvar x

lemma physicalCDF_exponential_generator (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (θ t x : ℝ) :
    (exponentialTimeField (physicalCDFJetField β α ha h1 hβ hT0 hT1 0) θ).generator
      (physicalCDFCompactDrift β α T) t x =
      (θ ^ 2 / 2) * (compactCDFJet β α T 1 (t / β ^ 2) x) ^ 2 *
        Real.exp (θ * compactCDFJet β α T 0 (t / β ^ 2) x) := by
  rw [exponentialTimeField_generator, physicalCDFGradient_generator_zero β α ha h1 hβ hT0 hT1]
  simp only [mul_zero, zero_add]
  change (θ ^ 2 / 2) * (deriv (compactCDFJet β α T 0 ((1 / β^2)*t)) x) ^ 2 *
    Real.exp (θ * compactCDFJet β α T 0 ((1 / β^2)*t) x) = _
  rw [deriv_compactCDFJet β α ha h1 hβ hT0 hT1]
  rw [show (1 / β^2)*t=t/β^2 by ring]

lemma physicalCDF_exponential_generator_bounds (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (θ t x : ℝ) :
    let F := exponentialTimeField (physicalCDFJetField β α ha h1 hβ hT0 hT1 0) θ
    0 ≤ F.generator (physicalCDFCompactDrift β α T) t x ∧
      F.generator (physicalCDFCompactDrift β α T) t x ≤ (θ ^ 2 / 2) * F.f t x := by
  dsimp only
  rw [physicalCDF_exponential_generator β α ha h1 hβ hT0 hT1]
  refine ⟨by positivity, ?_⟩
  have hsq : (compactCDFJet β α T 1 (t / β^2) x)^2 ≤ 1 := by
    have h := compactCDFJet_one_abs_le_one β α ha hT0 hT1.le (t / β^2) x
    nlinarith [sq_abs (compactCDFJet β α T 1 (t / β^2) x), abs_nonneg (compactCDFJet β α T 1 (t / β^2) x)]
  change (θ ^ 2 / 2) * (compactCDFJet β α T 1 (t / β^2) x)^2 *
    Real.exp (θ * compactCDFJet β α T 0 (t / β^2) x) ≤
      (θ ^ 2 / 2) * Real.exp (θ * compactCDFJet β α T 0 ((1/β^2)*t) x)
  rw [show (1 / β^2)*t=t/β^2 by ring]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity))
    (Real.exp_pos _).le |>.trans_eq (by ring)

theorem exponentialTimeField_expected_le_of_generator_bounds
    {Ω : Type*} [MeasurableSpace Ω] {T : ℝ} (F : TimeField T)
    (θ : ℝ) (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)
    (v K : ℝ) (hv0 : 0 ≤ v) (hvT : v < T) (_hK : 0 ≤ K)
    (hbr : ∀ r ∈ Ico (0 : ℝ) v, ∀ᵐ w ∂W.law,
      ContinuousWithinAt (fun s => b.pathDrift W s w) (Ioi r) r)
    (hgen : ∀ r ∈ Icc (0 : ℝ) v, ∀ x,
      0 ≤ (exponentialTimeField F θ).generator b.f r x ∧
      (exponentialTimeField F θ).generator b.f r x ≤
        K * (exponentialTimeField F θ).f r x) :
    (exponentialTimeField F θ).expected b W v ≤ Real.exp (θ * F.f 0 0) * Real.exp (K * v) := by
  let := W.isProbability
  let E := exponentialTimeField F θ
  let f := E.expected b W
  let d := fun r => ∫ w, E.generator b.f r
    (b.solution W.driver (Real.toNNReal r) w) ∂W.law
  have hfpos : ∀ r, 0 ≤ f r := fun r => integral_nonneg fun w => (Real.exp_pos _).le
  have hderiv : ∀ r ∈ Ico (0 : ℝ) v, HasDerivWithinAt f (d r) (Ici r) r := by
    intro r hr
    have H := E.expected_hasDerivWithinAt_right b W (Real.toNNReal r)
      (by simpa only [Real.coe_toNNReal r hr.1] using hr.2.trans hvT)
      (by simpa only [Real.coe_toNNReal r hr.1] using hbr r hr)
    simpa only [Real.coe_toNNReal r hr.1] using H.Ici_of_Ioi
  have hbound : ∀ r ∈ Ico (0 : ℝ) v, ‖d r‖ ≤ K * ‖f r‖ + 0 := by
    intro r hr
    have hi := integrable_family_comp (P := W.law) E.smooth r
      (b.solution_measurable W (Real.toNNReal r))
    have hgm : Measurable (fun x => E.generator b.f r x) := by
      have hm1 := (E.smooth.deriv.regular r).smooth.continuous.measurable
      have hm2 := (E.smooth.deriv.deriv.regular r).smooth.continuous.measurable
      have hm3 := (E.rate_smooth.regular r).smooth.continuous.measurable
      have hmb : Measurable (b.f r) := b.measurable.comp measurable_prodMk_left
      exact ((hm1.mul hmb).add (measurable_const.mul hm2)).add hm3
    have hg : Integrable (fun w => E.generator b.f r
        (b.solution W.driver (Real.toNNReal r) w)) W.law := by
      apply (hi.const_mul K).mono'
        (hgm.comp (b.solution_measurable W (Real.toNNReal r))).aestronglyMeasurable
      filter_upwards with w
      change |E.generator b.f r (b.solution W.driver (Real.toNNReal r) w)| ≤ _
      rw [abs_of_nonneg (show 0 ≤ E.generator b.f r
        (b.solution W.driver (Real.toNNReal r) w) from (hgen r ⟨hr.1, hr.2.le⟩ _).1)]
      exact (hgen r ⟨hr.1, hr.2.le⟩ _).2
    have hdpos : 0 ≤ d r := integral_nonneg fun w => (hgen r ⟨hr.1, hr.2.le⟩ _).1
    have hdle : d r ≤ K * f r := by
      dsimp only [d, f, TimeField.expected]
      rw [← integral_const_mul]
      exact integral_mono hg (hi.const_mul K) fun w => (hgen r ⟨hr.1, hr.2.le⟩ _).2
    simpa only [Real.norm_eq_abs, abs_of_nonneg hdpos, abs_of_nonneg (hfpos r), add_zero] using hdle
  have hinit : f 0 = Real.exp (θ * F.f 0 0) := by
    unfold f TimeField.expected
    simp only [Real.toNNReal_zero, b.solution_zero W, E, exponentialTimeField,
      integral_const, probReal_univ, smul_eq_mul, one_mul]
  have H := norm_le_gronwallBound_of_norm_deriv_right_le
    (E.expected_continuous b W).continuousOn hderiv
    (δ := Real.exp (θ * F.f 0 0)) (K := K) (ε := 0)
    (by change ‖f 0‖ ≤ _; rw [hinit, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])
    hbound v ⟨hv0, le_rfl⟩
  change ‖f v‖ ≤ _ at H
  rw [Real.norm_eq_abs, abs_of_nonneg (hfpos v), sub_zero, gronwallBound_ε0] at H
  exact H

set_option backward.isDefEq.respectTransparency true in
theorem physicalCDFGradient_initial_mgf
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (v : ℝ≥0) (hv : (v : ℝ) / β^2 < T) (θ : ℝ) :
    (∫ w, Real.exp (θ * compactCDFJet β α T 0 ((v : ℝ)/β^2)
      (finiteTemperatureCDFProcess W β α ha h1 v w)) ∂W.law) ≤
        Real.exp (θ^2 * (v : ℝ) / 2) := by
  let F := physicalCDFJetField β α ha h1 hβ hT0 hT1 0
  let b := finiteTemperatureCDFDrift β α ha h1
  have hvT : (v : ℝ) < T / (1/β^2) := by
    simp only [one_div, div_inv_eq_mul]
    exact (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mp hv
  have hbr : ∀ r ∈ Ico (0 : ℝ) (v : ℝ), ∀ᵐ w ∂W.law,
      ContinuousWithinAt (fun s => b.pathDrift W s w) (Ioi r) r := by
    intro r hr
    have H := (finiteTemperatureCDFDrift_path_right_continuous W β α ha h1).mono
      (fun w hw => hw (Real.toNNReal r))
    simpa only [Real.coe_toNNReal r hr.1] using H
  have hgen : ∀ r ∈ Icc (0 : ℝ) (v : ℝ), ∀ x,
      0 ≤ (exponentialTimeField F θ).generator b.f r x ∧
      (exponentialTimeField F θ).generator b.f r x ≤
        (θ^2/2) * (exponentialTimeField F θ).f r x := by
    intro r hr x
    have hrT : r / β^2 ∈ Icc (0 : ℝ) T := ⟨div_nonneg hr.1 (sq_nonneg β),
      (div_le_div_of_nonneg_right hr.2 (sq_nonneg β)).trans hv.le⟩
    have hbf : b.f r = physicalCDFCompactDrift β α T r := by
      funext z
      exact finiteTemperatureCDFDrift_eq_compact β α ha h1 hβ hT1.le hrT z
    have he : (exponentialTimeField F θ).generator b.f r x =
        (exponentialTimeField F θ).generator (physicalCDFCompactDrift β α T) r x := by
      unfold TimeField.generator
      rw [hbf]
    rw [he]
    exact physicalCDF_exponential_generator_bounds β α ha h1 hβ hT0 hT1 θ r x
  have H := exponentialTimeField_expected_le_of_generator_bounds F θ b W v (θ^2/2)
    v.coe_nonneg hvT (by positivity) hbr hgen
  have hzero : F.f 0 0 = 0 := by
    change compactCDFJet β α T 0 ((1/β^2)*0) 0 = 0
    simpa only [mul_zero, compactCDFJet, iteratedDeriv_zero, compactCDFGradient,
      cdfStripTime, min_eq_left hT0, max_self, sub_zero, Real.toNNReal_one] using
      (scalarCDFGradient_zero β ha α.mono 0 1 le_rfl)
  have hrhs : Real.exp (θ * F.f 0 0) * Real.exp ((θ^2/2)*(v : ℝ)) =
      Real.exp ((θ^2/2)*(v : ℝ)) := by
    rw [hzero, mul_zero, Real.exp_zero, one_mul]
  have H1 := H.trans_eq hrhs
  simp only [TimeField.expected, Real.toNNReal_coe] at H1
  change (∫ w, Real.exp (θ * compactCDFJet β α T 0 ((1/β^2)*(v : ℝ))
    (finiteTemperatureCDFProcess W β α ha h1 v w)) ∂W.law) ≤ _ at H1
  have ht : (1/β^2)*(v : ℝ) = (v : ℝ)/β^2 := by ring
  have he : θ^2/2*(v : ℝ) = θ^2*(v : ℝ)/2 := by ring
  simpa only [ht, he] using H1

end SKConstants.ParisiFullSupport

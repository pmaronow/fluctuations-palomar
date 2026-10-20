module

public import SKBarriers2.Analysis.QSmooth
public import OAI.Probability.SKBarriers.Scalar.VectorAverageAlgebra
public import OAI.Probability.SKBarriers.Scalar.ScalarMassStability
public import OAI.Probability.SKBarriers.Gaussian.GaussianTiltedCramer

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def stepLaw (m : ℝ) (v : E) (f : E → ℝ) (x : E) : Measure ℝ :=
  gaussianStepLaw m (f ∘ vectorTranslation v) x

def noiseMean (m : ℝ) (v : E) (f : E → ℝ) (x : E) (g : ℝ → ℝ) : ℝ :=
  ∫ t, g t ∂stepLaw m v f x

def stepEntropy (m : ℝ) (v : E) (f : E → ℝ) (x : E) : ℝ :=
  m * (noiseMean m v f x (fun t => f (x + t • v)) - vectorStep m v f x)

variable {r : ℕ} {B : ℝ} {f : E → ℝ}

theorem stepLaw_probability (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) : IsProbabilityMeasure (stepLaw m v f x) := by
  exact gaussianStepLaw_probability ((hf.boundedDerivs hr).compCLM (vectorTranslation v)) m x

theorem abs_noiseMean_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) {g : ℝ → ℝ} {C : ℝ} (hg : ∀ t, |g t| ≤ C) :
    |noiseMean m v f x g| ≤ C := by
  let _ := stepLaw_probability hf hr m v x
  simpa only [noiseMean, Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := stepLaw m v f x)
      (ae_of_all _ (fun t => show ‖g t‖ ≤ C from hg t)))

theorem hasDerivAt_mass (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ≠ 0) (v x : E) :
    HasDerivAt (fun a => vectorStep a v f x) (stepEntropy m v f x / m ^ 2) m := by
  have H := gaussianStep_hasDerivAt_mass_ne_zero
    ((hf.boundedDerivs hr).compCLM (vectorTranslation v)) x hm
  convert! H using 1
  unfold stepEntropy
  change m * (noiseMean m v f x (fun t => f (x + t • v)) - vectorStep m v f x) / m ^ 2 =
    (noiseMean m v f x (fun t => f (x + t • v)) - vectorStep m v f x) / m
  field_simp

theorem fderiv_step_apply (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x w : E) :
    fderiv ℝ (vectorStep m v f) x w =
      noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) w) := by
  have hd : Differentiable ℝ f := (hf.boundedDerivs hr).1.differentiable (by norm_num)
  have H := fderiv_gaussianStep_apply ((hf.boundedDerivs hr).compCLM (vectorTranslation v)) m x w
  change fderiv ℝ (vectorStep m v f) x w = _ at H
  rw [H]
  change (∫ t, prefixGradient (f ∘ vectorTranslation v) w (x,t) ∂stepLaw m v f x) = _
  apply integral_congr_ae
  filter_upwards [] with t
  rw [prefixGradient, (hd ((vectorTranslation v) (x,t))).hasFDerivAt.comp
    (x,t) (vectorTranslation v).hasFDerivAt |>.fderiv]
  simp only [ContinuousLinearMap.comp_apply, vectorTranslation, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smulRight_apply, zero_smul, add_zero]

theorem abs_fderiv_step_apply_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x w : E) :
    |fderiv ℝ (vectorStep m v f) x w| ≤ B * ‖w‖ := by
  rw [fderiv_step_apply hf hr]
  exact abs_noiseMean_le hf hr m v x (fun t => hf.directional_le (by omega) (x + t • v) w)

theorem abs_step_le (hf : QBddSmooth r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : 0 ≤ m) (v x : E) : |vectorStep m v f x| ≤ B := by
  have hb := (hf.potential.boundedDerivs hr).compCLM (vectorTranslation v)
  have hlo := gaussianStep_mono (boundedDerivs_constant (-B)) hb hm
    (fun z => (abs_le.mp (hf.abs_le ((vectorTranslation v) z))).1) x
  have hhi := gaussianStep_mono hb (boundedDerivs_constant B) hm
    (fun z => (abs_le.mp (hf.abs_le ((vectorTranslation v) z))).2) x
  have hc (c : ℝ) : gaussianStep m (fun _ : E × ℝ => c) x = c :=
    congrFun (gaussianStep_prefix (fun _ : E => c) m) x
  rw [hc] at hlo hhi
  exact abs_le.mpr ⟨hlo, hhi⟩

theorem norm_fderiv_step_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) : ‖fderiv ℝ (vectorStep m v f) x‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hf.nonneg
  intro w
  exact abs_fderiv_step_apply_le hf hr m v x w

theorem qbddSmooth_one_step (hf : QBddSmooth r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : 0 ≤ m) (v : E) : QBddSmooth 1 B (vectorStep m v f) := by
  refine ⟨hf.nonneg, (vectorStep_regular (hf.potential.boundedDerivs hr) m v).1.of_le (by norm_num), ?_⟩
  intro j hj x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h | h
  · subst j
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using abs_step_le hf hr hm v x
  · subst j
    simpa only [norm_iteratedFDeriv_one] using norm_fderiv_step_le hf.potential hr m v x

private theorem growth_line {F : E → ℝ} (hF : HasExpGrowth F) (x v : E) :
    HasExpGrowth (fun t : ℝ => F (x + t • v)) := by
  obtain ⟨C,M,hC,hM,hbound⟩ := hF
  refine ⟨C * Real.exp (M * ‖x‖), M * ‖v‖, by positivity, by positivity, ?_⟩
  intro t
  apply (hbound (x + t • v)).trans
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  calc
    M * ‖x + t • v‖ ≤ M * (‖x‖ + ‖t • v‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hM
    _ = M * ‖x‖ + M * ‖v‖ * ‖t‖ := by rw [norm_smul]; ring

private theorem line_hasDerivAt (hf : ContDiff ℝ 1 f) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t := by
  have hv : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    convert! (((hasDerivAt_id t).smul_const v).const_add x) using 1
    simp only [one_smul]
  exact (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hv

private theorem line_first_hasDerivAt (hf : ContDiff ℝ 2 f) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v)
      (fderiv ℝ (fderiv ℝ f) (x + t • v) v v) t := by
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    (x + t • v)).hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const v).const_add x)
  convert! hd.clm_apply (hasDerivAt_const t v) using 1
  simp only [Function.comp_def, id_eq, one_smul, map_zero, add_zero]

private theorem exp_growth (hf : QPotential r B f) (hr : 2 ≤ r) (m : ℝ) (x v : E) :
    HasExpGrowth (fun t : ℝ => Real.exp (m * f (x + t • v))) := by
  exact growth_line (exp_mul_growth_of_fderiv_bound f
    ((hf.boundedDerivs hr).1.differentiable (by norm_num)) B hf.nonneg
    (hf.fderiv_le (by omega)) m) x v

private theorem first_continuous (hf : QPotential r B f) (hr : 2 ≤ r) (x v : E) :
    Continuous (fun t : ℝ => fderiv ℝ f (x + t • v) v) := by
  exact (((hf.boundedDerivs hr).1.continuous_fderiv (by norm_num)).comp
    (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

private theorem first_growth (hf : QPotential r B f) (hr : 2 ≤ r) (x v : E) :
    HasExpGrowth (fun t : ℝ => fderiv ℝ f (x + t • v) v) := by
  exact HasExpGrowth.of_bounded (mul_nonneg hf.nonneg (norm_nonneg v))
    (fun t => hf.directional_le (by omega) (x + t • v) v)

theorem integrable_noise (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) {g : ℝ → ℝ} (hg : HasExpGrowth g) (hc : Continuous g) :
    Integrable g (stepLaw m v f x) := by
  exact hg.integrable_gaussianTilt (exp_growth hf hr m x v)
    (continuous_const.mul ((hf.boundedDerivs hr).1.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const)))) hc

theorem tilted_integration_by_parts (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) {g g' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hgc : Continuous g')
    (hgg : HasExpGrowth g) (hgg' : HasExpGrowth g') :
    noiseMean m v f x (fun t => t * g t) = noiseMean m v f x g' +
      m * noiseMean m v f x (fun t => g t * fderiv ℝ f (x + t • v) v) := by
  have hV (t : ℝ) : HasDerivAt (fun s : ℝ => m * f (x + s • v))
      (m * fderiv ℝ f (x + t • v) v) t :=
    (line_hasDerivAt ((hf.boundedDerivs hr).1.of_le (by norm_num)) x v t).const_mul m
  have hmg : HasExpGrowth (fun t : ℝ => m * fderiv ℝ f (x + t • v) v) :=
    HasExpGrowth.of_bounded (mul_nonneg (abs_nonneg m) (mul_nonneg hf.nonneg (norm_nonneg v)))
      (fun t => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hf.directional_le (by omega) (x + t • v) v) (abs_nonneg m))
  have H := gaussian_tilted_stein_growth hV hg (exp_growth hf hr m x v) hmg hgg hgg'
    (continuous_const.mul (first_continuous hf hr x v)) hgc
  change noiseMean m v f x (fun t => t * g t) = noiseMean m v f x g' +
    noiseMean m v f x (fun t => g t * (m * fderiv ℝ f (x + t • v) v)) at H
  rw [H]
  congr 1
  unfold noiseMean
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring_nf

theorem noise_first (hf : QPotential r B f) (hr : 2 ≤ r) (m : ℝ) (v x : E) :
    noiseMean m v f x (fun t => t) =
      m * noiseMean m v f x (fun t => fderiv ℝ f (x + t • v) v) := by
  have H := tilted_integration_by_parts hf hr m v x
    (fun t => hasDerivAt_const t (1 : ℝ)) continuous_const
    (HasExpGrowth.of_bounded (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by norm_num))
    (HasExpGrowth.of_bounded (by norm_num : (0 : ℝ) ≤ 0) (fun _ => by norm_num))
  simpa only [mul_one, one_mul, noiseMean, integral_zero, zero_add] using H

theorem abs_noise_first_le (hf : QPotential r B f) (hr : 2 ≤ r) (m : ℝ) (v x : E) :
    |noiseMean m v f x (fun t => t)| ≤ |m| * B * ‖v‖ := by
  rw [noise_first hf hr, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (abs_noiseMean_le hf hr m v x
      (fun t => hf.directional_le (by omega) (x + t • v) v)) (abs_nonneg m)

private theorem second_continuous (hf : QPotential r B f) (hr : 2 ≤ r) (x v : E) :
    Continuous (fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x + t • v) v v) := by
  exact ((((hf.boundedDerivs hr).1.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
    (by norm_num)).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
    continuous_const |>.clm_apply continuous_const

private theorem second_growth (hf : QPotential r B f) (hr : 2 ≤ r) (x v : E) :
    HasExpGrowth (fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x + t • v) v v) := by
  exact HasExpGrowth.of_bounded (mul_nonneg (mul_nonneg hf.nonneg (norm_nonneg v)) (norm_nonneg v))
    (fun t => hf.second_directional_le hr (x + t • v) v v)

theorem noise_second (hf : QPotential r B f) (hr : 2 ≤ r) (m : ℝ) (v x : E) :
    noiseMean m v f x (fun t => t ^ 2) = 1 +
      m * noiseMean m v f x (fun t => fderiv ℝ (fderiv ℝ f) (x + t • v) v v) +
      m ^ 2 * noiseMean m v f x (fun t => (fderiv ℝ f (x + t • v) v) ^ 2) := by
  let _ := stepLaw_probability hf hr m v x
  have H := tilted_integration_by_parts hf hr m v x (fun t => hasDerivAt_id t)
    continuous_const (HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ))
    (HasExpGrowth.of_bounded (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by norm_num))
  have H' := tilted_integration_by_parts hf hr m v x
    (line_first_hasDerivAt (hf.boundedDerivs hr).1 x v) (second_continuous hf hr x v)
    (first_growth hf hr x v) (second_growth hf hr x v)
  change noiseMean m v f x (fun t => t * fderiv ℝ f (x + t • v) v) = _ at H'
  have hone : noiseMean m v f x (fun _ => (1 : ℝ)) = 1 := by simp only [noiseMean, integral_const, probReal_univ, one_smul]
  simp only [id_eq, ← pow_two, hone] at H
  rw [H, H']
  ring_nf

theorem abs_noise_second_sub_one_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v x : E) :
    |noiseMean m v f x (fun t => t ^ 2) - 1| ≤ (|m| * B + m ^ 2 * B ^ 2) * ‖v‖ ^ 2 := by
  have hsecond := abs_noiseMean_le hf hr m v x
    (fun t => hf.second_directional_le hr (x + t • v) v v)
  have hsquare : |noiseMean m v f x (fun t => (fderiv ℝ f (x + t • v) v) ^ 2)| ≤
      (B * ‖v‖) ^ 2 := by
    apply abs_noiseMean_le hf hr m v x
    intro t
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hf.nonneg (norm_nonneg v))).mpr
      (hf.directional_le (by omega) (x + t • v) v)
  rw [noise_second hf hr]
  have he (a b : ℝ) : 1 + a + b - 1 = a + b := by ring
  rw [he]
  calc
    _ ≤ |m * noiseMean m v f x (fun t => fderiv ℝ (fderiv ℝ f) (x + t • v) v v)| +
        |m ^ 2 * noiseMean m v f x (fun t => (fderiv ℝ f (x + t • v) v) ^ 2)| := abs_add_le _ _
    _ ≤ |m| * (B * ‖v‖ * ‖v‖) + m ^ 2 * (B * ‖v‖) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg m)]
      exact add_le_add (mul_le_mul_of_nonneg_left hsecond (abs_nonneg m))
        (mul_le_mul_of_nonneg_left hsquare (sq_nonneg m))
    _ = _ := by ring

private theorem id_growth : HasExpGrowth (fun t : ℝ => t) :=
  HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)

private theorem const_growth (c : ℝ) : HasExpGrowth (fun _ : ℝ => c) :=
  HasExpGrowth.of_bounded (abs_nonneg c) (fun _ => le_rfl)

theorem noise_variance_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : 0 ≤ m) (v x : E) (hsmall : m * (B * ‖v‖ ^ 2) < 1) :
    variance (fun t : ℝ => t) (stepLaw m v f x) ≤ 1 / (1 - m * (B * ‖v‖ ^ 2)) := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  let a := noiseMean m v f x (fun t => t)
  let H : ℝ → ℝ := fun t => fderiv ℝ f (x + t • v) v
  let Z : ℝ → ℝ := fun t => t - a
  have hZg : HasExpGrowth Z := id_growth.sub_real (const_growth a)
  have hZc : Continuous Z := continuous_id.sub continuous_const
  have hHc : Continuous H := first_continuous hf hr x v
  have hHg : HasExpGrowth H := first_growth hf hr x v
  have hiZ := integrable_noise hf hr m v x hZg hZc
  have hiZZ := integrable_noise hf hr m v x (hZg.mul hZg) (hZc.mul hZc)
  have hiZH := integrable_noise hf hr m v x (hZg.mul hHg) (hZc.mul hHc)
  have hiZc := integrable_noise hf hr m v x (hZg.mul (const_growth (H a)))
    (hZc.mul continuous_const)
  have hmean : (∫ t, Z t ∂μ) = 0 := by
    rw [show Z = (fun t => t - a) from rfl, integral_sub
      (integrable_noise hf hr m v x id_growth continuous_id) (integrable_const a)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact sub_self a
  have hzv : (∫ t, Z t ^ 2 ∂μ) = variance (fun t : ℝ => t) μ := by
    exact (variance_eq_integral continuous_id.measurable.aemeasurable).symm
  have hstein := tilted_integration_by_parts hf hr m v x
    (fun t => (hasDerivAt_id t).sub_const a) continuous_const hZg (const_growth 1)
  have hone : noiseMean m v f x (fun _ => (1 : ℝ)) = 1 := by
    simp only [noiseMean, integral_const, probReal_univ, one_smul]
  have hleft : noiseMean m v f x (fun t => t * (t - a)) = variance (fun t : ℝ => t) μ := by
    change (∫ t, t * Z t ∂μ) = _
    have he (t : ℝ) : t * Z t = Z t * Z t + a * Z t := by dsimp only [Z]; ring
    simp_rw [he]
    rw [integral_add hiZZ (hiZ.const_mul a), integral_const_mul, hmean, mul_zero, add_zero]
    simpa only [pow_two] using hzv
  have hvar : variance (fun t : ℝ => t) μ = 1 + m * (∫ t, Z t * H t ∂μ) := by
    simp only [id_eq] at hstein
    rw [hleft, hone] at hstein
    exact hstein
  have hcenter : (∫ t, Z t * H t ∂μ) = ∫ t, Z t * (H t - H a) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub hiZH hiZc, integral_mul_const, hmean, zero_mul, sub_zero]
  have hLip (t : ℝ) : |H t - H a| ≤ B * ‖v‖ ^ 2 * |t - a| := by
    have hd := line_first_hasDerivAt (hf.boundedDerivs hr).1 x v
    have hbound (s : ℝ) : ‖deriv H s‖ ≤ B * ‖v‖ ^ 2 := by
      calc
        ‖deriv H s‖ = |fderiv ℝ (fderiv ℝ f) (x + s • v) v v| := by rw [(hd s).deriv]; rfl
        _ ≤ B * ‖v‖ * ‖v‖ := hf.second_directional_le hr (x + s • v) v v
        _ = B * ‖v‖ ^ 2 := by ring
    exact Convex.norm_image_sub_le_of_norm_deriv_le (fun s _ => (hd s).differentiableAt)
      (fun s _ => hbound s) convex_univ (mem_univ a) (mem_univ t)
  have hcov : (∫ t, Z t * H t ∂μ) ≤ B * ‖v‖ ^ 2 * variance (fun t : ℝ => t) μ := by
    rw [hcenter, ← hzv, ← integral_const_mul]
    have hiDiff : Integrable (fun t => Z t * (H t - H a)) μ :=
      integrable_noise hf hr m v x (hZg.mul (hHg.sub_real (const_growth (H a))))
        (hZc.mul (hHc.sub continuous_const))
    have hiUpper : Integrable (fun t => B * ‖v‖ ^ 2 * Z t ^ 2) μ := by
      convert! hiZZ.const_mul (B * ‖v‖ ^ 2) using 1
      funext t
      exact congrArg (fun z => B * ‖v‖ ^ 2 * z) (pow_two (Z t))
    apply integral_mono hiDiff hiUpper
    intro t
    calc
      Z t * (H t - H a) ≤ |Z t * (H t - H a)| := le_abs_self _
      _ = |Z t| * |H t - H a| := abs_mul _ _
      _ ≤ |Z t| * (B * ‖v‖ ^ 2 * |Z t|) := mul_le_mul_of_nonneg_left (hLip t) (abs_nonneg _)
      _ = B * ‖v‖ ^ 2 * Z t ^ 2 := by
        calc
          _ = B * ‖v‖ ^ 2 * |Z t| ^ 2 := by ring
          _ = _ := by rw [sq_abs]
  apply (le_div_iff₀ (by linarith : 0 < 1 - m * (B * ‖v‖ ^ 2))).mpr
  have hmul := mul_le_mul_of_nonneg_left hcov hm
  nlinarith [hvar]

theorem tilted_variance_lipschitz_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : 0 ≤ m) (v x : E) (hsmall : m * (B * ‖v‖ ^ 2) < 1)
    {C : ℝ≥0} {g : ℝ → ℝ} (hg : LipschitzWith C g) :
    variance g (stepLaw m v f x) ≤ (C : ℝ) ^ 2 / (1 - m * (B * ‖v‖ ^ 2)) := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  let a := noiseMean m v f x (fun t => t)
  have hc : Continuous (fun t : ℝ => t - a) := continuous_id.sub continuous_const
  have hgrowth : HasExpGrowth (fun t : ℝ => t - a) := id_growth.sub_real (const_growth a)
  have hi : Integrable (fun t : ℝ => (t - a) ^ 2) μ := by
    simpa only [pow_two] using integrable_noise hf hr m v x (hgrowth.mul hgrowth) (hc.mul hc)
  have hid : (∫ t : ℝ, (t - a) ^ 2 ∂μ) = variance (fun t : ℝ => t) μ :=
    (variance_eq_integral continuous_id.measurable.aemeasurable).symm
  calc
    variance g μ = variance (fun t => g t - g a) μ :=
      (variance_sub_const hg.continuous.aestronglyMeasurable (g a)).symm
    _ ≤ ∫ t, (g t - g a) ^ 2 ∂μ :=
      variance_le_expectation_sq (hg.continuous.sub continuous_const).aestronglyMeasurable
    _ ≤ ∫ t, (C : ℝ) ^ 2 * (t - a) ^ 2 ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun t => sq_nonneg _)) (hi.const_mul _)
      apply ae_of_all
      intro t
      have h := hg.norm_sub_le t a
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
      have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg C.coe_nonneg (abs_nonneg _))).mpr h
      simpa only [sq_abs, mul_pow] using hs
    _ = (C : ℝ) ^ 2 * variance (fun t : ℝ => t) μ := by rw [integral_const_mul, hid]
    _ ≤ (C : ℝ) ^ 2 * (1 / (1 - m * (B * ‖v‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left (noise_variance_le hf hr hm v x hsmall) (sq_nonneg _)
    _ = _ := by ring

theorem spatial_variance_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : 0 ≤ m) (v x : E) (hsmall : m * (B * ‖v‖ ^ 2) < 1)
    {C : ℝ≥0} {g : E → ℝ} (hg : LipschitzWith C g) :
    variance (fun t : ℝ => g (x + t • v)) (stepLaw m v f x) ≤
      (C : ℝ) ^ 2 * ‖v‖ ^ 2 / (1 - m * (B * ‖v‖ ^ 2)) := by
  have hline : LipschitzWith ‖v‖₊ (fun t : ℝ => x + t • v) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [dist_eq_norm]
    have he : (x + s • v) - (x + t • v) = (s - t) • v := by module
    rw [he, norm_smul, Real.norm_eq_abs, Real.dist_eq, coe_nnnorm, mul_comm]
  simpa only [NNReal.coe_mul, coe_nnnorm, mul_pow, Function.comp_def] using
    tilted_variance_lipschitz_le hf hr hm v x hsmall (hg.comp hline)

end SKBarriers2.StepCalculus

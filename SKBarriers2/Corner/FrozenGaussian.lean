module

public import OAI.Probability.SKBarriers.Gaussian.GaussianStepCalculus
public import OAI.Probability.SKBarriers.Scalar.VectorHierarchy

@[expose] public section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic

namespace SKBarriers2.Corner

def quadraticGaussian (D L : ℝ) : Measure ℝ :=
  gaussianReal (L / D) (Real.toNNReal D⁻¹)

def quadraticNormalizer (D L : ℝ) : ℝ := Real.exp (L ^ 2 / (2 * D)) / Real.sqrt D

theorem quadraticNormalizer_pos {D : ℝ} (hD : 0 < D) (L : ℝ) :
    0 < quadraticNormalizer D L := by
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr hD)

theorem quadratic_gaussian_density {D : ℝ} (hD : 0 < D) (L t : ℝ) :
    gaussianPDFReal 0 1 t * Real.exp ((1 - D) * t ^ 2 / 2 + L * t) =
      quadraticNormalizer D L * gaussianPDFReal (L / D) (Real.toNNReal D⁻¹) t := by
  have hD₀ : D ≠ 0 := ne_of_gt hD
  have hv : (Real.toNNReal D⁻¹ : ℝ) = D⁻¹ := Real.coe_toNNReal _ (inv_nonneg.mpr hD.le)
  have hs : Real.sqrt D * Real.sqrt (2 * Real.pi * D⁻¹) = Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul hD.le]
    congr 1
    field_simp
  have he : -t ^ 2 / 2 + ((1 - D) * t ^ 2 / 2 + L * t) =
      L ^ 2 / (2 * D) - (t - L / D) ^ 2 / (2 * D⁻¹) := by
    field_simp
    ring
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, hv, quadraticNormalizer]
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-t ^ 2 / 2 + ((1 - D) * t ^ 2 / 2 + L * t)) := by
      rw [Real.exp_add (-t ^ 2 / 2) ((1 - D) * t ^ 2 / 2 + L * t)]
      ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (L ^ 2 / (2 * D)) * Real.exp (-(t - L / D) ^ 2 / (2 * D⁻¹))) := by
      have he' : -t ^ 2 / 2 + ((1 - D) * t ^ 2 / 2 + L * t) =
          L ^ 2 / (2 * D) + (-(t - L / D) ^ 2 / (2 * D⁻¹)) := by
        rw [he]
        ring
      rw [he', Real.exp_add (L ^ 2 / (2 * D)) (-(t - L / D) ^ 2 / (2 * D⁻¹))]
    _ = _ := by rw [← hs]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem integral_quadratic_tilt {D : ℝ} (hD : 0 < D) (L : ℝ) (g : ℝ → ℝ) :
    (∫ t, Real.exp ((1 - D) * t ^ 2 / 2 + L * t) * g t ∂gaussianReal 0 1) =
      quadraticNormalizer D L * ∫ t, g t ∂quadraticGaussian D L := by
  have hv : Real.toNNReal D⁻¹ ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr (inv_pos.mpr hD))
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    quadraticGaussian, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  calc
    _ = ∫ t, (gaussianPDFReal 0 1 t * Real.exp ((1 - D) * t ^ 2 / 2 + L * t)) * g t := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by ring)
    _ = ∫ t, quadraticNormalizer D L *
        (gaussianPDFReal (L / D) (Real.toNNReal D⁻¹) t * g t) := by
      simp_rw [quadratic_gaussian_density hD, mul_assoc]
    _ = _ := integral_const_mul _ _

theorem integral_exp_quadratic {D : ℝ} (hD : 0 < D) (L : ℝ) :
    (∫ t, Real.exp ((1 - D) * t ^ 2 / 2 + L * t) ∂gaussianReal 0 1) =
      quadraticNormalizer D L := by
  simpa [quadraticGaussian] using integral_quadratic_tilt hD L (fun _ => 1)

theorem integrable_exp_quadratic {D : ℝ} (hD : 0 < D) (L : ℝ) :
    Integrable (fun t => Real.exp ((1 - D) * t ^ 2 / 2 + L * t)) (gaussianReal 0 1) := by
  by_contra hi
  have H := integral_exp_quadratic hD L
  rw [integral_undef hi] at H
  exact (ne_of_gt (quadraticNormalizer_pos hD L)) H.symm

private theorem integrable_gaussianReal_iff_pdf {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (g : ℝ → ℝ) : Integrable g (gaussianReal μ v) ↔
      Integrable (fun t => gaussianPDFReal μ v t * g t) := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

theorem integrable_quadraticGaussian_iff {D : ℝ} (hD : 0 < D) (L : ℝ) (g : ℝ → ℝ) :
    Integrable g (quadraticGaussian D L) ↔
      Integrable (fun t => Real.exp ((1 - D) * t ^ 2 / 2 + L * t) * g t) (gaussianReal 0 1) := by
  have hv : Real.toNNReal D⁻¹ ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr (inv_pos.mpr hD))
  rw [quadraticGaussian, integrable_gaussianReal_iff_pdf hv,
    integrable_gaussianReal_iff_pdf (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he : (fun t => gaussianPDFReal 0 1 t *
      (Real.exp ((1 - D) * t ^ 2 / 2 + L * t) * g t)) =
      fun t => quadraticNormalizer D L * (gaussianPDFReal (L / D) (Real.toNNReal D⁻¹) t * g t) := by
    funext t
    rw [← mul_assoc, quadratic_gaussian_density hD]
    ring
  rw [he, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ne_of_gt (quadraticNormalizer_pos hD L)))]

theorem integrable_exp_quadraticGrowth {D C : ℝ} (hD : 0 < D) (_hC : 0 ≤ C)
    (L A ε : ℝ) {K : ℝ → ℝ} (hK : Continuous K)
    (hgrowth : ∀ t, |K t| ≤ A + C * t ^ 2) (hε : 2 * |ε| * C < D) :
    Integrable (fun t => Real.exp (ε * K t)) (quadraticGaussian D L) := by
  rw [integrable_quadraticGaussian_iff hD]
  let D' := D - 2 * |ε| * C
  have hD' : 0 < D' := by dsimp [D']; linarith
  have hi := (integrable_exp_quadratic hD' L).const_mul (Real.exp (|ε| * A))
  apply hi.mono' (by fun_prop)
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : ε * K t ≤ |ε| * (A + C * t ^ 2) := by
    calc
      _ ≤ |ε * K t| := le_abs_self _
      _ = |ε| * |K t| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgrowth t) (abs_nonneg _)
  dsimp [D']
  nlinarith

theorem quadraticGrowth_mem_interior {D C : ℝ} (hD : 0 < D) (hC : 0 ≤ C)
    (L A : ℝ) {K : ℝ → ℝ} (hK : Continuous K)
    (hgrowth : ∀ t, |K t| ≤ A + C * t ^ 2) :
    0 ∈ interior (integrableExpSet K (quadraticGaussian D L)) := by
  let ρ := D / (4 * (C + 1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hs : Set.Ioo (-ρ) ρ ⊆ integrableExpSet K (quadraticGaussian D L) := by
    intro ε hε
    apply integrable_exp_quadraticGrowth hD hC L A ε hK hgrowth
    have ha : |ε| < ρ := abs_lt.mpr hε
    have hb : 4 * (C + 1) * |ε| < D := by
      have ht := (lt_div_iff₀ (by positivity : 0 < 4 * (C + 1))).mp ha
      nlinarith
    nlinarith [abs_nonneg ε]
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Ioo_mem_nhds (neg_neg_of_pos hρ) hρ) hs)

theorem gaussianStep_quadratic_zero (C L H : ℝ) :
    gaussianStep 0 (fun p : Unit × ℝ => C + L * p.2 + H / 2 * p.2 ^ 2) () = C + H / 2 := by
  have hX : MemLp (fun t : ℝ => t) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hs : (∫ t : ℝ, t ^ 2 ∂gaussianReal 0 1) = 1 := by
    have hv := variance_eq_sub hX
    simpa only [variance_fun_id_gaussianReal, NNReal.coe_one, integral_id_gaussianReal,
      zero_pow (by norm_num : 2 ≠ 0), sub_zero, Pi.pow_apply] using hv.symm
  simp only [gaussianStep, ite_true]
  have hi : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := hX.integrable (by norm_num)
  calc
    _ = (∫ t : ℝ, C + L * t ∂gaussianReal 0 1) +
        ∫ t : ℝ, H / 2 * t ^ 2 ∂gaussianReal 0 1 :=
      integral_add ((integrable_const C).add (hi.const_mul L))
        (hX.integrable_sq.const_mul (H / 2))
    _ = ((∫ _t : ℝ, C ∂gaussianReal 0 1) + (∫ t : ℝ, L * t ∂gaussianReal 0 1)) +
        ∫ t : ℝ, H / 2 * t ^ 2 ∂gaussianReal 0 1 := by
      rw [integral_add (integrable_const C) (hi.const_mul L)]
    _ = _ := by rw [integral_const, integral_const_mul, integral_const_mul,
                    integral_id_gaussianReal, hs]; simp

theorem gaussianStep_quadratic {m H : ℝ} (hm : m ≠ 0) (hD : 0 < 1 - m * H)
    (C L : ℝ) :
    gaussianStep m (fun p : Unit × ℝ => C + L * p.2 + H / 2 * p.2 ^ 2) () =
      C - Real.log (1 - m * H) / (2 * m) + m * L ^ 2 / (2 * (1 - m * H)) := by
  have he (t : ℝ) : m * (C + L * t + H / 2 * t ^ 2) =
      m * C + ((1 - (1 - m * H)) * t ^ 2 / 2 + (m * L) * t) := by ring
  simp only [gaussianStep, ite_eq_right hm, positiveGaussianLogStep]
  have hex (t : ℝ) : Real.exp (m * (C + L * t + H / 2 * t ^ 2)) =
      Real.exp (m * C) * Real.exp ((1 - (1 - m * H)) * t ^ 2 / 2 + (m * L) * t) := by
    rw [he, Real.exp_add (m * C) ((1 - (1 - m * H)) * t ^ 2 / 2 + (m * L) * t)]
  simp_rw [hex]
  rw [integral_const_mul, integral_exp_quadratic hD, quadraticNormalizer,
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr hD))),
    Real.log_exp, Real.log_div (Real.exp_ne_zero _) (ne_of_gt (Real.sqrt_pos.mpr hD)),
    Real.log_exp, Real.log_sqrt hD.le]
  field_simp
  ring

def quadraticPerturbation (m C L H : ℝ) (K : ℝ → ℝ) (ε : ℝ) : ℝ :=
  gaussianStep m (fun p : Unit × ℝ => C + L * p.2 + H / 2 * p.2 ^ 2 + ε * K p.2) ()

theorem quadraticPerturbation_eq_cgf {m H : ℝ} (hm : m ≠ 0) (hD : 0 < 1 - m * H)
    (C L ε : ℝ) (K : ℝ → ℝ)
    (hK : m * ε ∈ integrableExpSet K (quadraticGaussian (1 - m * H) (m * L))) :
    quadraticPerturbation m C L H K ε =
      C - Real.log (1 - m * H) / (2 * m) + m * L ^ 2 / (2 * (1 - m * H)) +
        cgf K (quadraticGaussian (1 - m * H) (m * L)) (m * ε) / m := by
  let μ := quadraticGaussian (1 - m * H) (m * L)
  let : IsProbabilityMeasure μ := by unfold μ quadraticGaussian; infer_instance
  have hpos : 0 < mgf K μ (m * ε) := mgf_pos hK
  have he (t : ℝ) : Real.exp (m * (C + L * t + H / 2 * t ^ 2 + ε * K t)) =
      Real.exp (m * C) *
        (Real.exp ((1 - (1 - m * H)) * t ^ 2 / 2 + (m * L) * t) *
          Real.exp ((m * ε) * K t)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [quadraticPerturbation, gaussianStep, ite_eq_right hm, positiveGaussianLogStep]
  simp_rw [he]
  rw [integral_const_mul, integral_quadratic_tilt hD]
  change Real.log (Real.exp (m * C) * (quadraticNormalizer (1 - m * H) (m * L) *
    mgf K μ (m * ε))) / m = _
  rw [Real.log_mul (Real.exp_ne_zero _)
      (mul_ne_zero (ne_of_gt (quadraticNormalizer_pos hD _)) (ne_of_gt hpos)),
    Real.log_exp, Real.log_mul (ne_of_gt (quadraticNormalizer_pos hD _)) (ne_of_gt hpos),
    quadraticNormalizer, Real.log_div (Real.exp_ne_zero _) (ne_of_gt (Real.sqrt_pos.mpr hD)),
    Real.log_exp, Real.log_sqrt hD.le]
  change _ = _ + Real.log (mgf K μ (m * ε)) / m
  field_simp
  ring

theorem quadraticPerturbation_eventuallyEq_cgf {m H ε : ℝ} (hm : m ≠ 0)
    (hD : 0 < 1 - m * H) (C L : ℝ) (K : ℝ → ℝ)
    (hK : m * ε ∈ interior (integrableExpSet K (quadraticGaussian (1 - m * H) (m * L)))) :
    quadraticPerturbation m C L H K =ᶠ[𝓝 ε]
      fun t => C - Real.log (1 - m * H) / (2 * m) + m * L ^ 2 / (2 * (1 - m * H)) +
        cgf K (quadraticGaussian (1 - m * H) (m * L)) (m * t) / m := by
  have he : ∀ᶠ t in 𝓝 ε, m * t ∈ interior
      (integrableExpSet K (quadraticGaussian (1 - m * H) (m * L))) :=
    ((continuous_const.mul continuous_id).tendsto ε).eventually
      (isOpen_interior.mem_nhds hK)
  filter_upwards [he] with t ht
  exact quadraticPerturbation_eq_cgf hm hD C L t K (interior_subset ht)

theorem quadraticPerturbation_hasDerivAt {m H ε : ℝ} (hm : m ≠ 0)
    (hD : 0 < 1 - m * H) (C L : ℝ) (K : ℝ → ℝ)
    (hK : m * ε ∈ interior (integrableExpSet K (quadraticGaussian (1 - m * H) (m * L)))) :
    HasDerivAt (quadraticPerturbation m C L H K)
      (deriv (cgf K (quadraticGaussian (1 - m * H) (m * L))) (m * ε)) ε := by
  have hd := (((analyticAt_cgf hK).differentiableAt.hasDerivAt.comp ε
      ((hasDerivAt_id ε).const_mul m)).div_const m).const_add
    (C - Real.log (1 - m * H) / (2 * m) + m * L ^ 2 / (2 * (1 - m * H)))
  have hd' : HasDerivAt
      (fun t => C - Real.log (1 - m * H) / (2 * m) + m * L ^ 2 / (2 * (1 - m * H)) +
        cgf K (quadraticGaussian (1 - m * H) (m * L)) (m * t) / m)
      (deriv (cgf K (quadraticGaussian (1 - m * H) (m * L))) (m * ε)) ε := by
    simpa only [Function.comp_def, mul_one, mul_div_cancel_right₀ _ hm] using hd
  exact hd'.congr_of_eventuallyEq (quadraticPerturbation_eventuallyEq_cgf hm hD C L K hK)

theorem quadraticPerturbation_hasDerivAt_zero {m H : ℝ} (hm : m ≠ 0)
    (hD : 0 < 1 - m * H) (C L : ℝ) (K : ℝ → ℝ)
    (hK : 0 ∈ interior (integrableExpSet K (quadraticGaussian (1 - m * H) (m * L)))) :
    HasDerivAt (quadraticPerturbation m C L H K)
      (∫ t, K t ∂quadraticGaussian (1 - m * H) (m * L)) 0 := by
  let : IsProbabilityMeasure (quadraticGaussian (1 - m * H) (m * L)) := by
    unfold quadraticGaussian
    infer_instance
  have hd := quadraticPerturbation_hasDerivAt hm hD C L K (by simpa using hK :
    m * 0 ∈ interior (integrableExpSet K (quadraticGaussian (1 - m * H) (m * L))))
  simpa only [mul_zero, deriv_cgf_zero hK, probReal_univ, div_one] using hd

theorem quadraticPerturbation_second_zero {m H : ℝ} (hm : m ≠ 0)
    (hD : 0 < 1 - m * H) (C L : ℝ) (K : ℝ → ℝ)
    (hK : 0 ∈ interior (integrableExpSet K (quadraticGaussian (1 - m * H) (m * L)))) :
    iteratedDeriv 2 (quadraticPerturbation m C L H K) 0 =
      m * ((∫ t, K t ^ 2 ∂quadraticGaussian (1 - m * H) (m * L)) -
        (∫ t, K t ∂quadraticGaussian (1 - m * H) (m * L)) ^ 2) := by
  let μ := quadraticGaussian (1 - m * H) (m * L)
  let : IsProbabilityMeasure μ := by unfold μ quadraticGaussian; infer_instance
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), m * t ∈ interior (integrableExpSet K μ) := by
    have hK' : m * 0 ∈ interior (integrableExpSet K μ) := by simpa using hK
    exact ((continuous_const.mul continuous_id).tendsto 0).eventually
      (isOpen_interior.mem_nhds hK')
  have hd : deriv (quadraticPerturbation m C L H K) =ᶠ[𝓝 (0 : ℝ)]
      fun t => deriv (cgf K μ) (m * t) := by
    filter_upwards [he] with t ht
    exact (quadraticPerturbation_hasDerivAt hm hD C L K ht).deriv
  have hcgf : HasDerivAt (deriv (cgf K μ)) (deriv (deriv (cgf K μ)) (m * 0)) (m * 0) := by
    simpa only [mul_zero] using (analyticAt_cgf hK).deriv.differentiableAt.hasDerivAt
  have htwo := (hcgf.comp 0 ((hasDerivAt_id 0).const_mul m)).deriv
  simp only [Function.comp_def] at htwo
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, htwo]
  have hvar := iteratedDeriv_two_cgf hK
  simp only [mul_zero]
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hvar
  rw [hvar, deriv_cgf_zero hK]
  simp only [zero_mul, Real.exp_zero, mul_one, mgf_zero, probReal_univ, div_one]
  ring

theorem integral_exp_linear_quadraticGaussian {D : ℝ} (hD : 0 < D) (M C L : ℝ) :
    (∫ t, Real.exp (C + L * t) ∂quadraticGaussian D M) =
      Real.exp (C + (M / D) * L + D⁻¹ * L ^ 2 / 2) := by
  have he : (fun t => Real.exp (C + L * t)) = fun t => Real.exp C * Real.exp (L * t) := by
    funext t
    exact Real.exp_add _ _
  rw [he, integral_const_mul]
  change Real.exp C * mgf id (gaussianReal (M / D) (Real.toNNReal D⁻¹)) L = _
  rw [mgf_id_gaussianReal, Real.coe_toNNReal _ (inv_nonneg.mpr hD.le), ← Real.exp_add]
  congr 1
  ring

theorem logPartition_hasDerivAt {Z : ℝ → ℝ} {m z₁ x : ℝ}
    (hZ : HasDerivAt Z z₁ x) (hpos : Z x ≠ 0) :
    HasDerivAt (fun ε => Real.log (Z ε) / m) (z₁ / Z x / m) x := by
  exact (hZ.log hpos).div_const m

theorem logPartition_second {Z : ℝ → ℝ} {m z₁ z₂ x : ℝ}
    (hZ : HasDerivAt Z z₁ x) (hZ₂ : HasDerivAt (deriv Z) z₂ x)
    (hd : ∀ᶠ ε in 𝓝 x, DifferentiableAt ℝ Z ε) (hpos : Z x ≠ 0) :
    HasDerivAt (deriv (fun ε => Real.log (Z ε) / m))
      ((z₂ * Z x - z₁ ^ 2) / (Z x) ^ 2 / m) x := by
  have hn : ∀ᶠ ε in 𝓝 x, Z ε ≠ 0 := hZ.continuousAt.eventually_ne hpos
  have he : deriv (fun ε => Real.log (Z ε) / m) =ᶠ[𝓝 x]
      fun ε => deriv Z ε / Z ε / m := by
    filter_upwards [hd, hn] with ε hε hnε
    exact ((hε.hasDerivAt.log hnε).div_const m).deriv
  have H := (hZ₂.div hZ hpos).div_const m
  rw [hZ.deriv] at H
  have H' : HasDerivAt (fun ε => deriv Z ε / Z ε / m)
      ((z₂ * Z x - z₁ ^ 2) / (Z x) ^ 2 / m) x := by
    simpa only [Pi.div_apply, pow_two] using H
  exact H'.congr_of_eventuallyEq he

def IntegralDerivativeControl (μ : Measure ℝ) (F F₁ : ℝ → ℝ → ℝ) (ε : ℝ) : Prop :=
  ∃ S : Set ℝ, S ∈ 𝓝 ε ∧ ∃ b : ℝ → ℝ,
    (∀ᶠ e in 𝓝 ε, AEStronglyMeasurable (F e) μ) ∧ Integrable (F ε) μ ∧
    AEStronglyMeasurable (F₁ ε) μ ∧ Integrable b μ ∧
    (∀ᵐ t ∂μ, ∀ e ∈ S, ‖F₁ e t‖ ≤ b t) ∧
    (∀ᵐ t ∂μ, ∀ e ∈ S, HasDerivAt (fun u => F u t) (F₁ e t) e)

theorem IntegralDerivativeControl.hasDerivAt {μ : Measure ℝ} {F F₁ : ℝ → ℝ → ℝ} {ε : ℝ}
    (H : IntegralDerivativeControl μ F F₁ ε) :
    HasDerivAt (fun e => ∫ t, F e t ∂μ) (∫ t, F₁ ε t ∂μ) ε := by
  rcases H with ⟨S, hS, b, hm, hi, hm₁, hb, hbound, hd⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS hm hi hm₁ hbound hb hd).2

end SKBarriers2.Corner

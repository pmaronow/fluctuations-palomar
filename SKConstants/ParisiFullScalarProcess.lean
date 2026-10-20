module
public import SKConstants.ScalarProcessParisiSeed
public import SKConstants.ScalarForwardPicardPaths

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.SK.Analytic SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def actualParisiFullScalarDrift (β : ℝ) : BoundedLipschitzDrift :=
  finiteTemperatureCDFDrift β (cdf (parisiEquilibriumMeasure β : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩)
    (supported_probability_cdf_one (parisiEquilibriumMeasure β)
      (parisiEquilibriumMeasure_upstream_spec β).1)

def actualParisiFullMagnetization (β : ℝ) (v x : ℝ) : ℝ :=
  scalarCDFGradient β (cdf (parisiEquilibriumMeasure β : Measure ℝ))
    (cdfTimeClamp (v/β^2)) (Real.toNNReal (1-cdfTimeClamp (v/β^2))) x

def actualParisiFullCurvature (β : ℝ) (v x : ℝ) : ℝ :=
  scalarCDFHessian β (cdf (parisiEquilibriumMeasure β : Measure ℝ))
    (cdfTimeClamp (v/β^2)) (Real.toNNReal (1-cdfTimeClamp (v/β^2))) x

theorem actualParisiEquilibrium_cdf_one_after_support (β : ℝ) (hβ : 1 < β)
    (q : ℝ) (hq : parisiEquilibriumSupportEndpoint β ≤ q) :
    cdf (parisiEquilibriumMeasure β : Measure ℝ) q = 1 := by
  have hs := (parisiEquilibriumSupportEndpoint_spec β hβ).2.2.1
  have hcut := probability_cdf_one_of_support_bound (parisiEquilibriumMeasure β)
    (parisiEquilibriumSupportEndpoint β) (fun x hx => (hs hx).2)
  exact le_antisymm (cdf_le_one _ _) (by
    rw [←hcut]
    exact (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono hq)

theorem actualParisiEquilibrium_cdf_clamped_one (β : ℝ) (hβ : 1 < β)
    (v : ℝ) (hv : β^2*parisiEquilibriumSupportEndpoint β ≤ v) :
    cdf (parisiEquilibriumMeasure β : Measure ℝ) (cdfTimeClamp (v/β^2)) = 1 := by
  apply actualParisiEquilibrium_cdf_one_after_support β hβ
  have hb : 0 < β^2 := sq_pos_of_pos (lt_trans zero_lt_one hβ)
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hdiv : parisiEquilibriumSupportEndpoint β ≤ v/β^2 :=
    (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hv)
  exact (le_min hdiv hQ.2.le).trans (le_max_right 0 _)

theorem actualParisiFullMagnetization_eq_tanh_after_support
    (β : ℝ) (hβ : 1 < β) (v : ℝ)
    (hv : β^2*parisiEquilibriumSupportEndpoint β ≤ v) :
    actualParisiFullMagnetization β v = Real.tanh := by
  have hb : β ≠ 0 := ne_of_gt (lt_trans zero_lt_one hβ)
  let q := cdfTimeClamp (v/β^2)
  have hq := cdfTimeClamp_mem (v/β^2)
  have hdiv : β^2*q/β^2 = q := by field_simp
  have H := parisiPhysicalGradient_at_cdf_one β hb (parisiEquilibriumMeasure β)
    (β^2*q) ⟨mul_nonneg (sq_nonneg β) hq.1,by nlinarith [hq.2,sq_nonneg β]⟩
    (by rw [hdiv]; exact actualParisiEquilibrium_cdf_clamped_one β hβ v hv)
  rw [hdiv] at H
  funext x
  exact (congrFun H x).trans (Real.tanh_eq_sinh_div_cosh x).symm

theorem actualParisiFullScalarDrift_eq_tanh_after_support
    (β : ℝ) (hβ : 1 < β) (v : ℝ)
    (hv : β^2*parisiEquilibriumSupportEndpoint β ≤ v) :
    (actualParisiFullScalarDrift β).f v = Real.tanh := by
  funext x
  change cdf (parisiEquilibriumMeasure β : Measure ℝ) (cdfTimeClamp (v/β^2))*
    actualParisiFullMagnetization β v x = _
  rw [actualParisiEquilibrium_cdf_clamped_one β hβ v hv,
    actualParisiFullMagnetization_eq_tanh_after_support β hβ v hv,one_mul]

theorem actualParisiFullMagnetization_hasDerivAt (β v x : ℝ) :
    HasDerivAt (actualParisiFullMagnetization β v) (actualParisiFullCurvature β v x) x := by
  have ht : Real.toNNReal (1-cdfTimeClamp (v/β^2)) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [(cdfTimeClamp_mem (v/β^2)).1]
  exact scalarCDFGradient_hasDerivAt β
    (fun z => ⟨cdf_nonneg (parisiEquilibriumMeasure β : Measure ℝ) z,cdf_le_one _ z⟩)
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono _ _ ht x

theorem actualParisiFullCurvature_eq_tanh_after_support
    (β : ℝ) (hβ : 1 < β) (v x : ℝ)
    (hv : β^2*parisiEquilibriumSupportEndpoint β ≤ v) :
    actualParisiFullCurvature β v x = 1-(Real.tanh x)^2 := by
  have H := actualParisiFullMagnetization_hasDerivAt β v x
  rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ v hv] at H
  exact H.unique (SKConstantsOAI.ZeroTemperatureSK.Heat.hasDerivAt_tanh x)

theorem actualParisiFullMagnetization_jets_eq_after_support
    (β : ℝ) (hβ : 1 < β) (v : ℝ)
    (hv : β^2*parisiEquilibriumSupportEndpoint β ≤ v) (n : ℕ) :
    iteratedDeriv n (actualParisiFullMagnetization β v) = iteratedDeriv n Real.tanh := by
  rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ v hv]

theorem continuous_actualParisiFullMagnetization (β : ℝ) :
    Continuous (Function.uncurry (actualParisiFullMagnetization β)) := by
  have hc : Continuous (fun p : ℝ×ℝ => (p.1/β^2,p.2)) := by fun_prop
  have H := continuous_clamped_CDFGradient β (cdf (parisiEquilibriumMeasure β : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩)
    (supported_probability_cdf_one (parisiEquilibriumMeasure β)
      (parisiEquilibriumMeasure_upstream_spec β).1)
  change Continuous (fun p : ℝ×ℝ => scalarCDFGradient β
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)) (cdfTimeClamp (p.1/β^2))
    (Real.toNNReal (1-cdfTimeClamp (p.1/β^2))) p.2)
  convert H.comp hc using 1
  rfl

theorem actualParisiFullMagnetization_curvature_bounds (β v x : ℝ) :
    |actualParisiFullMagnetization β v x| ≤ 1 ∧
    0 ≤ actualParisiFullCurvature β v x ∧
    actualParisiFullCurvature β v x ≤ 1-(actualParisiFullMagnetization β v x)^2 := by
  have ht : Real.toNNReal (1-cdfTimeClamp (v/β^2)) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [(cdfTimeClamp_mem (v/β^2)).1]
  exact scalarCDF_derivative_bounds β
    (fun z => ⟨cdf_nonneg (parisiEquilibriumMeasure β : Measure ℝ) z,cdf_le_one _ z⟩)
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono _ _ ht x

theorem actualParisiFullCurvature_lipschitz (β v : ℝ) :
    LipschitzWith susceptibilityLipschitzConstant (actualParisiFullCurvature β v) := by
  have ht : Real.toNNReal (1-cdfTimeClamp (v/β^2)) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [(cdfTimeClamp_mem (v/β^2)).1]
  exact scalarCDFHessian_lipschitz β
    (fun z => ⟨cdf_nonneg (parisiEquilibriumMeasure β : Measure ℝ) z,cdf_le_one _ z⟩)
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono _ _ ht

theorem continuous_actualParisiFullCurvature (β : ℝ) :
    Continuous (Function.uncurry (actualParisiFullCurvature β)) := by
  let α := cdf (parisiEquilibriumMeasure β : Measure ℝ)
  have ha (z : ℝ) : α z ∈ Icc (0:ℝ) 1 := ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1 = 1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have ht (s : ℝ) : Real.toNNReal (1-cdfTimeClamp s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [(cdfTimeClamp_mem s).1]
  have H : Continuous (fun p : ℝ×ℝ => scalarCDFHessian β α (cdfTimeClamp p.1)
      (Real.toNNReal (1-cdfTimeClamp p.1)) p.2) := by
    apply continuous_family_of_uniform_time
      (F := fun s => scalarCDFHessian β α (cdfTimeClamp s)
        (Real.toNNReal (1-cdfTimeClamp s)))
    · intro s
      exact (scalarCDFHessian_lipschitz β ha α.mono _ _ (ht s)).continuous
    · intro s
      have hclamp : Tendsto cdfTimeClamp (𝓝 s) (𝓝[Icc (0:ℝ) 1] cdfTimeClamp s) :=
        tendsto_nhdsWithin_iff.mpr ⟨continuous_cdfTimeClamp.tendsto s,
          Eventually.of_forall cdfTimeClamp_mem⟩
      have HU := scalarCDFHessian_time_uniform β α ha h1 (cdfTimeClamp_mem s)
      rw [Metric.tendstoUniformly_iff] at HU ⊢
      intro ε hε
      exact hclamp.eventually (HU ε hε)
  have hc : Continuous (fun p : ℝ×ℝ => (p.1/β^2,p.2)) := by fun_prop
  change Continuous (fun p : ℝ×ℝ => scalarCDFHessian β α (cdfTimeClamp (p.1/β^2))
    (Real.toNNReal (1-cdfTimeClamp (p.1/β^2))) p.2)
  convert H.comp hc using 1
  rfl

theorem actualParisiFullMagnetization_strict_bounds (β v x : ℝ) :
    -1 < actualParisiFullMagnetization β v x ∧ actualParisiFullMagnetization β v x < 1 := by
  let m := actualParisiFullMagnetization β v
  let a := actualParisiFullCurvature β v
  have hd (y : ℝ) : HasDerivAt m (a y) y := actualParisiFullMagnetization_hasDerivAt β v y
  have hb (y : ℝ) : |m y| ≤ 1 ∧ 0 ≤ a y ∧ a y ≤ 1-(m y)^2 :=
    actualParisiFullMagnetization_curvature_bounds β v y
  have ht : Real.toNNReal (1-cdfTimeClamp (v/β^2)) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [(cdfTimeClamp_mem (v/β^2)).1]
  have ho : Function.Odd m := parisiCDFGradient_odd β
    (fun z => ⟨cdf_nonneg (parisiEquilibriumMeasure β : Measure ℝ) z,cdf_le_one _ z⟩)
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono _ _ ht
  have hm0 : m 0 = 0 := by have H := ho 0; simp only [neg_zero] at H; linarith
  have hm : Monotone m := monotone_of_hasDerivAt_nonneg hd (fun y => (hb y).2.1)
  let g := fun y : ℝ => Real.exp (2*y)*(1-m y)
  have hgd (y : ℝ) : HasDerivAt g
      (Real.exp (2*y)*(2*(1-m y)-a y)) y := by
    have he : HasDerivAt (fun u : ℝ => Real.exp (2*u)) (Real.exp (2*y)*2) y := by
      convert ((hasDerivAt_id y).const_mul 2).exp using 1 <;> simp only [id_eq] <;> ring
    have H := he.mul ((hasDerivAt_const y (1:ℝ)).sub (hd y))
    change HasDerivAt (fun u : ℝ => Real.exp (2*u)*(1-m u))
      (Real.exp (2*y)*2*(1-m y)+Real.exp (2*y)*(0-a y)) y at H
    exact H.congr_deriv (by ring)
  have hg : Monotone g := monotone_of_hasDerivAt_nonneg hgd (fun y => by
    apply mul_nonneg (Real.exp_pos _).le
    nlinarith [(hb y).2.2,sq_nonneg (1-m y)])
  have hupper (y : ℝ) : m y < 1 := by
    by_cases hy : 0 ≤ y
    · have H := hg hy
      have Hg0 : g 0 = 1 := by simp [g,hm0]
      rw [Hg0] at H
      have He := Real.exp_pos (2*y)
      dsimp only [g] at H
      by_contra hn
      have hn' : 1 ≤ m y := le_of_not_gt hn
      nlinarith
    · have H := hm (le_of_not_ge hy)
      rw [hm0] at H
      linarith
  refine ⟨?_,hupper x⟩
  have H := hupper (-x)
  rw [ho x] at H
  linarith

def actualParisiFullScalarProcess {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) : ℝ≥0 → Ω → ℝ :=
  (actualParisiFullScalarDrift β).solution W.driver

theorem actualParisiFullScalarProcess_eq_preContinuationField
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) :
    actualParisiFullScalarProcess W β = actualParisiPreContinuationField W β := rfl

end SKConstants

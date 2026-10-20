module

public import SKConstants.ScalarProcessRowCovariance
public import SKConstants.ScalarProcessSignInnovationLimit
public import SKConstants.ScalarProcessInnovationMGF
public import Mathlib.Probability.Moments.Variance

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
namespace SKConstants

set_option backward.isDefEq.respectTransparency true

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem scalarHiddenSign_hasLaw (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) :
    HasLaw (fun u : Bool × Ω => scalarHiddenSign u.1) (scalarSpinLaw z)
      (scalarHiddenBrownianLaw z P) := by
  have hm := measurable_of_finite scalarHiddenSign
  refine ⟨(hm.comp measurable_fst).aemeasurable, ?_⟩
  change Measure.map (scalarHiddenSign ∘ Prod.fst) _ = _
  rw [scalarHiddenBrownianLaw, ← Measure.map_map hm measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]
  simp only [scalarHiddenPriorBool, scalarSpinLaw, Measure.map_add _ _ hm]
  rw [Measure.map_smul _ hm.aemeasurable, Measure.map_smul _ hm.aemeasurable,
    Measure.map_dirac' hm, Measure.map_dirac' hm]
  rfl

theorem scalarHiddenCenteredSign_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) :
    HasSubgaussianMGF (fun u : Bool × Ω => scalarHiddenSign u.1 - Real.tanh z) 1
      (scalarHiddenBrownianLaw z P) := by
  have hl := scalarHiddenSign_hasLaw P z
  have h := scalarSpinLaw_centered_subgaussian z
  rw [← hl.map_eq] at h
  exact HasSubgaussianMGF.of_map hl.aemeasurable h

theorem scalarHiddenCenteredSign_secondMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) :
    (∫ u : Bool × Ω, (scalarHiddenSign u.1 - Real.tanh z)^2
      ∂scalarHiddenBrownianLaw z P) = 1 - (Real.tanh z)^2 := by
  change (∫ u, ((fun a : ℝ => (a - Real.tanh z)^2) ∘
    (fun u : Bool × Ω => scalarHiddenSign u.1)) u ∂scalarHiddenBrownianLaw z P) = _
  rw [(scalarHiddenSign_hasLaw P z).integral_comp (by fun_prop), integral_scalarSpinLaw]
  have hw := scalarWeight_sum z
  have hd := scalarWeight_difference z
  nlinarith

theorem measurable_scalarContinuousInnovation (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBm : Measurable (Function.uncurry B)) (T : ℝ≥0) :
    Measurable (scalarContinuousInnovation z B T) := by
  have hb : Measurable (B T) := hBm.comp (measurable_const.prodMk measurable_id)
  exact (((measurable_const.add
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul_const (T : ℝ))).add
      (hb.comp measurable_snd)).sub_const z).sub
        (measurable_scalarContinuousDrift z B hBm T)

def scalarNormalizedInnovationRow (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (q : ℕ → ℝ≥0) (u : Bool × Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i =>
    (scalarContinuousInnovation z B (q (i+1)) u - scalarContinuousInnovation z B (q i) u) /
      Real.sqrt ((q (i+1) : ℝ) - (q i : ℝ)))

theorem measurable_scalarNormalizedInnovationRow (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBm : Measurable (Function.uncurry B)) (q : ℕ → ℝ≥0) :
    Measurable (scalarNormalizedInnovationRow (d := d) z B q) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  exact ((measurable_scalarContinuousInnovation z B hBm _).sub
    (measurable_scalarContinuousInnovation z B hBm _)).div_const _

theorem scalarNormalizedInnovationRow_coordinate_independent
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (q : ℕ → ℝ≥0) (hq : Monotone q) :
    iIndepFun (fun i : Fin d => fun u => scalarNormalizedInnovationRow z B q u i)
      (scalarHiddenBrownianLaw z P) := by
  have hi := (brownianMeshIncrement_iIndepFun
    (scalarContinuousInnovation_isBrownianReal P z B hB).toIsPreBrownianReal q hq).precomp
      (g := fun i : Fin d => i.val) Fin.val_injective
  exact hi.comp (fun i x => x / Real.sqrt ((q (i+1) : ℝ) - (q i : ℝ)))
    (fun _ => measurable_id.div_const _)

theorem scalarNormalizedInnovationRow_coordinate_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q) (i : Fin d) :
    HasLaw (fun u => scalarNormalizedInnovationRow z B q u i) (gaussianReal 0 1)
      (scalarHiddenBrownianLaw z P) :=
  scalarNormalizedInnovation_sub_hasLaw P z B hB _ _ (hq (by omega))

private theorem standardGaussian_hasSubgaussianMGF {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {X : A → ℝ} (h : HasLaw X (gaussianReal 0 1) μ) :
    HasSubgaussianMGF X 1 μ where
  integrable_exp_mul θ := h.integrable_comp (integrable_exp_mul_gaussianReal θ)
  mgf_le θ := by rw [mgf_gaussianReal h]; simp

theorem scalarNormalizedInnovationRow_linearForm_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q)
    (a : EuclideanSpace ℝ (Fin d)) :
    HasSubgaussianMGF (fun u => ⟪scalarNormalizedInnovationRow z B q u, a⟫_ℝ)
      (∑ i : Fin d, (NNReal.mk ((a i)^2) (sq_nonneg _))) (scalarHiddenBrownianLaw z P) := by
  have hi := (scalarNormalizedInnovationRow_coordinate_independent P z B hB q hq.monotone).comp
    (fun i x => a i * x) (fun _ => measurable_const.mul measurable_id)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ)
    (fun i _ => (standardGaussian_hasSubgaussianMGF
      (scalarNormalizedInnovationRow_coordinate_hasLaw P z B hB q hq i)).const_mul (a i))
  convert h using 1
  · ext u
    simp only [Function.comp_def, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  · apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_mk]
    change (∑ i, (a i)^2) = ∑ i, (a i)^2*1
    simp

theorem scalarNormalizedInnovationRow_linearForm_secondMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q)
    (a : EuclideanSpace ℝ (Fin d)) :
    (∫ u, ⟪scalarNormalizedInnovationRow z B q u, a⟫_ℝ ^ 2
      ∂scalarHiddenBrownianLaw z P) = ‖a‖^2 := by
  let μ := scalarHiddenBrownianLaw z P
  let X : Fin d → Bool × Ω → ℝ := fun i u => a i * scalarNormalizedInnovationRow z B q u i
  have hMGF (i : Fin d) : HasSubgaussianMGF (X i) (NNReal.mk ((a i)^2) (sq_nonneg _)) μ := by
    convert (standardGaussian_hasSubgaussianMGF
      (scalarNormalizedInnovationRow_coordinate_hasLaw P z B hB q hq i)).const_mul (a i) using 1
    apply NNReal.eq
    change (a i)^2 = (a i)^2*1
    simp
  have hLp (i : Fin d) : MemLp (X i) 2 μ := (hMGF i).memLp 2
  have hMean (i : Fin d) : (∫ u, X i u ∂μ) = 0 := by
    rw [show X i = fun u => a i * scalarNormalizedInnovationRow z B q u i from rfl,
      integral_const_mul, (scalarNormalizedInnovationRow_coordinate_hasLaw P z B hB q hq i).integral_eq,
      integral_id_gaussianReal, mul_zero]
  have hVar (i : Fin d) : variance (X i) μ = (a i)^2 := by
    rw [show X i = fun u => a i * scalarNormalizedInnovationRow z B q u i from rfl,
      variance_const_mul, (scalarNormalizedInnovationRow_coordinate_hasLaw P z B hB q hq i).variance_eq,
      variance_id_gaussianReal]
    simp
  have hi : iIndepFun X μ :=
    (scalarNormalizedInnovationRow_coordinate_independent P z B hB q hq.monotone).comp
      (fun i x => a i * x) (fun _ => measurable_const.mul measurable_id)
  have hsLp : MemLp (fun u => ∑ i, X i u) 2 μ :=
    memLp_finsetSum _ (fun i _ => hLp i)
  have hsMean : (∫ u, ∑ i, X i u ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hLp i).integrable one_le_two)]
    simp_rw [hMean]
    simp
  have hsVar : variance (fun u => ∑ i, X i u) μ = ∑ i, (a i)^2 := by
    have hfun : (∑ i, X i) = fun u => ∑ i, X i u := by ext u; simp
    have hv := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hLp i)
      (fun i _ j _ hij => hi.indepFun hij)
    simpa only [hfun, hVar] using hv
  rw [variance_eq_sub hsLp, hsMean, zero_pow (by omega), sub_zero] at hsVar
  simpa only [X, μ, Pi.pow_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    mul_comm, EuclideanSpace.real_norm_sq_eq] using hsVar

set_option backward.isDefEq.respectTransparency true in
theorem scalarNormalizedInnovationRow_unit_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF (fun u => ⟪scalarNormalizedInnovationRow z B q u, a⟫_ℝ) 1
      (scalarHiddenBrownianLaw z P) := by
  have h := scalarNormalizedInnovationRow_linearForm_hasSubgaussianMGF P z B hB q hq a
  have hc : (∑ i : Fin d, ((NNReal.mk ((a i)^2) (sq_nonneg _)) : ℝ≥0)) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one]
    rw [← EuclideanSpace.real_norm_sq_eq]
    nlinarith [norm_nonneg a]
  refine ⟨h.integrable_exp_mul, fun θ => (h.mgf_le θ).trans ?_⟩
  apply Real.exp_le_exp.mpr
  simp only [NNReal.coe_one]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hc) (sq_nonneg θ)) (by norm_num)

end SKConstants

module
public import SKConstants.ScalarProcessMixedRowPrimitives
public import SKConstants.ScalarOrthogonalWeightedBrownian

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators InnerProductSpace
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

def scalarNormalizedBrownianRow (B : ℝ≥0 → Ω → ℝ) (q : ℕ → ℝ≥0) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (B (q (i+1)) ω-B (q i) ω)/Real.sqrt ((q (i+1):ℝ)-(q i:ℝ)))

lemma measurable_scalarNormalizedBrownianRow (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀t,Measurable (B t)) (q : ℕ → ℝ≥0) : Measurable (scalarNormalizedBrownianRow (d:=d) B q) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  exact ((hBm _).sub (hBm _)).div_const _

theorem scalarNormalizedBrownian_sub_hasLaw (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (S T : ℝ≥0) (hST : S < T) :
    HasLaw (fun u => (B T u-B S u)/Real.sqrt ((T:ℝ)-(S:ℝ))) (gaussianReal 0 1) P := by
  have hd : 0 < (T:ℝ)-(S:ℝ) := sub_pos.mpr (NNReal.coe_lt_coe.mpr hST)
  have hv : (nndist (T:ℝ) (S:ℝ):ℝ)=(T:ℝ)-(S:ℝ) := by
    change |(T:ℝ)-(S:ℝ)|=(T:ℝ)-(S:ℝ)
    exact abs_of_pos hd
  have hn : nndist (T:ℝ) (S:ℝ)/NNReal.mk ((Real.sqrt ((T:ℝ)-(S:ℝ)))^2) (sq_nonneg _)=1 := by
    apply NNReal.eq
    simp only [NNReal.coe_div,NNReal.coe_mk,NNReal.coe_one,hv,Real.sq_sqrt hd.le]
    exact div_self hd.ne'
  have hi := hB.hasLaw_sub T S
  have H := gaussianReal_div_const hi (Real.sqrt ((T:ℝ)-(S:ℝ)))
  refine ⟨hi.aemeasurable.div_const _,?_⟩
  exact H.map_eq.trans (congrArg₂ gaussianReal (zero_div _) hn)

theorem scalarNormalizedBrownianRow_coordinate_independent
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (q : ℕ → ℝ≥0) (hq : Monotone q) :
    iIndepFun (fun i : Fin d => fun u => scalarNormalizedBrownianRow B q u i)
      (P) := by
  have hi := (brownianMeshIncrement_iIndepFun
    hB q hq).precomp
      (g := fun i : Fin d => i.val) Fin.val_injective
  exact hi.comp (fun i x => x / Real.sqrt ((q (i+1) : ℝ) - (q i : ℝ)))
    (fun _ => measurable_id.div_const _)

theorem scalarNormalizedBrownianRow_coordinate_hasLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q) (i : Fin d) :
    HasLaw (fun u => scalarNormalizedBrownianRow B q u i) (gaussianReal 0 1)
      (P) :=
  scalarNormalizedBrownian_sub_hasLaw P B hB _ _ (hq (by omega))

private theorem standardGaussian_hasSubgaussianMGF {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {X : A → ℝ} (h : HasLaw X (gaussianReal 0 1) μ) :
    HasSubgaussianMGF X 1 μ where
  integrable_exp_mul θ := h.integrable_comp (integrable_exp_mul_gaussianReal θ)
  mgf_le θ := by rw [mgf_gaussianReal h]; simp

theorem scalarNormalizedBrownianRow_linearForm_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q)
    (a : EuclideanSpace ℝ (Fin d)) :
    HasSubgaussianMGF (fun u => ⟪scalarNormalizedBrownianRow B q u, a⟫_ℝ)
      (∑ i : Fin d, (NNReal.mk ((a i)^2) (sq_nonneg _))) (P) := by
  have hi := (scalarNormalizedBrownianRow_coordinate_independent P B hB q hq.monotone).comp
    (fun i x => a i * x) (fun _ => measurable_const.mul measurable_id)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ)
    (fun i _ => (standardGaussian_hasSubgaussianMGF
      (scalarNormalizedBrownianRow_coordinate_hasLaw P B hB q hq i)).const_mul (a i))
  convert h using 1
  · ext u
    simp only [Function.comp_def, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  · apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_mk]
    change (∑ i, (a i)^2) = ∑ i, (a i)^2*1
    simp

theorem scalarNormalizedBrownianRow_linearForm_secondMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q)
    (a : EuclideanSpace ℝ (Fin d)) :
    (∫ u, ⟪scalarNormalizedBrownianRow B q u, a⟫_ℝ ^ 2
      ∂P) = ‖a‖^2 := by
  let μ := P
  let X : Fin d → Ω → ℝ := fun i u => a i * scalarNormalizedBrownianRow B q u i
  have hMGF (i : Fin d) : HasSubgaussianMGF (X i) (NNReal.mk ((a i)^2) (sq_nonneg _)) μ := by
    convert (standardGaussian_hasSubgaussianMGF
      (scalarNormalizedBrownianRow_coordinate_hasLaw P B hB q hq i)).const_mul (a i) using 1
    apply NNReal.eq
    change (a i)^2 = (a i)^2*1
    simp
  have hLp (i : Fin d) : MemLp (X i) 2 μ := (hMGF i).memLp 2
  have hMean (i : Fin d) : (∫ u, X i u ∂μ) = 0 := by
    rw [show X i = fun u => a i * scalarNormalizedBrownianRow B q u i from rfl,
      integral_const_mul, (scalarNormalizedBrownianRow_coordinate_hasLaw P B hB q hq i).integral_eq,
      integral_id_gaussianReal, mul_zero]
  have hVar (i : Fin d) : variance (X i) μ = (a i)^2 := by
    rw [show X i = fun u => a i * scalarNormalizedBrownianRow B q u i from rfl,
      variance_const_mul, (scalarNormalizedBrownianRow_coordinate_hasLaw P B hB q hq i).variance_eq,
      variance_id_gaussianReal]
    simp
  have hi : iIndepFun X μ :=
    (scalarNormalizedBrownianRow_coordinate_independent P B hB q hq.monotone).comp
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
theorem scalarNormalizedBrownianRow_unit_hasSubgaussianMGF
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF (fun u => ⟪scalarNormalizedBrownianRow B q u, a⟫_ℝ) 1
      (P) := by
  have h := scalarNormalizedBrownianRow_linearForm_hasSubgaussianMGF P B hB q hq a
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

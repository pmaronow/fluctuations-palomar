module

public import SKConstants.GaussianRotation

public section
open MeasureTheory ProbabilityTheory
noncomputable section
namespace SKConstants
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
@[expose] def originalRotatedPairCLM (a b : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E E).prod
    (a • ContinuousLinearMap.fst ℝ E E + b • ContinuousLinearMap.snd ℝ E E)
@[expose] def rotatedOriginalPairCLM (a b : ℝ) : E × E →L[ℝ] E × E :=
  (a • ContinuousLinearMap.fst ℝ E E + b • ContinuousLinearMap.snd ℝ E E).prod
    (ContinuousLinearMap.fst ℝ E E)
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma originalRotatedPairCLM_apply (a b : ℝ) (p : E × E) :
    originalRotatedPairCLM a b p = (p.1, gaussianRotation a b p) := by rfl
omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma rotatedOriginalPairCLM_apply (a b : ℝ) (p : E × E) :
    rotatedOriginalPairCLM a b p = (gaussianRotation a b p, p.1) := by rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma dual_rotation_norm_identity (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1)
    (U V : StrongDual ℝ E) :
    ‖U + a • V‖ ^ 2 + ‖b • V‖ ^ 2 = ‖a • U + V‖ ^ 2 + ‖b • U‖ ^ 2 := by
  simp_rw [← (InnerProductSpace.toDual ℝ E).symm.norm_map,
    map_add, map_smul]
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, real_inner_smul_left]
  linear_combination (‖(InnerProductSpace.toDual ℝ E).symm V‖ ^ 2 -
    ‖(InnerProductSpace.toDual ℝ E).symm U‖ ^ 2) * h

lemma stdGaussian_rotated_pair_exchangeable (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ((stdGaussian E).prod (stdGaussian E)).map (fun p => (p.1, gaussianRotation a b p)) =
      ((stdGaussian E).prod (stdGaussian E)).map (fun p => (gaussianRotation a b p, p.1)) := by
  change ((stdGaussian E).prod (stdGaussian E)).map (originalRotatedPairCLM a b) =
      ((stdGaussian E).prod (stdGaussian E)).map (rotatedOriginalPairCLM a b)
  apply Measure.ext_of_charFunDual
  ext L
  have h1 : (L.comp (originalRotatedPairCLM a b)).comp (.inl ℝ E E) =
      L.comp (.inl ℝ E E) + a • L.comp (.inr ℝ E E) := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      originalRotatedPairCLM_apply, gaussianRotation, smul_zero, add_zero]
    rw [← L.comp_inl_add_comp_inr]
    simp
  have h2 : (L.comp (originalRotatedPairCLM a b)).comp (.inr ℝ E E) =
      b • L.comp (.inr ℝ E E) := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      originalRotatedPairCLM_apply, gaussianRotation, smul_zero, zero_add]
    rw [← L.comp_inl_add_comp_inr]
    simp
    exact L.map_zero
  have h3 : (L.comp (rotatedOriginalPairCLM a b)).comp (.inl ℝ E E) =
      a • L.comp (.inl ℝ E E) + L.comp (.inr ℝ E E) := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      rotatedOriginalPairCLM_apply, gaussianRotation, smul_zero, add_zero]
    rw [← L.comp_inl_add_comp_inr]
    simp
  have h4 : (L.comp (rotatedOriginalPairCLM a b)).comp (.inr ℝ E E) =
      b • L.comp (.inl ℝ E E) := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      rotatedOriginalPairCLM_apply, gaussianRotation, smul_zero, zero_add]
    rw [← L.comp_inl_add_comp_inr]
    simp
    exact L.map_zero
  simp_rw [charFunDual_map, charFunDual_prod, h1, h2, h3, h4,
    charFunDual_stdGaussian, ← Complex.exp_add]
  have hn := dual_rotation_norm_identity a b h (L.comp (.inl ℝ E E)) (L.comp (.inr ℝ E E))
  congr 1
  rw [← add_div, ← add_div, ← neg_add, ← neg_add]
  exact_mod_cast congrArg (fun t : ℝ => -t / 2) hn
end SKConstants
namespace SKConstants
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
lemma stdGaussian_rotated_pair_identDistrib (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    IdentDistrib (fun p : E × E => (p.1, gaussianRotation a b p))
      (fun p => (gaussianRotation a b p, p.1))
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) :=
  ⟨(by unfold gaussianRotation; fun_prop), (by unfold gaussianRotation; fun_prop),
    stdGaussian_rotated_pair_exchangeable a b h⟩

lemma goe_rotated_pair_identDistrib {n : ℕ} (sigma a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    IdentDistrib
      (fun p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n) =>
        (GaussianProposal.goeMatrix sigma p.1, GaussianProposal.goeMatrix sigma (gaussianRotation a b p)))
      (fun p => (GaussianProposal.goeMatrix sigma (gaussianRotation a b p), GaussianProposal.goeMatrix sigma p.1))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) := by
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n) =>
      (GaussianProposal.goeMatrix sigma p.1, GaussianProposal.goeMatrix sigma p.2)) :=
    ((continuous_goeMatrix sigma).measurable.comp measurable_fst).prodMk
      ((continuous_goeMatrix sigma).measurable.comp measurable_snd)
  exact (stdGaussian_rotated_pair_identDistrib a b h).comp hm

lemma goe_rotated_pair_integral_swap {n : ℕ} (sigma a b : ℝ) (h : a ^ 2 + b ^ 2 = 1)
    (f : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ → ℝ) (hf : Measurable f) :
    (∫ p, f (GaussianProposal.goeMatrix sigma p.1,
        GaussianProposal.goeMatrix sigma (gaussianRotation a b p))
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) =
    (∫ p, f (GaussianProposal.goeMatrix sigma (gaussianRotation a b p),
        GaussianProposal.goeMatrix sigma p.1)
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) := by
  exact ((goe_rotated_pair_identDistrib (n := n) sigma a b h).comp hf).integral_eq

lemma goe_rotated_pair_integrable_swap_iff {n : ℕ} (sigma a b : ℝ) (h : a ^ 2 + b ^ 2 = 1)
    (f : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ → ℝ) (hf : Measurable f) :
    Integrable (fun p => f (GaussianProposal.goeMatrix sigma p.1,
        GaussianProposal.goeMatrix sigma (gaussianRotation a b p)))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) ↔
    Integrable (fun p => f (GaussianProposal.goeMatrix sigma (gaussianRotation a b p),
        GaussianProposal.goeMatrix sigma p.1))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) := by
  exact ((goe_rotated_pair_identDistrib (n := n) sigma a b h).comp hf).integrable_iff
end SKConstants

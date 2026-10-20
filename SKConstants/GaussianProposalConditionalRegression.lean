module

public import SKConstants.ConditionalGibbsDisintegration
public import SKConstants.ProposalGibbsChangeOfMeasure
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Independence.CharacteristicFunction

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem gaussianEuclideanSmoothing_compProd_eq_affine_map
    {ι : Type*} [Fintype ι] (μ : Measure (EuclideanSpace ℝ ι)) [SFinite μ]
    (c : ℝ) (v : ℝ≥0) :
    μ ⊗ₘ gaussianEuclideanSmoothingKernel c v =
      (μ.prod (GaussianProposal.primitiveGaussian ι)).map
        (fun p => (p.1, c • p.1 + Real.sqrt (v : ℝ) • p.2)) := by
  let J : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
    fun p => (p.1, c • p.1 + Real.sqrt (v : ℝ) • p.2)
  have hJ : Measurable J := by fun_prop
  ext T hT
  rw [Measure.compProd_apply hT, Measure.map_apply hJ hT,
    ← lintegral_indicator_one (hJ hT)]
  rw [lintegral_prod (α := EuclideanSpace ℝ ι) (β := EuclideanSpace ℝ ι)
    _ (show Measurable ((J ⁻¹' T).indicator
      (1 : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ≥0∞))
      from measurable_const.indicator (hJ hT)).aemeasurable]
  apply lintegral_congr
  intro z
  rw [gaussianEuclideanSmoothingKernel_eq_affine_map, Measure.map_apply (by fun_prop)
    (measurable_prodMk_left hT), ← lintegral_indicator_one (by measurability)]
  congr 1

theorem primitiveGaussian_map_neg {ι : Type*} [Fintype ι] :
    (GaussianProposal.primitiveGaussian ι).map (fun z => -z) =
      GaussianProposal.primitiveGaussian ι := by
  exact stdGaussian_map (LinearIsometryEquiv.neg ℝ)

theorem gaussianEuclideanSmoothing_reversible {ι : Type*} [Fintype ι]
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) :
    ((GaussianProposal.primitiveGaussian ι) ⊗ₘ
      gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ).map Prod.swap =
      (GaussianProposal.primitiveGaussian ι) ⊗ₘ
        gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ := by
  let γ := GaussianProposal.primitiveGaussian ι
  let c := Real.sqrt (1 - (δ : ℝ))
  let s := Real.sqrt (δ : ℝ)
  let θ := Real.arcsin s
  have hsin : Real.sin θ = s := Real.sin_arcsin
    (by dsimp [s]; exact (by norm_num : (-1 : ℝ) ≤ 0).trans (Real.sqrt_nonneg _)) (by
      dsimp [s]
      exact Real.sqrt_le_one.mpr (by exact_mod_cast hδ1))
  have hcos : Real.cos θ = c := by
    dsimp [θ]
    rw [Real.cos_arcsin]
    simp only [s, Real.sq_sqrt δ.coe_nonneg, c]
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    rw [Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hδ1)),
      Real.sq_sqrt δ.coe_nonneg]
    ring
  let R : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
    ContinuousLinearMap.rotation θ
  let N : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι := fun p => (p.1, -p.2)
  let J : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι →
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι := fun p => (p.1, c • p.1 + s • p.2)
  have hR : (γ.prod γ).map R = γ.prod γ :=
    IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero
      (fun L => integral_strongDual_stdGaussian L) θ
  have hN : (γ.prod γ).map N = γ.prod γ := by
    rw [show N = Prod.map id (fun z => -z) by rfl,
      ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
      primitiveGaussian_map_neg]
  have hNR : (γ.prod γ).map (N ∘ R) = γ.prod γ := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), hR, hN]
  have hJR : J ∘ N ∘ R = Prod.swap ∘ J := by
    funext p
    simp only [Function.comp_apply, J, N, R, ContinuousLinearMap.rotation_apply,
      hcos, hsin, Prod.swap_prod_mk]
    apply Prod.ext
    · rfl
    · ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]
      nlinarith [congrArg (fun a : ℝ => a * p.1 i) hcs]
  simp_rw [gaussianEuclideanSmoothing_compProd_eq_affine_map]
  change ((γ.prod γ).map J).map Prod.swap = (γ.prod γ).map J
  rw [Measure.map_map measurable_swap (by fun_prop), ← hJR,
    ← Measure.map_map (by fun_prop) (by fun_prop), hNR]

theorem gaussianEuclideanSmoothing_preserves_primitiveGaussian {ι : Type*} [Fintype ι]
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) :
    gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ ∘ₘ
      GaussianProposal.primitiveGaussian ι = GaussianProposal.primitiveGaussian ι := by
  have h := congrArg Measure.fst (gaussianEuclideanSmoothing_reversible (ι := ι) δ hδ1)
  simpa only [Measure.fst_map_swap, Measure.snd_compProd, Measure.fst_compProd] using h

theorem reversibleKernel_weighted_rectangle {E : Type*} [MeasurableSpace E]
    (γ : Measure E) [IsProbabilityMeasure γ] (κ : Kernel E E) [IsMarkovKernel κ]
    (hrev : (γ ⊗ₘ κ).map Prod.swap = γ ⊗ₘ κ)
    (φ : E → ℝ≥0∞) (hφ : Measurable φ) (A : Set E) (hA : MeasurableSet A) :
    (∫⁻ z, κ z A * φ z ∂γ) = ∫⁻ base in A, ∫⁻ z, φ z ∂κ base ∂γ := by
  let F : E × E → ℝ≥0∞ := fun p => φ p.1 * A.indicator (1 : E → ℝ≥0∞) p.2
  have hF : Measurable F := (hφ.comp measurable_fst).mul
    ((measurable_const.indicator hA).comp measurable_snd)
  have hfwd : (∫⁻ p, F p ∂(γ ⊗ₘ κ)) = ∫⁻ z, κ z A * φ z ∂γ := by
    rw [Measure.lintegral_compProd hF]
    apply lintegral_congr
    intro z
    change (∫⁻ y, φ z * A.indicator (1 : E → ℝ≥0∞) y ∂κ z) = _
    rw [lintegral_const_mul _ (show Measurable (A.indicator (1 : E → ℝ≥0∞))
      from measurable_one.indicator hA),
      lintegral_indicator_one hA, mul_comm]
  have hbwd : (∫⁻ p, F p.swap ∂(γ ⊗ₘ κ)) = ∫⁻ base in A, ∫⁻ z, φ z ∂κ base ∂γ := by
    rw [Measure.lintegral_compProd
      (show Measurable (fun p : E × E => F p.swap) from hF.comp measurable_swap),
      ← lintegral_indicator hA]
    apply lintegral_congr
    intro base
    by_cases hb : base ∈ A
    · simp [F, hb]
    · simp [F, hb]
  have h := congrArg (fun μ : Measure (E × E) => ∫⁻ p, F p ∂μ) hrev
  rw [lintegral_map hF measurable_swap] at h
  exact hfwd.symm.trans (h.symm.trans hbwd)

theorem reversibleKernel_output_disintegration {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X]
    (γ : Measure E) [IsProbabilityMeasure γ] (κ : Kernel E E) [IsMarkovKernel κ]
    (hrev : (γ ⊗ₘ κ).map Prod.swap = γ ⊗ₘ κ)
    (σ : Kernel E X) [IsMarkovKernel σ] :
    (κ ∥ₖ (Kernel.id : Kernel X X)) ∘ₘ (γ ⊗ₘ σ) = γ ⊗ₘ (σ ∘ₖ κ) := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.bind_apply (hA.prod hB) (Kernel.aemeasurable _),
    Measure.compProd_apply_prod hA hB]
  have hi : (∫⁻ p : E × X, (κ ∥ₖ (Kernel.id : Kernel X X)) p (A ×ˢ B) ∂(γ ⊗ₘ σ)) =
      ∫⁻ z, κ z A * σ z B ∂γ := by
    rw [Measure.lintegral_compProd (Kernel.measurable_coe _ (hA.prod hB))]
    apply lintegral_congr
    intro z
    simp only [Kernel.parallelComp_apply_prod, Kernel.id_apply,
      Measure.dirac_apply' _ hB]
    change (∫⁻ y, κ z A * B.indicator (1 : X → ℝ≥0∞) y ∂σ z) = _
    rw [lintegral_const_mul _ (show Measurable (B.indicator (1 : X → ℝ≥0∞))
      from measurable_one.indicator hB),
      lintegral_indicator_one hB]
  rw [hi, reversibleKernel_weighted_rectangle γ κ hrev (fun z => σ z B)
    (σ.measurable_coe hB) A hA]
  apply setLIntegral_congr_fun hA
  intro base hb
  exact (Kernel.comp_apply' σ κ base hB).symm

theorem primitiveGaussian_weighted_sum_law {ι : Type*} [Fintype ι] (a b : ℝ) :
    ((GaussianProposal.primitiveGaussian ι).prod (GaussianProposal.primitiveGaussian ι)).map
      (fun p => a • p.1 + b • p.2) =
      (GaussianProposal.primitiveGaussian ι).map
        (fun z => Real.sqrt (a ^ 2 + b ^ 2) • z) := by
  let γ := GaussianProposal.primitiveGaussian ι
  have he : (γ.prod γ).map (fun p => a • p.1 + b • p.2) =
      ((γ.map (fun z => a • z)).prod (γ.map (fun z => b • z))).map
        (fun p => p.1 + p.2) := by
    rw [Measure.map_prod_map _ _
      (show Measurable (fun z : EuclideanSpace ℝ ι => a • z) by fun_prop)
      (show Measurable (fun z : EuclideanSpace ℝ ι => b • z) by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he]
  apply Measure.ext_of_charFun
  rw [charFun_map_add_prod_eq_mul]
  ext t
  simp only [Pi.mul_apply, charFun_map_smul, γ, GaussianProposal.primitiveGaussian,
    charFun_stdGaussian, norm_smul, Real.norm_eq_abs]
  rw [← Complex.exp_add]
  congr 1
  norm_cast
  simp only [mul_pow, sq_abs, Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + b ^ 2)]
  ring

theorem gaussianEuclideanSmoothingKernel_comp {ι : Type*} [Fintype ι]
    (c₁ c₂ : ℝ) (v₁ v₂ : ℝ≥0) :
    gaussianEuclideanSmoothingKernel (ι := ι) c₂ v₂ ∘ₖ
      gaussianEuclideanSmoothingKernel c₁ v₁ =
      gaussianEuclideanSmoothingKernel (c₂ * c₁)
        (c₂ ^ 2 * (v₁ : ℝ) + (v₂ : ℝ)).toNNReal := by
  let γ := GaussianProposal.primitiveGaussian ι
  let s₁ := Real.sqrt (v₁ : ℝ)
  let s₂ := Real.sqrt (v₂ : ℝ)
  let v := c₂ ^ 2 * (v₁ : ℝ) + (v₂ : ℝ)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hs : (c₂ * s₁) ^ 2 + s₂ ^ 2 = v := by
    dsimp [s₁, s₂, v]
    rw [mul_pow, Real.sq_sqrt v₁.coe_nonneg, Real.sq_sqrt v₂.coe_nonneg]
  apply Kernel.ext
  intro z
  have hj := congrArg Measure.snd (gaussianEuclideanSmoothing_compProd_eq_affine_map
    (gaussianEuclideanSmoothingKernel c₁ v₁ z) c₂ v₂)
  rw [Measure.snd_compProd] at hj
  change gaussianEuclideanSmoothingKernel c₂ v₂ ∘ₘ
    gaussianEuclideanSmoothingKernel c₁ v₁ z = _
  calc
    _ = ((gaussianEuclideanSmoothingKernel c₁ v₁ z).prod γ).map
        (fun p => c₂ • p.1 + s₂ • p.2) := by
      have hm : Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        (p.1, c₂ • p.1 + Real.sqrt (v₂ : ℝ) • p.2)) := by fun_prop
      simpa only [Measure.snd, Measure.map_map measurable_snd hm,
        Function.comp_def, s₂, γ] using hj
    _ = ((γ.prod γ).map (fun p => (c₂ * s₁) • p.1 + s₂ • p.2)).map
        (fun w => (c₂ * c₁) • z + w) := by
      rw [gaussianEuclideanSmoothingKernel_eq_affine_map]
      have hp : ((γ.map (fun w => c₁ • z + s₁ • w)).prod γ) =
          (γ.prod γ).map (Prod.map (fun w => c₁ • z + s₁ • w) id) := by
        rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id]
      rw [hp, Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext p
      ext i
      simp only [Function.comp_apply, Prod.map_apply', id_eq, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      ring
    _ = (γ.map (fun w => Real.sqrt v • w)).map (fun w => (c₂ * c₁) • z + w) := by
      rw [primitiveGaussian_weighted_sum_law, hs]
    _ = gaussianEuclideanSmoothingKernel (c₂ * c₁) v.toNNReal z := by
      rw [gaussianEuclideanSmoothingKernel_eq_affine_map,
        Measure.map_map (by fun_prop) (by fun_prop), Real.coe_toNNReal v hv]
      rfl

theorem gaussianEuclideanSmoothingKernel_comp_delta {ι : Type*} [Fintype ι]
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) :
    gaussianEuclideanSmoothingKernel (ι := ι) (Real.sqrt (1 - (δ : ℝ))) δ ∘ₖ
      gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ =
      gaussianEuclideanSmoothingKernel (1 - (δ : ℝ))
        ((δ : ℝ) * (2 - (δ : ℝ))).toNNReal := by
  have hc : Real.sqrt (1 - (δ : ℝ)) * Real.sqrt (1 - (δ : ℝ)) = 1 - (δ : ℝ) := by
    rw [← pow_two, Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hδ1))]
  have hv : (Real.sqrt (1 - (δ : ℝ))) ^ 2 * (δ : ℝ) + (δ : ℝ) =
      (δ : ℝ) * (2 - (δ : ℝ)) := by
    rw [Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hδ1))]
    ring
  simpa only [hc, hv] using gaussianEuclideanSmoothingKernel_comp
    (ι := ι) (Real.sqrt (1 - (δ : ℝ))) (Real.sqrt (1 - (δ : ℝ))) δ δ

theorem gaussianEuclideanSmoothingKernel_comp_delta_fresh_gaussian {ι : Type*} [Fintype ι]
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) (z : EuclideanSpace ℝ ι) :
    (gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ ∘ₖ
      gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ) z =
      (GaussianProposal.primitiveGaussian ι).map
        (fun noise => (1 - (δ : ℝ)) • z +
          Real.sqrt ((δ : ℝ) * (2 - (δ : ℝ))) • noise) := by
  rw [gaussianEuclideanSmoothingKernel_comp_delta δ hδ1,
    gaussianEuclideanSmoothingKernel_eq_affine_map, Real.coe_toNNReal _ (by
      exact mul_nonneg δ.coe_nonneg (by linarith [(show (δ : ℝ) ≤ 1 by exact_mod_cast hδ1)]))]

end SKConstants

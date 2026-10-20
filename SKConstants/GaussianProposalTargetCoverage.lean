module

public import SKConstants.ConditionalMixtureEntropy
public import SKConstants.GaussianGibbsRotation
public import SKConstants.MeasureEntropyCoverage

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def primitiveGibbsSpinKernel (n : ℕ) (beta sigma : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n × Fin n)) (Spin n) :=
  (gibbsKernel n beta).comap (GaussianProposal.goeMatrix sigma)
    (continuous_goeMatrix sigma).measurable

instance primitiveGibbsSpinKernel_isMarkov (n : ℕ) (beta sigma : ℝ) :
    IsMarkovKernel (primitiveGibbsSpinKernel n beta sigma) := by
  unfold primitiveGibbsSpinKernel
  infer_instance

theorem primitiveGibbsSpinKernel_singleton (n : ℕ) (beta sigma : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) (x : Spin n) :
    primitiveGibbsSpinKernel n beta sigma z {x} =
      ENNReal.ofReal (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x) := by
  change finiteWeightMeasure _ {x} = _
  rw [finiteWeightMeasure_apply _ _ (measurableSet_singleton x)]
  simp

theorem primitiveGibbsSpinKernel_pos_singleton (n : ℕ) (beta sigma : ℝ) :
    ∀ z x, primitiveGibbsSpinKernel n beta sigma z {x} ≠ 0 := by
  intro z x
  rw [primitiveGibbsSpinKernel_singleton]
  exact ENNReal.ofReal_ne_zero_iff.mpr (gibbsProbability_pos _ _ _)

theorem primitiveGibbsSpinKernel_klDiv (n : ℕ) (beta sigma : ℝ)
    (z w : EuclideanSpace ℝ (Fin n × Fin n)) :
    klDiv (primitiveGibbsSpinKernel n beta sigma z)
      (primitiveGibbsSpinKernel n beta sigma w) = ENNReal.ofReal
        (finiteKL (gibbsProbability beta (GaussianProposal.goeMatrix sigma z))
          (gibbsProbability beta (GaussianProposal.goeMatrix sigma w))) := by
  exact klDiv_finiteWeightMeasure _ _ (gibbsProbability_pos _ _)
    (gibbsProbability_pos _ _) (gibbsProbability_sum _ _) (gibbsProbability_sum _ _)

theorem actualGibbs_gaussian_perturbation_KL {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) :
    (∫⁻ p, klDiv
      (primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ))) p.1)
      (primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ))) p.2)
      ∂(GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ
        gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ)) ≤
      ENNReal.ofReal ((δ : ℝ) * (beta ^ 2 * ((n : ℝ) - 1) / 2)) := by
  let σ := primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ)))
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
      EuclideanSpace ℝ (Fin n × Fin n) => klDiv (σ p.1) (σ p.2)) :=
    measurable_klDiv_positive_finite_kernel
      (σ.comap Prod.fst measurable_fst) (σ.comap Prod.snd measurable_snd)
      (fun p x => primitiveGibbsSpinKernel_pos_singleton n beta _ p.1 x)
  rw [gaussianEuclideanSmoothing_compProd_eq_affine_map,
    lintegral_map hm (by fun_prop)]
  have he : (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
      EuclideanSpace ℝ (Fin n × Fin n) =>
        klDiv (σ p.1) (σ (Real.sqrt (1 - (δ : ℝ)) • p.1 + Real.sqrt (δ : ℝ) • p.2))) =
      fun p => ENNReal.ofReal (skGibbsRotationKL n beta (δ : ℝ) p) := by
    funext p
    exact primitiveGibbsSpinKernel_klDiv n beta _ _ _
  change (∫⁻ p, klDiv (σ p.1)
    (σ (Real.sqrt (1 - (δ : ℝ)) • p.1 + Real.sqrt (δ : ℝ) • p.2))
    ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) ≤ _
  rw [he]
  have hrot : (Real.sqrt (1 - (δ : ℝ))) ^ 2 + (Real.sqrt (δ : ℝ)) ^ 2 = 1 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hδ1)), Real.sq_sqrt δ.coe_nonneg]
    ring
  have hint := integrable_goeGibbsKL_rotation (n := n)
    (1 / Real.sqrt (2 * (n : ℝ))) beta _ _ hrot
  have hnn : 0 ≤ᵐ[(GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
      (GaussianProposal.primitiveGaussian (Fin n × Fin n))]
      (skGibbsRotationKL n beta (δ : ℝ)) := by
    filter_upwards with p
    exact finiteKL_nonneg _ _ (gibbsProbability_pos _ _) (gibbsProbability_pos _ _)
      (gibbsProbability_sum _ _) (gibbsProbability_sum _ _)
  have hInt : Integrable (skGibbsRotationKL n beta (δ : ℝ))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) := hint
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  exact ENNReal.ofReal_le_ofReal
    (skGibbsRotationKL_integral_le_delta hn beta δ δ.coe_nonneg (by exact_mod_cast hδ1))

theorem actualProposal_smoothed_gibbs_joint (n : ℕ) (beta sigma : ℝ)
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) :
    (smoothedProposalJointLaw n ((primitiveJointGibbsLaw n beta sigma).map Prod.swap)
      (Real.sqrt (1 - (δ : ℝ))) δ).map Prod.swap =
      GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ
        (primitiveGibbsSpinKernel n beta sigma ∘ₖ
          gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ) := by
  rw [smoothedProposalJointLaw_swap, Measure.map_map measurable_swap measurable_swap]
  simp only [Function.comp_def, Prod.swap_swap, Measure.map_id']
  change (gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ ∥ₖ
    (Kernel.id : Kernel (Spin n) (Spin n))) ∘ₘ
    (GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ
      primitiveGibbsSpinKernel n beta sigma) = _
  exact reversibleKernel_output_disintegration _ _
    (gaussianEuclideanSmoothing_reversible δ hδ1) (primitiveGibbsSpinKernel n beta sigma)

theorem actualProposal_original_target_average_KL {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hspin : Q.fst = uniformSpinLaw n)
    (hgauss : Q.snd = GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (δ : ℝ≥0) (hδ : δ ≠ 0) (hδ1 : δ < 1) :
    (∫⁻ p, klDiv
      (primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ))) p.1)
      (regressionProposalSpinKernel n Q δ p.2)
      ∂(GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ
        gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ)) ≤
      ENNReal.ofReal ((δ : ℝ) * (beta ^ 2 * ((n : ℝ) - 1) / 2)) +
        ENNReal.ofReal (1 / (δ : ℝ)) * klDiv Q
          ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) := by
  let P := (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap
  let γ : Measure (EuclideanSpace ℝ (Fin n × Fin n)) :=
    GaussianProposal.primitiveGaussian (Fin n × Fin n)
  let κ : Kernel (EuclideanSpace ℝ (Fin n × Fin n))
      (EuclideanSpace ℝ (Fin n × Fin n)) := gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ
  let σ := primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ)))
  let ν := regressionProposalSpinKernel n Q δ
  have hle := reversibleKernel_original_target_KL_le γ κ
    (gaussianEuclideanSmoothing_reversible δ hδ1.le) σ ν
    (primitiveGibbsSpinKernel_pos_singleton n beta _)
  have hrev := actualProposal_reverse_smoothed_KL_delta n beta Q hspin δ hδ hδ1
  have he : klDiv (smoothedProposalJointLaw n P (Real.sqrt (1 - (δ : ℝ))) δ)
      (smoothedProposalJointLaw n Q (Real.sqrt (1 - (δ : ℝ))) δ) =
      klDiv (γ ⊗ₘ (σ ∘ₖ κ)) (γ ⊗ₘ ν) := by
    rw [← klDiv_map_prod_swap]
    rw [actualProposal_smoothed_gibbs_joint n beta _ δ hδ1.le,
      actualProposal_smoothed_spin_regression n Q hgauss δ hδ1.le]
  rw [he] at hrev
  exact hle.trans (add_le_add (actualGibbs_gaussian_perturbation_KL hn beta δ hδ1.le) hrev)

theorem actualProposal_original_target_average_KL_of_forward_budget {n : ℕ}
    (hn : 0 < n) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hspin : Q.fst = uniformSpinLaw n)
    (hgauss : Q.snd = GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (δ : ℝ≥0) (hδ : δ ≠ 0) (hδ1 : δ < 1) (K : ℝ) (hK : 0 ≤ K)
    (hforward : klDiv Q
      ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) ≤
        ENNReal.ofReal K) :
    (∫⁻ p, klDiv
      (primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ))) p.1)
      (regressionProposalSpinKernel n Q δ p.2)
      ∂(GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ
        gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ)) ≤
      ENNReal.ofReal ((δ : ℝ) * (beta ^ 2 * ((n : ℝ) - 1) / 2) + K / (δ : ℝ)) := by
  have h := actualProposal_original_target_average_KL hn beta Q hspin hgauss δ hδ hδ1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : 0 ≤ (δ : ℝ) * (beta ^ 2 * ((n : ℝ) - 1) / 2) := by positivity
  have hd : 0 ≤ 1 / (δ : ℝ) := by positivity
  have he : ENNReal.ofReal ((δ : ℝ) * (beta ^ 2 * ((n : ℝ) - 1) / 2)) +
      ENNReal.ofReal (1 / (δ : ℝ)) * ENNReal.ofReal K =
      ENNReal.ofReal ((δ : ℝ) * (beta ^ 2 * ((n : ℝ) - 1) / 2) + K / (δ : ℝ)) := by
    rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_add hc (mul_nonneg hd hK)]
    congr 1
    ring
  have hb : ENNReal.ofReal (1 / (δ : ℝ)) * klDiv Q
      ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) ≤
      ENNReal.ofReal (1 / (δ : ℝ)) * ENNReal.ofReal K := by
    gcongr
  exact (h.trans (add_le_add le_rfl hb)).trans_eq he

def actualProposalOriginalTargetKL (n : ℕ) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (δ : ℝ≥0)
    (p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n)) : ℝ≥0∞ :=
  klDiv (primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ))) p.1)
    (regressionProposalSpinKernel n Q δ
      (gaussianRotation (Real.sqrt (1 - (δ : ℝ))) (Real.sqrt (δ : ℝ)) p))

theorem measurable_actualProposalOriginalTargetKL (n : ℕ) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (δ : ℝ≥0) : Measurable (actualProposalOriginalTargetKL n beta Q δ) := by
  exact measurable_klDiv_positive_finite_kernel
    ((primitiveGibbsSpinKernel n beta _).comap Prod.fst measurable_fst)
    ((regressionProposalSpinKernel n Q δ).comap
      (gaussianRotation (Real.sqrt (1 - (δ : ℝ))) (Real.sqrt (δ : ℝ))) (by
        unfold gaussianRotation
        fun_prop))
    (fun p x => primitiveGibbsSpinKernel_pos_singleton n beta _ p.1 x)

theorem actualProposal_original_target_fresh_average_KL {n : ℕ}
    (hn : 0 < n) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hspin : Q.fst = uniformSpinLaw n)
    (hgauss : Q.snd = GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (δ : ℝ≥0) (hδ : δ ≠ 0) (hδ1 : δ < 1) (K : ℝ) (hK : 0 ≤ K)
    (hforward : klDiv Q
      ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) ≤
        ENNReal.ofReal K) :
    (∫⁻ p, actualProposalOriginalTargetKL n beta Q δ p
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) ≤
      ENNReal.ofReal ((δ : ℝ) * (beta ^ 2 * ((n : ℝ) - 1) / 2) + K / (δ : ℝ)) := by
  have h := actualProposal_original_target_average_KL_of_forward_budget
    hn beta Q hspin hgauss δ hδ hδ1 K hK hforward
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
      EuclideanSpace ℝ (Fin n × Fin n) => klDiv
        (primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ))) p.1)
        (regressionProposalSpinKernel n Q δ p.2)) :=
    measurable_klDiv_positive_finite_kernel
      ((primitiveGibbsSpinKernel n beta _).comap Prod.fst measurable_fst)
      ((regressionProposalSpinKernel n Q δ).comap Prod.snd measurable_snd)
      (fun p x => primitiveGibbsSpinKernel_pos_singleton n beta _ p.1 x)
  rw [gaussianEuclideanSmoothing_compProd_eq_affine_map, lintegral_map hm (by fun_prop)] at h
  exact h

theorem actualProposal_original_target_KL_tail {n : ℕ}
    (hn : 0 < n) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hspin : Q.fst = uniformSpinLaw n)
    (hgauss : Q.snd = GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (δ : ℝ≥0) (hδ : δ ≠ 0) (hδ1 : δ < 1) (K : ℝ) (hK : 0 ≤ K)
    (hforward : klDiv Q
      ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) ≤
        ENNReal.ofReal K) (t : ℝ) (ht : 0 < t) :
    ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)))
        {p | ENNReal.ofReal t ≤ actualProposalOriginalTargetKL n beta Q δ p} ≤
      ENNReal.ofReal ((δ : ℝ) * (beta ^ 2 * ((n : ℝ) - 1) / 2) + K / (δ : ℝ)) /
        ENNReal.ofReal t := by
  have h := meas_ge_le_lintegral_div
    (μ := (GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)))
    (measurable_actualProposalOriginalTargetKL n beta Q δ).aemeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top
  exact h.trans (ENNReal.div_le_div_right
    (actualProposal_original_target_fresh_average_KL hn beta Q hspin hgauss δ hδ hδ1 K hK hforward) _)

theorem actualProposal_original_target_entropy_coverage (n : ℕ) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (δ : ℝ≥0) (target base : EuclideanSpace ℝ (Fin n × Fin n))
    (A : Finset (Spin n)) (T alpha : ℝ) (hT : 0 ≤ T) (halpha : 0 < alpha)
    (hKL : klDiv (primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ))) target)
      (regressionProposalSpinKernel n Q δ base) ≤ ENNReal.ofReal T)
    (hMass : alpha ≤ (primitiveGibbsSpinKernel n beta
      (1 / Real.sqrt (2 * (n : ℝ))) target).real (A : Set (Spin n))) :
    Real.exp (-(T + Real.log 2) / alpha) ≤
      (regressionProposalSpinKernel n Q δ base).real (A : Set (Spin n)) := by
  let μ := primitiveGibbsSpinKernel n beta (1 / Real.sqrt (2 * (n : ℝ))) target
  let ν := regressionProposalSpinKernel n Q δ base
  have hac : μ ≪ ν := (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL)).1
  have hp : ∀ x, 0 < μ.real {x} := by
    intro x
    exact ENNReal.toReal_pos (primitiveGibbsSpinKernel_pos_singleton n beta _ target x)
      (measure_ne_top _ _)
  have hq : ∀ x, 0 < ν.real {x} := by
    intro x
    apply ENNReal.toReal_pos _ (measure_ne_top _ _)
    intro hx
    exact primitiveGibbsSpinKernel_pos_singleton n beta _ target x (hac hx)
  exact measureKL_finite_endpoint_coverage μ ν id measurable_id hp hq A T alpha hT hKL halpha hMass

end SKConstants

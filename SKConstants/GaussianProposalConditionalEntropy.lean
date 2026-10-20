module

public import SKConstants.GaussianProposalConditionalRegression
public import Mathlib.Probability.Kernel.Disintegration.Unique

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def spinPreservingGaussianSmoothingKernel (n : ℕ) (c : ℝ) (v : ℝ≥0) :
    Kernel (Spin n × EuclideanSpace ℝ (Fin n × Fin n))
      (Spin n × EuclideanSpace ℝ (Fin n × Fin n)) :=
  Kernel.id ∥ₖ gaussianEuclideanSmoothingKernel c v

instance spinPreservingGaussianSmoothingKernel_isMarkov (n : ℕ) (c : ℝ) (v : ℝ≥0) :
    IsMarkovKernel (spinPreservingGaussianSmoothingKernel n c v) := by
  unfold spinPreservingGaussianSmoothingKernel
  infer_instance

def smoothedProposalJointLaw (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n)))
    (c : ℝ) (v : ℝ≥0) : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n)) :=
  spinPreservingGaussianSmoothingKernel n c v ∘ₘ Q

instance smoothedProposalJointLaw_isProbability (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (c : ℝ) (v : ℝ≥0) : IsProbabilityMeasure (smoothedProposalJointLaw n Q c v) := by
  unfold smoothedProposalJointLaw
  infer_instance

def proposalConditionalDisorderKernel (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q] :
    Kernel (Spin n) (EuclideanSpace ℝ (Fin n × Fin n)) := Q.condKernel

instance proposalConditionalDisorderKernel_isMarkov (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q] :
    IsMarkovKernel (proposalConditionalDisorderKernel n Q) := by
  unfold proposalConditionalDisorderKernel
  infer_instance

theorem proposalJointLaw_eq_uniform_conditional (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hspin : Q.fst = uniformSpinLaw n) :
    Q = uniformSpinLaw n ⊗ₘ proposalConditionalDisorderKernel n Q := by
  rw [← hspin]
  exact (Measure.disintegrate Q Q.condKernel).symm

theorem smoothedProposalJointLaw_eq_uniform_conditional (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hspin : Q.fst = uniformSpinLaw n) (c : ℝ) (v : ℝ≥0) :
    smoothedProposalJointLaw n Q c v = uniformSpinLaw n ⊗ₘ
      (gaussianEuclideanSmoothingKernel c v ∘ₖ proposalConditionalDisorderKernel n Q) := by
  unfold smoothedProposalJointLaw spinPreservingGaussianSmoothingKernel
  calc
    _ = (Kernel.id ∥ₖ gaussianEuclideanSmoothingKernel c v) ∘ₘ
        (uniformSpinLaw n ⊗ₘ proposalConditionalDisorderKernel n Q) :=
      congrArg (fun μ => (Kernel.id ∥ₖ gaussianEuclideanSmoothingKernel c v) ∘ₘ μ)
        (proposalJointLaw_eq_uniform_conditional n Q hspin)
    _ = _ := Measure.parallelComp_comp_compProd

theorem primitiveJointGibbsLaw_sk_eq_uniform_conditional (n : ℕ) (beta : ℝ) :
    (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap =
      uniformSpinLaw n ⊗ₘ conditionalGibbsGaussianKernel n beta
        (1 / Real.sqrt (2 * (n : ℝ))) := by
  rw [primitiveJointGibbsLaw_disintegrated, conditionalGibbsSpinLaw_sk]
  rfl

theorem actualProposal_reverse_smoothed_KL (n : ℕ) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hspin : Q.fst = uniformSpinLaw n) (c : ℝ) (hc : c ≠ 0)
    (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (smoothedProposalJointLaw n
      ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) c v)
      (smoothedProposalJointLaw n Q c v) ≤
      ENNReal.ofReal (c ^ 2 / (v : ℝ)) *
        klDiv Q ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) := by
  have h := conditionalGibbs_common_spin_reverse_smoothing_KL n beta
    (1 / Real.sqrt (2 * (n : ℝ))) (uniformSpinLaw n)
    (proposalConditionalDisorderKernel n Q) c hc v hv
  have hp : smoothedProposalJointLaw n
      ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) c v =
      uniformSpinLaw n ⊗ₘ (gaussianEuclideanSmoothingKernel c v ∘ₖ
        conditionalGibbsGaussianKernel n beta (1 / Real.sqrt (2 * (n : ℝ)))) := by
    unfold smoothedProposalJointLaw spinPreservingGaussianSmoothingKernel
    rw [primitiveJointGibbsLaw_sk_eq_uniform_conditional,
      Measure.parallelComp_comp_compProd]
  calc
    _ = klDiv (uniformSpinLaw n ⊗ₘ (gaussianEuclideanSmoothingKernel c v ∘ₖ
        conditionalGibbsGaussianKernel n beta (1 / Real.sqrt (2 * (n : ℝ)))))
        (uniformSpinLaw n ⊗ₘ (gaussianEuclideanSmoothingKernel c v ∘ₖ
          proposalConditionalDisorderKernel n Q)) := by
      rw [hp, smoothedProposalJointLaw_eq_uniform_conditional n Q hspin c v]
    _ ≤ ENNReal.ofReal (c ^ 2 / (v : ℝ)) *
        klDiv (uniformSpinLaw n ⊗ₘ proposalConditionalDisorderKernel n Q)
          (uniformSpinLaw n ⊗ₘ conditionalGibbsGaussianKernel n beta
            (1 / Real.sqrt (2 * (n : ℝ)))) := h
    _ = _ := by
      rw [← proposalJointLaw_eq_uniform_conditional n Q hspin,
        ← primitiveJointGibbsLaw_sk_eq_uniform_conditional n beta]

theorem actualProposal_reverse_smoothed_KL_delta (n : ℕ) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hspin : Q.fst = uniformSpinLaw n) (δ : ℝ≥0) (hδ : δ ≠ 0) (hδ1 : δ < 1) :
    klDiv (smoothedProposalJointLaw n
      ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap)
        (Real.sqrt (1 - (δ : ℝ))) δ)
      (smoothedProposalJointLaw n Q (Real.sqrt (1 - (δ : ℝ))) δ) ≤
      ENNReal.ofReal (1 / (δ : ℝ)) *
        klDiv Q ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) := by
  have h := actualProposal_reverse_smoothed_KL n beta Q hspin
    (Real.sqrt (1 - (δ : ℝ))) (Real.sqrt_pos.mpr
      (sub_pos.mpr (by exact_mod_cast hδ1))).ne' δ hδ
  refine h.trans ?_
  have hc : ENNReal.ofReal ((Real.sqrt (1 - (δ : ℝ))) ^ 2 / (δ : ℝ)) ≤
      ENNReal.ofReal (1 / (δ : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hδ1.le))]
    exact div_le_div_of_nonneg_right (sub_le_self _ δ.coe_nonneg) δ.coe_nonneg
  gcongr

def proposalConditionalSpinKernel (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q] :
    Kernel (EuclideanSpace ℝ (Fin n × Fin n)) (Spin n) :=
  (Q.map Prod.swap).condKernel

instance proposalConditionalSpinKernel_isMarkov (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q] :
    IsMarkovKernel (proposalConditionalSpinKernel n Q) := by
  unfold proposalConditionalSpinKernel
  infer_instance

theorem proposalJointLaw_swap_eq_gaussian_conditional (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hgauss : Q.snd = GaussianProposal.primitiveGaussian (Fin n × Fin n)) :
    Q.map Prod.swap = GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ
      proposalConditionalSpinKernel n Q := by
  have h := Measure.disintegrate (Q.map Prod.swap) (Q.map Prod.swap).condKernel
  rw [Measure.fst_map_swap, hgauss] at h
  exact h.symm

def regressionProposalSpinKernel (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (δ : ℝ≥0) : Kernel (EuclideanSpace ℝ (Fin n × Fin n)) (Spin n) :=
  proposalConditionalSpinKernel n Q ∘ₖ
    gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ

instance regressionProposalSpinKernel_isMarkov (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (δ : ℝ≥0) : IsMarkovKernel (regressionProposalSpinKernel n Q δ) := by
  unfold regressionProposalSpinKernel
  infer_instance

theorem regressionProposalSpinKernel_apply_fresh_gaussian (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (δ : ℝ≥0) (base : EuclideanSpace ℝ (Fin n × Fin n))
    (A : Set (Spin n)) (hA : MeasurableSet A) :
    regressionProposalSpinKernel n Q δ base A =
      ∫⁻ noise, proposalConditionalSpinKernel n Q
        (Real.sqrt (1 - (δ : ℝ)) • base + Real.sqrt (δ : ℝ) • noise) A
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
  rw [regressionProposalSpinKernel, Kernel.comp_apply' _ _ _ hA,
    gaussianEuclideanSmoothingKernel_eq_affine_map,
    lintegral_map ((proposalConditionalSpinKernel n Q).measurable_coe hA) (by fun_prop)]

theorem primitiveJointGibbsLaw_disorder_marginal (n : ℕ) (beta sigma : ℝ) :
    (primitiveJointGibbsLaw n beta sigma).fst =
      GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
  unfold primitiveJointGibbsLaw
  exact Measure.fst_compProd _ _

theorem smoothedProposalJointLaw_swap (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) (c : ℝ) (v : ℝ≥0) :
    (smoothedProposalJointLaw n Q c v).map Prod.swap =
      (gaussianEuclideanSmoothingKernel c v ∥ₖ (Kernel.id : Kernel (Spin n) (Spin n))) ∘ₘ
        Q.map Prod.swap := by
  unfold smoothedProposalJointLaw spinPreservingGaussianSmoothingKernel
  rw [← Measure.deterministic_comp_eq_map measurable_swap,
    Measure.comp_assoc]
  change (Kernel.swap (Spin n) (EuclideanSpace ℝ (Fin n × Fin n)) ∘ₖ
    (Kernel.id ∥ₖ gaussianEuclideanSmoothingKernel c v)) ∘ₘ Q = _
  rw [Kernel.swap_parallelComp,
    ← Measure.comp_assoc, Kernel.swap, Measure.deterministic_comp_eq_map measurable_swap]

theorem actualProposal_smoothed_spin_regression (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hgauss : Q.snd = GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) :
    (smoothedProposalJointLaw n Q (Real.sqrt (1 - (δ : ℝ))) δ).map Prod.swap =
      GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ
        regressionProposalSpinKernel n Q δ := by
  rw [smoothedProposalJointLaw_swap]
  calc
    _ = (gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ ∥ₖ
        (Kernel.id : Kernel (Spin n) (Spin n))) ∘ₘ
        (GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ
          proposalConditionalSpinKernel n Q) :=
      congrArg (fun μ => (gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ ∥ₖ
        (Kernel.id : Kernel (Spin n) (Spin n))) ∘ₘ μ)
          (proposalJointLaw_swap_eq_gaussian_conditional n Q hgauss)
    _ = _ := reversibleKernel_output_disintegration _ _
      (gaussianEuclideanSmoothing_reversible δ hδ1) (proposalConditionalSpinKernel n Q)

theorem actualProposal_smoothed_disorder_marginal (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hgauss : Q.snd = GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) :
    (smoothedProposalJointLaw n Q (Real.sqrt (1 - (δ : ℝ))) δ).snd =
      GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
  have h := congrArg Measure.fst (actualProposal_smoothed_spin_regression n Q hgauss δ hδ1)
  simpa only [Measure.fst_map_swap, Measure.fst_compProd] using h

theorem actualProposal_smoothed_conditional_spin_eq_regression_ae (n : ℕ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hgauss : Q.snd = GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (δ : ℝ≥0) (hδ1 : δ ≤ 1) :
    ∀ᵐ base ∂GaussianProposal.primitiveGaussian (Fin n × Fin n),
      regressionProposalSpinKernel n Q δ base =
        proposalConditionalSpinKernel n
          (smoothedProposalJointLaw n Q (Real.sqrt (1 - (δ : ℝ))) δ) base := by
  have h := eq_condKernel_of_measure_eq_compProd (regressionProposalSpinKernel n Q δ)
    (ρ := (smoothedProposalJointLaw n Q (Real.sqrt (1 - (δ : ℝ))) δ).map Prod.swap) (by
      rw [Measure.fst_map_swap, actualProposal_smoothed_disorder_marginal n Q hgauss δ hδ1]
      exact actualProposal_smoothed_spin_regression n Q hgauss δ hδ1)
  rwa [Measure.fst_map_swap, actualProposal_smoothed_disorder_marginal n Q hgauss δ hδ1] at h

theorem actualProposal_regression_average_KL (n : ℕ) (beta : ℝ)
    (Q : Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure Q]
    (hspin : Q.fst = uniformSpinLaw n)
    (hgauss : Q.snd = GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (δ : ℝ≥0) (hδ : δ ≠ 0) (hδ1 : δ < 1) :
    (∫⁻ base, klDiv
      (regressionProposalSpinKernel n
        ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) δ base)
      (regressionProposalSpinKernel n Q δ base)
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤
      ENNReal.ofReal (1 / (δ : ℝ)) *
        klDiv Q ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) := by
  let P := (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap
  let γ := GaussianProposal.primitiveGaussian (Fin n × Fin n)
  let ka := regressionProposalSpinKernel n P δ
  let kb := regressionProposalSpinKernel n Q δ
  have hPgauss : P.snd = γ := by
    rw [Measure.snd_map_swap, primitiveJointGibbsLaw_disorder_marginal]
  have h := actualProposal_reverse_smoothed_KL_delta n beta Q hspin δ hδ hδ1
  have he : klDiv (smoothedProposalJointLaw n P (Real.sqrt (1 - (δ : ℝ))) δ)
      (smoothedProposalJointLaw n Q (Real.sqrt (1 - (δ : ℝ))) δ) =
      klDiv (γ ⊗ₘ ka) (γ ⊗ₘ kb) := by
    rw [← klDiv_map_measurableEquiv _ _
      (MeasurableEquiv.prodComm : Spin n × EuclideanSpace ℝ (Fin n × Fin n) ≃ᵐ
        EuclideanSpace ℝ (Fin n × Fin n) × Spin n)]
    change klDiv ((smoothedProposalJointLaw n P (Real.sqrt (1 - (δ : ℝ))) δ).map Prod.swap)
      ((smoothedProposalJointLaw n Q (Real.sqrt (1 - (δ : ℝ))) δ).map Prod.swap) = _
    rw [actualProposal_smoothed_spin_regression n P hPgauss δ hδ1.le,
      actualProposal_smoothed_spin_regression n Q hgauss δ hδ1.le]
  change klDiv (smoothedProposalJointLaw n P (Real.sqrt (1 - (δ : ℝ))) δ)
      (smoothedProposalJointLaw n Q (Real.sqrt (1 - (δ : ℝ))) δ) ≤
      ENNReal.ofReal (1 / (δ : ℝ)) * klDiv Q P at h
  rw [he] at h
  change (∫⁻ base, klDiv (ka base) (kb base) ∂γ) ≤
    ENNReal.ofReal (1 / (δ : ℝ)) * klDiv Q P
  by_cases hD : klDiv Q P = ⊤
  · have hc : ENNReal.ofReal (1 / (δ : ℝ)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (one_div_pos.mpr
        (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hδ)))
    rw [hD, ENNReal.mul_top hc]
    exact le_top
  · have hfinite : klDiv (γ ⊗ₘ ka) (γ ⊗ₘ kb) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD) h
    have hac := (klDiv_ne_top_iff.mp hfinite).1.kernel_of_compProd
    rw [klDiv_compProd_same_left_eq_lintegral_ae γ ka kb hac] at h
    exact h

end SKConstants

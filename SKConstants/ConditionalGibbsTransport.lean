module

public import SKConstants.ConditionalGibbsConvexity
public import SKConstants.TransportEntropy

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal Topology BoundedContinuousFunction

namespace SKConstants
open Transport

def conditionalNormalizedGibbsPotential {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  conditionalGibbsPotential beta sigma x z -
    Real.log ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin n × Fin n) /
      conditionalGibbsSpinMass beta sigma x)

theorem conditionalNormalizedGibbsPotential_strongConvex {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) :
    StrongConvexOn univ 1 (conditionalNormalizedGibbsPotential beta sigma x) := by
  have hu := conditionalGibbsPotential_strongConvex beta sigma x
  refine ⟨hu.1, ?_⟩
  intro z hz w hw a b ha hb hab
  have h := hu.2 hz hw ha hb hab
  simp only [conditionalNormalizedGibbsPotential, smul_eq_mul] at *
  have hc := congrArg (fun t : ℝ => t * Real.log
    ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin n × Fin n) /
      conditionalGibbsSpinMass beta sigma x)) hab
  nlinarith

theorem continuous_conditionalNormalizedGibbsPotential {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) :
    Continuous (conditionalNormalizedGibbsPotential beta sigma x) :=
  (continuous_conditionalGibbsPotential beta sigma x).sub continuous_const

theorem conditionalGibbsGaussianLaw_eq_exp_normalized {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) :
    conditionalGibbsGaussianLaw beta sigma x =
      expPotentialLaw (conditionalNormalizedGibbsPotential beta sigma x) := by
  rw [conditionalGibbsGaussianLaw_eq_exp_potential, expPotentialLaw]
  congr 1
  funext z
  congr 1
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin n × Fin n) /
      conditionalGibbsSpinMass beta sigma x :=
    div_pos (pow_pos (inv_pos.mpr (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos))) _)
      (conditionalGibbsSpinMass_pos beta sigma x)
  rw [conditionalNormalizedGibbsPotential, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hc]

instance conditionalNormalizedGibbsPotential_isProbability {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) :
    IsProbabilityMeasure (expPotentialLaw (conditionalNormalizedGibbsPotential beta sigma x)) := by
  rw [← conditionalGibbsGaussianLaw_eq_exp_normalized]
  infer_instance

theorem conditionalGibbs_hopf_log_mgf_le {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (f : EuclideanSpace ℝ (Fin n × Fin n) →ᵇ ℝ) :
    Real.log (mgf (boundedHopf f) (conditionalGibbsGaussianLaw beta sigma x) 1) ≤
      ∫ z, f z ∂conditionalGibbsGaussianLaw beta sigma x := by
  rw [conditionalGibbsGaussianLaw_eq_exp_normalized]
  exact strongConvex_hopf_log_mgf_le _
    (continuous_conditionalNormalizedGibbsPotential beta sigma x).measurable
    (conditionalNormalizedGibbsPotential_strongConvex beta sigma x) f

theorem conditionalGibbs_exists_coupling_cost_le_two_klDiv {n : ℕ}
    (beta sigma : ℝ) (x : Spin n)
    (μ : Measure (EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure μ] :
    ∃ q : Measure (EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n)),
      IsProbabilityMeasure q ∧ q.map Prod.fst = μ ∧
      q.map Prod.snd = conditionalGibbsGaussianLaw beta sigma x ∧
      (∫⁻ p, edist p.1 p.2 ^ 2 ∂q) ≤
        2 * klDiv μ (conditionalGibbsGaussianLaw beta sigma x) := by
  rw [conditionalGibbsGaussianLaw_eq_exp_normalized]
  exact strongConvex_exists_coupling_cost_le_two_klDiv _
    (continuous_conditionalNormalizedGibbsPotential beta sigma x).measurable
    (conditionalNormalizedGibbsPotential_strongConvex beta sigma x) μ

end SKConstants

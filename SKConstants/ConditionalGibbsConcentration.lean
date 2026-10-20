module

public import SKConstants.ConditionalGibbsTransport
public import SKConstants.ConditionalGibbsMeans
public import SKConstants.StrongConvexConcentration
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem conditionalGibbs_lipschitz_hasSubgaussianMGF {n : ℕ} (beta sigma : ℝ)
    (x : Spin n) {f : EuclideanSpace ℝ (Fin n × Fin n) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hfi : Integrable f (conditionalGibbsGaussianLaw beta sigma x)) :
    HasSubgaussianMGF (fun z => f z - ∫ y, f y ∂conditionalGibbsGaussianLaw beta sigma x)
      (L^2) (conditionalGibbsGaussianLaw beta sigma x) := by
  rw [conditionalGibbsGaussianLaw_eq_exp_normalized] at hfi ⊢
  exact Transport.strongConvex_lipschitz_hasSubgaussianMGF _
    (continuous_conditionalNormalizedGibbsPotential beta sigma x).measurable
    (conditionalNormalizedGibbsPotential_strongConvex beta sigma x) hf hfi

theorem conditionalGibbs_linearForm_integrable {n : ℕ} (beta sigma : ℝ)
    (x : Spin n) (a : (Fin n × Fin n) → ℝ) :
    Integrable (GaussianProposal.linearForm a) (conditionalGibbsGaussianLaw beta sigma x) := by
  exact integrable_finsetSum Finset.univ (fun i _ =>
    (conditionalGibbsGaussianLaw_coordinate_integrable beta sigma x i).const_mul (a i))

theorem gaussianProposal_linearForm_eq_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (z : EuclideanSpace ℝ ι) :
    GaussianProposal.linearForm a z = inner (𝕜 := ℝ) (toLp 2 a) z := by
  simp [GaussianProposal.linearForm, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, mul_comm]

theorem gaussianProposal_linearForm_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) :
    LipschitzWith ‖toLp 2 a‖₊ (GaussianProposal.linearForm a) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq, gaussianProposal_linearForm_eq_inner,
    gaussianProposal_linearForm_eq_inner, ← inner_sub_right, dist_eq_norm]
  exact abs_real_inner_le_norm _ _

theorem conditionalGibbs_linearForm_hasSubgaussianMGF {n : ℕ} (beta sigma : ℝ)
    (x : Spin n) (a : (Fin n × Fin n) → ℝ) :
    HasSubgaussianMGF (fun z => GaussianProposal.linearForm a z -
      ∫ y, GaussianProposal.linearForm a y ∂conditionalGibbsGaussianLaw beta sigma x)
      (‖toLp 2 a‖₊^2) (conditionalGibbsGaussianLaw beta sigma x) :=
  conditionalGibbs_lipschitz_hasSubgaussianMGF beta sigma x
    (gaussianProposal_linearForm_lipschitz a) (conditionalGibbs_linearForm_integrable beta sigma x a)

theorem conditionalGibbs_linearForm_mean {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (a : (Fin n × Fin n) → ℝ) :
    (∫ z, GaussianProposal.linearForm a z ∂conditionalGibbsGaussianLaw beta sigma x) =
      ∑ i, a i * ∫ z : EuclideanSpace ℝ (Fin n × Fin n), z i
        ∂conditionalGibbsGaussianLaw beta sigma x := by
  unfold GaussianProposal.linearForm
  rw [integral_finsetSum _ (fun i _ =>
    (conditionalGibbsGaussianLaw_coordinate_integrable beta sigma x i).const_mul (a i))]
  simp only [integral_const_mul]

theorem abs_conditionalGibbs_linearForm_mean_le {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (a : (Fin n × Fin n) → ℝ) :
    |∫ z, GaussianProposal.linearForm a z ∂conditionalGibbsGaussianLaw beta sigma x| ≤
      (2 * |beta| * |sigma|) * ∑ i, |a i| := by
  rw [conditionalGibbs_linearForm_mean]
  calc
    _ ≤ ∑ i, |a i * ∫ z : EuclideanSpace ℝ (Fin n × Fin n), z i
        ∂conditionalGibbsGaussianLaw beta sigma x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * (2 * |beta| * |sigma|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_conditionalGibbsGaussianLaw_coordinate_mean_le beta sigma x i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end SKConstants

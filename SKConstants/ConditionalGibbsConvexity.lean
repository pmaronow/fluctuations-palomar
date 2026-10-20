module

public import SKConstants.GibbsVariational
public import SKConstants.GaussianLebesgueDensity
public import SKConstants.SKGibbsGauge
public import SKConstants.GaussianGibbsInterpolation
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal ContDiff
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def conditionalGibbsPotential {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  ‖z‖ ^ 2 / 2 - beta * goeSpinHamiltonian sigma x z +
    Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z))

theorem convexOn_goeGibbsPressure {n : ℕ} (beta sigma : ℝ) :
    ConvexOn ℝ univ (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
      Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z))) := by
  refine ⟨convex_univ, ?_⟩
  intro z hz w hw a b ha hb hab
  let v := a • z + b • w
  let q := gibbsProbability beta (GaussianProposal.goeMatrix sigma v)
  have hq : ∀ x, 0 < q x := gibbsProbability_pos _ _
  have hqs : ∑ x, q x = 1 := gibbsProbability_sum _ _
  have hself : finiteKL q q = 0 := by
    unfold finiteKL
    simp only [div_self (hq _).ne', Real.log_one, mul_zero, Finset.sum_const_zero]
  have hv := finiteGibbs_entropy_energy_identity beta
    (GaussianProposal.goeMatrix sigma v) q hq hqs
  change finiteKL q q = _ at hv
  rw [hself] at hv
  have hzv := finiteGibbs_variational_bound beta (GaussianProposal.goeMatrix sigma z) q hq hqs
  have hwv := finiteGibbs_variational_bound beta (GaussianProposal.goeMatrix sigma w) q hq hqs
  have hlin : (∑ x, q x * quadraticHamiltonian (GaussianProposal.goeMatrix sigma v) x) =
      a * (∑ x, q x * quadraticHamiltonian (GaussianProposal.goeMatrix sigma z) x) +
      b * (∑ x, q x * quadraticHamiltonian (GaussianProposal.goeMatrix sigma w) x) := by
    change (∑ x, q x * goeSpinHamiltonian sigma x (a • z + b • w)) = _
    simp_rw [goeSpinHamiltonian_linear_combination]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, goeSpinHamiltonian]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;> ring
  rw [hlin] at hv
  change Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma v)) ≤ _
  simp only [smul_eq_mul]
  have hzmul := mul_le_mul_of_nonneg_left hzv ha
  have hwmul := mul_le_mul_of_nonneg_left hwv hb
  have hentropy := congrArg (fun t : ℝ => t * finiteShannonEntropy q) hab
  nlinarith [hentropy]

theorem conditionalGibbsPotential_strongConvex {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    StrongConvexOn univ 1 (conditionalGibbsPotential beta sigma x) := by
  rw [strongConvexOn_iff_convex]
  refine ⟨convex_univ, ?_⟩
  intro z hz w hw a b ha hb hab
  have hp := (convexOn_goeGibbsPressure (n := n) beta sigma).2 hz hw ha hb hab
  have hl := goeSpinHamiltonian_linear_combination sigma a b x z w
  simp only [conditionalGibbsPotential, smul_eq_mul, hl] at *
  linarith

theorem continuous_conditionalGibbsPotential {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    Continuous (conditionalGibbsPotential beta sigma x) := by
  unfold conditionalGibbsPotential goeSpinHamiltonian
  apply Continuous.add
  · exact ((continuous_norm.pow 2).div_const 2).sub
      (continuous_const.mul ((continuous_quadraticHamiltonian x).comp (continuous_goeMatrix sigma)))
  · exact (continuous_gibbsPartition beta).comp (continuous_goeMatrix sigma) |>.log
      (fun z => (gibbsPartition_pos beta _).ne')

theorem contDiff_conditionalGibbsPotential {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (m : ℕ∞ω) : ContDiff ℝ m (conditionalGibbsPotential beta sigma x) := by
  have hH (x : Spin n) : ContDiff ℝ m (goeSpinHamiltonian sigma x) := by
    have heq : goeSpinHamiltonian sigma x =
        GaussianProposal.linearFormCLM (spinGaussianCoefficient sigma x) := by
      funext z
      rw [GaussianProposal.linearFormCLM_apply, GaussianProposal.linearForm,
        goeSpinHamiltonian_eq_linear]
    rw [heq]
    exact ContinuousLinearMap.contDiff _
  have hZ : ContDiff ℝ m
      (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
        gibbsPartition beta (GaussianProposal.goeMatrix sigma z)) := by
    unfold gibbsPartition
    apply ContDiff.sum
    intro x hx
    exact (contDiff_const.mul (hH x)).exp
  have hq : ContDiff ℝ m (fun z : EuclideanSpace ℝ (Fin n × Fin n) => ‖z‖ ^ 2 / 2) := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    fun_prop
  exact (hq.sub (contDiff_const.mul (hH x))).add
    (hZ.log (fun z => (gibbsPartition_pos beta _).ne'))

def conditionalGibbsSpinMass {n : ℕ} (beta sigma : ℝ) (x : Spin n) : ℝ :=
  ∫ z, gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x
    ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)

def conditionalGibbsGaussianLaw {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    Measure (EuclideanSpace ℝ (Fin n × Fin n)) :=
  (GaussianProposal.primitiveGaussian (Fin n × Fin n)).withDensity
    (fun z => ENNReal.ofReal
      (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x /
        conditionalGibbsSpinMass beta sigma x))

theorem conditionalGibbsSpinMass_pos {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    0 < conditionalGibbsSpinMass beta sigma x := by
  unfold conditionalGibbsSpinMass
  rw [integral_pos_iff_support_of_nonneg
    (fun z => (gibbsProbability_pos beta _ x).le)
    (goeGibbsProbability_integrable beta sigma x)]
  have hs : Function.support
      (fun z => gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x) = univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (gibbsProbability_pos beta _ x).ne'
  rw [hs, measure_univ]
  norm_num

instance conditionalGibbsGaussianLaw_isProbability {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    IsProbabilityMeasure (conditionalGibbsGaussianLaw beta sigma x) := by
  constructor
  rw [conditionalGibbsGaussianLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div, ← conditionalGibbsSpinMass,
      div_self (conditionalGibbsSpinMass_pos beta sigma x).ne']
    simp
  · exact (goeGibbsProbability_integrable beta sigma x).div_const _
  · exact ae_of_all _ (fun z => div_nonneg
      (gibbsProbability_pos beta _ x).le (conditionalGibbsSpinMass_pos beta sigma x).le)

def primitiveJointGibbsLaw (n : ℕ) (beta sigma : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n × Fin n) × Spin n) :=
  GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ
    (gibbsKernel n beta).comap (GaussianProposal.goeMatrix sigma)
      (continuous_goeMatrix sigma).measurable

theorem conditionalGibbsGaussianLaw_weighted {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    ENNReal.ofReal (conditionalGibbsSpinMass beta sigma x) •
      conditionalGibbsGaussianLaw beta sigma x =
    (GaussianProposal.primitiveGaussian (Fin n × Fin n)).withDensity
      (fun z => ENNReal.ofReal (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x)) := by
  have hw : Measurable (fun z => ENNReal.ofReal
      (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x /
        conditionalGibbsSpinMass beta sigma x)) :=
    (((continuous_gibbsProbability beta x).comp (continuous_goeMatrix sigma)).div_const _).measurable.ennreal_ofReal
  rw [conditionalGibbsGaussianLaw, ← withDensity_smul _ hw]
  apply withDensity_congr_ae
  exact ae_of_all _ (fun z => by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (conditionalGibbsSpinMass_pos beta sigma x).le]
    congr 1
    field_simp [(conditionalGibbsSpinMass_pos beta sigma x).ne'])

theorem primitiveJointGibbsLaw_spin_fiber {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (A : Set (EuclideanSpace ℝ (Fin n × Fin n))) (hA : MeasurableSet A) :
    primitiveJointGibbsLaw n beta sigma (A ×ˢ {x}) =
      ENNReal.ofReal (conditionalGibbsSpinMass beta sigma x) *
        conditionalGibbsGaussianLaw beta sigma x A := by
  rw [primitiveJointGibbsLaw, Measure.compProd_apply_prod hA (measurableSet_singleton x)]
  simp only [Kernel.comap_apply]
  have hk (z : EuclideanSpace ℝ (Fin n × Fin n)) :
      gibbsKernel n beta (GaussianProposal.goeMatrix sigma z) {x} =
        ENNReal.ofReal (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x) := by
    change finiteWeightMeasure _ {x} = _
    rw [finiteWeightMeasure_apply _ _ (measurableSet_singleton x)]
    simp
  simp_rw [hk]
  rw [← withDensity_apply _ hA, ← conditionalGibbsGaussianLaw_weighted,
    Measure.smul_apply, smul_eq_mul]

theorem conditionalGibbsGaussianLaw_eq_exp_potential {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) :
    conditionalGibbsGaussianLaw beta sigma x =
      volume.withDensity (fun z => ENNReal.ofReal
        (((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card (Fin n × Fin n) /
          conditionalGibbsSpinMass beta sigma x) *
          Real.exp (-conditionalGibbsPotential beta sigma x z))) := by
  have hd : Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
      ENNReal.ofReal (standardGaussianEuclideanDensity z)) := by
    unfold standardGaussianEuclideanDensity
    exact (Finset.measurable_prod _ (fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (by fun_prop))).ennreal_ofReal
  have hw : Measurable (fun z => ENNReal.ofReal
      (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x /
        conditionalGibbsSpinMass beta sigma x)) :=
    (((continuous_gibbsProbability beta x).comp (continuous_goeMatrix sigma)).div_const _).measurable.ennreal_ofReal
  rw [conditionalGibbsGaussianLaw, GaussianProposal.primitiveGaussian,
    stdGaussian_euclidean_eq_withDensity, ← withDensity_mul volume hd hw]
  apply withDensity_congr_ae
  exact ae_of_all _ (fun z => by
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (by
      unfold standardGaussianEuclideanDensity
      exact Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _))]
    congr 1
    have he : Real.exp (-conditionalGibbsPotential beta sigma x z) =
        Real.exp (-‖z‖ ^ 2 / 2) * Real.exp (beta * goeSpinHamiltonian sigma x z) /
          gibbsPartition beta (GaussianProposal.goeMatrix sigma z) := by
      unfold conditionalGibbsPotential
      rw [show -(‖z‖ ^ 2 / 2 - beta * goeSpinHamiltonian sigma x z +
        Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z))) =
        -‖z‖ ^ 2 / 2 + beta * goeSpinHamiltonian sigma x z -
        Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z)) by ring,
        Real.exp_sub, Real.exp_add, Real.exp_log (gibbsPartition_pos beta _)]
    rw [standardGaussianEuclideanDensity_eq_norm, he]
    unfold gibbsProbability goeSpinHamiltonian
    ring)

theorem conditionalGibbsSpinMass_sk {n : ℕ} (beta : ℝ) (x : Spin n) :
    conditionalGibbsSpinMass beta (1 / Real.sqrt (2 * (n : ℝ))) x = 1 / (2 : ℝ) ^ n := by
  exact integral_goeGibbsWeight_sk_uniform beta x

theorem conditionalGibbsGaussianLaw_sk {n : ℕ} (beta : ℝ) (x : Spin n) :
    conditionalGibbsGaussianLaw beta (1 / Real.sqrt (2 * (n : ℝ))) x =
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)).withDensity
        (fun z => ENNReal.ofReal ((2 : ℝ) ^ n *
          gibbsProbability beta (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z) x)) := by
  unfold conditionalGibbsGaussianLaw
  rw [conditionalGibbsSpinMass_sk]
  congr 1
  funext z
  congr 1
  field_simp

end SKConstants

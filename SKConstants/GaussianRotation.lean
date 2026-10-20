module
public import SKConstants.GaussianMaximum
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace SKConstants
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
theorem stdGaussian_rotation_marginal (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ((stdGaussian E).prod (stdGaussian E)).map
      (fun p : E × E ↦ a • p.1 + b • p.2) = stdGaussian E := by
  have hm : ((stdGaussian E).prod (stdGaussian E)).map
      (fun p : E × E ↦ a • p.1 + b • p.2) =
      ((stdGaussian E).map (a • ·)) ∗ ((stdGaussian E).map (b • ·)) := by
    rw [Measure.conv, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hm]
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_conv, charFun_map_smul, charFun_map_smul, charFun_stdGaussian,
    charFun_stdGaussian, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs]
  have ha : ((|a| : ℝ) : ℂ)^2 = (a : ℂ)^2 := by exact_mod_cast sq_abs a
  have hb : ((|b| : ℝ) : ℂ)^2 = (b : ℂ)^2 := by exact_mod_cast sq_abs b
  simp only [Complex.ofReal_mul, mul_pow, ha, hb]
  have hc := congrArg Complex.ofReal h
  push_cast at hc
  linear_combination -(‖t‖ : ℂ)^2 / 2 * hc

@[expose] def gaussianRotation (a b : ℝ) (p : E × E) : E := a • p.1 + b • p.2

theorem gaussianRotation_hasLaw (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    HasLaw (gaussianRotation (E := E) a b) (stdGaussian E)
      ((stdGaussian E).prod (stdGaussian E)) :=
  ⟨(by unfold gaussianRotation; fun_prop), stdGaussian_rotation_marginal a b h⟩

theorem goeGaussianRotation_hasLaw {n : ℕ} (sigma a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) :
    HasLaw (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
        EuclideanSpace ℝ (Fin n × Fin n) ↦
      GaussianProposal.goeMatrix sigma (gaussianRotation a b p))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix sigma))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) := by
  have hl : HasLaw (GaussianProposal.goeMatrix (ι := Fin n) sigma)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix sigma))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) :=
    ⟨(continuous_goeMatrix sigma).measurable.aemeasurable, rfl⟩
  exact hl.fun_comp (gaussianRotation_hasLaw a b h)

theorem gibbsPressure_abs_le_maximum {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    |Real.log (gibbsPartition beta W)| ≤
      |Real.log (gibbsPartition beta (0 : Matrix (Fin n) (Fin n) ℝ))| +
        |beta| * spinHamiltonianMaximum W := by
  have he : ∀ x : Spin n,
      |quadraticHamiltonian W x - quadraticHamiltonian (0 : Matrix (Fin n) (Fin n) ℝ) x| ≤
        spinHamiltonianMaximum W := by
    intro x
    simpa [quadraticHamiltonian, spinHamiltonianMaximum] using
      abs_le_finiteMaxAbs (fun x W ↦ quadraticHamiltonian W x) x W
  have h := gibbsPressure_comparison beta (spinHamiltonianMaximum W) W 0 he
  calc
    _ ≤ |Real.log (gibbsPartition beta W) - Real.log (gibbsPartition beta (0 : Matrix (Fin n) (Fin n) ℝ))| +
        |Real.log (gibbsPartition beta (0 : Matrix (Fin n) (Fin n) ℝ))| := by
      simpa only [sub_add_cancel] using abs_add_le
        (Real.log (gibbsPartition beta W) - Real.log (gibbsPartition beta (0 : Matrix (Fin n) (Fin n) ℝ)))
        (Real.log (gibbsPartition beta (0 : Matrix (Fin n) (Fin n) ℝ)))
    _ ≤ _ := by
      simpa only [add_comm] using add_le_add_right h
        |Real.log (gibbsPartition beta (0 : Matrix (Fin n) (Fin n) ℝ))|

theorem integrable_goeGibbsPressure {n : ℕ} (sigma beta : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n × Fin n) ↦
      Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z)))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin n) ↦
      Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z))) :=
    Real.measurable_log.comp ((continuous_gibbsPartition beta).measurable.comp
      (continuous_goeMatrix sigma).measurable)
  apply ((integrable_const |Real.log (gibbsPartition beta (0 : Matrix (Fin n) (Fin n) ℝ))|).add
    ((integrable_goeHamiltonianMaximum sigma).const_mul |beta|)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z ↦ by
    simpa only [Real.norm_eq_abs, spinHamiltonianMaximum_goe, Pi.add_apply, Pi.mul_apply] using
      gibbsPressure_abs_le_maximum beta (GaussianProposal.goeMatrix sigma z))

theorem integrable_goeGibbsPressure_rotated {n : ℕ} (sigma beta a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
        EuclideanSpace ℝ (Fin n × Fin n) ↦
      Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma
        (gaussianRotation a b p))))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) := by
  exact (gaussianRotation_hasLaw a b h).integrable_fun_comp
    (integrable_goeGibbsPressure sigma beta)

theorem goeGibbsPressure_rotation_integral {n : ℕ} (sigma beta a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) :
    (∫ p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n),
      Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma
        (gaussianRotation a b p)))
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) =
    ∫ z, Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z))
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
  exact (gaussianRotation_hasLaw a b h).integral_comp
    (integrable_goeGibbsPressure sigma beta).aestronglyMeasurable

end SKConstants

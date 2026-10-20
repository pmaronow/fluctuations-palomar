module

public import SKConstants.GaussianRotation
public import SKConstants.GaussianGibbsInterpolation
public import SKConstants.GaussianPairExchangeability

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
namespace SKConstants

theorem finiteGibbs_KL_energy_pressure {n : ℕ} (beta : ℝ)
    (W V : Matrix (Fin n) (Fin n) ℝ) :
    finiteKL (gibbsProbability beta W) (gibbsProbability beta V) =
      beta * ((∑ x, gibbsProbability beta W x * quadraticHamiltonian W x) -
        (∑ x, gibbsProbability beta W x * quadraticHamiltonian V x)) +
        Real.log (gibbsPartition beta V) - Real.log (gibbsPartition beta W) := by
  have hp : ∀ x, gibbsProbability beta W x *
      Real.log (gibbsProbability beta W x / gibbsProbability beta V x) =
      beta * (gibbsProbability beta W x * quadraticHamiltonian W x -
        gibbsProbability beta W x * quadraticHamiltonian V x) +
      gibbsProbability beta W x * Real.log (gibbsPartition beta V) -
      gibbsProbability beta W x * Real.log (gibbsPartition beta W) := by
    intro x
    rw [Real.log_div (gibbsProbability_pos beta W x).ne'
      (gibbsProbability_pos beta V x).ne', log_gibbsProbability, log_gibbsProbability]
    ring
  unfold finiteKL
  simp only [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, gibbsProbability_sum, one_mul]

theorem integrable_gibbs_KL_of_integrable_maximum {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (beta : ℝ) (W V : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hW : Measurable W) (hV : Measurable V)
    (hWi : Integrable (fun ω ↦ spinHamiltonianMaximum (W ω)) μ)
    (hVi : Integrable (fun ω ↦ spinHamiltonianMaximum (V ω)) μ) :
    Integrable (fun ω ↦ finiteKL (gibbsProbability beta (W ω))
      (gibbsProbability beta (V ω))) μ := by
  have hm := (measurable_gibbs_KL beta).comp (hW.prodMk hV)
  apply ((hWi.add hVi).const_mul (2 * |beta|)).mono' hm.aestronglyMeasurable
  filter_upwards with ω
  change |finiteKL (gibbsProbability beta (W ω)) (gibbsProbability beta (V ω))| ≤
    2 * |beta| * (spinHamiltonianMaximum (W ω) + spinHamiltonianMaximum (V ω))
  rw [abs_of_nonneg (finiteKL_nonneg _ _
    (gibbsProbability_pos beta (W ω)) (gibbsProbability_pos beta (V ω))
    (gibbsProbability_sum beta (W ω)) (gibbsProbability_sum beta (V ω)))]
  apply gibbs_KL_comparison
  intro x
  exact (abs_sub _ _).trans (add_le_add
    (abs_le_finiteMaxAbs (fun x W ↦ quadraticHamiltonian W x) x (W ω))
    (abs_le_finiteMaxAbs (fun x W ↦ quadraticHamiltonian W x) x (V ω)))

theorem integrable_goeGibbsKL_rotation {n : ℕ} (sigma beta a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
        EuclideanSpace ℝ (Fin n × Fin n) ↦
      finiteKL (gibbsProbability beta (GaussianProposal.goeMatrix sigma p.1))
        (gibbsProbability beta (GaussianProposal.goeMatrix sigma
          (gaussianRotation a b p))))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) := by
  let μ := GaussianProposal.primitiveGaussian (Fin n × Fin n)
  have hWm : Measurable (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
      EuclideanSpace ℝ (Fin n × Fin n) ↦ GaussianProposal.goeMatrix sigma p.1) :=
    (continuous_goeMatrix (V := Fin n) sigma).measurable.comp measurable_fst
  have hVm : Measurable (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
      EuclideanSpace ℝ (Fin n × Fin n) ↦
      GaussianProposal.goeMatrix sigma (gaussianRotation a b p)) :=
    (continuous_goeMatrix (V := Fin n) sigma).measurable.comp
      (by unfold gaussianRotation; fun_prop)
  have hWi : Integrable (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
      EuclideanSpace ℝ (Fin n × Fin n) ↦
      spinHamiltonianMaximum (GaussianProposal.goeMatrix sigma p.1)) (μ.prod μ) := by
    simpa only [Function.comp_def, spinHamiltonianMaximum_goe] using
      (integrable_goeHamiltonianMaximum (n := n) sigma).comp_fst μ
  have hVi : Integrable (fun p : EuclideanSpace ℝ (Fin n × Fin n) ×
      EuclideanSpace ℝ (Fin n × Fin n) ↦
      spinHamiltonianMaximum (GaussianProposal.goeMatrix sigma (gaussianRotation a b p)))
      (μ.prod μ) := by
    have hi := (gaussianRotation_hasLaw (E := EuclideanSpace ℝ (Fin n × Fin n))
      a b h).integrable_fun_comp (integrable_goeHamiltonianMaximum (n := n) sigma)
    simpa only [Function.comp_def, spinHamiltonianMaximum_goe,
      GaussianProposal.primitiveGaussian, μ] using hi
  exact integrable_gibbs_KL_of_integrable_maximum (μ.prod μ) beta _ _ hWm hVm hWi hVi

@[expose] def goeGibbsRotationKL {n : ℕ} (sigma beta a b : ℝ)
    (p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  finiteKL (gibbsProbability beta (GaussianProposal.goeMatrix sigma p.1))
    (gibbsProbability beta (GaussianProposal.goeMatrix sigma (gaussianRotation a b p)))

theorem goeGibbsRotationKL_integral {n : ℕ} (sigma beta a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) :
    (∫ p, goeGibbsRotationKL (n := n) sigma beta a b p
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) =
      (1 - a) * (beta * ∫ z, goeGibbsEnergy (n := n) beta sigma z
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  let μ := GaussianProposal.primitiveGaussian (Fin n × Fin n)
  have hE := (goeGibbsEnergy_integrable (n := n) beta sigma).comp_fst μ
  have hM := goeMixedGibbsEnergy_integrable (n := n) beta sigma a b
  have hP := integrable_goeGibbsPressure_rotated (n := n) sigma beta a b h
  have hQ := (integrable_goeGibbsPressure (n := n) sigma beta).comp_fst μ
  have heq : goeGibbsRotationKL (n := n) sigma beta a b = fun p ↦
      beta * (goeGibbsEnergy beta sigma p.1 - goeMixedGibbsEnergy beta sigma a b p) +
      Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma (gaussianRotation a b p))) -
      Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma p.1)) := by
    funext p
    exact finiteGibbs_KL_energy_pressure beta
      (GaussianProposal.goeMatrix sigma p.1)
      (GaussianProposal.goeMatrix sigma (gaussianRotation a b p))
  have hsplit := integral_sub (((hE.sub hM).const_mul beta).add hP) hQ
  have hadd := integral_add ((hE.sub hM).const_mul beta) hP
  have hdiff := integral_sub hE hM
  simp only [Pi.add_apply, Pi.sub_apply, μ] at hsplit hadd hdiff
  have hEi := integral_fun_fst (μ := μ) (ν := μ) (goeGibbsEnergy (n := n) beta sigma)
  have hQi := integral_fun_fst (μ := μ) (ν := μ)
    (fun z : EuclideanSpace ℝ (Fin n × Fin n) ↦
      Real.log (gibbsPartition beta (GaussianProposal.goeMatrix sigma z)))
  simp only [μ, probReal_univ, one_smul] at hEi hQi
  rw [heq]
  simp only
  rw [hsplit, hadd, integral_const_mul,
    hdiff, goeMixedGibbsEnergy_integral,
    goeGibbsPressure_rotation_integral sigma beta a b h, hEi, hQi]
  ring

theorem goeGibbsRotationKL_integral_le {n : ℕ} (sigma beta a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) (ha : a ≤ 1) :
    (∫ p, goeGibbsRotationKL (n := n) sigma beta a b p
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) ≤
      (1 - a) * (beta ^ 2 * sigma ^ 2 * ((n : ℝ) ^ 2 - n)) := by
  rw [goeGibbsRotationKL_integral sigma beta a b h]
  exact mul_le_mul_of_nonneg_left
    (goe_gibbs_expected_energy_diagonal_bound (n := n) beta sigma) (sub_nonneg.mpr ha)

@[expose] def skGibbsRotationKL (n : ℕ) (beta delta : ℝ) :=
  goeGibbsRotationKL (n := n) (1 / Real.sqrt (2 * (n : ℝ))) beta
    (Real.sqrt (1 - delta)) (Real.sqrt delta)

theorem skGibbsRotationKL_integral_le_exact {n : ℕ} (hn : 0 < n) (beta delta : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) :
    (∫ p, skGibbsRotationKL n beta delta p
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) ≤
      (1 - Real.sqrt (1 - delta)) * (beta ^ 2 * ((n : ℝ) - 1) / 2) := by
  have hrot : (Real.sqrt (1 - delta)) ^ 2 + (Real.sqrt delta) ^ 2 = 1 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hd1), Real.sq_sqrt hd0]
    ring
  have ha : Real.sqrt (1 - delta) ≤ 1 := (Real.sqrt_le_one).mpr (by linarith)
  unfold skGibbsRotationKL
  rw [goeGibbsRotationKL_integral _ _ _ _ hrot]
  exact mul_le_mul_of_nonneg_left (sk_gibbs_expected_energy_diagonal_bound hn beta)
    (sub_nonneg.mpr ha)

theorem skGibbsRotationKL_integral_le_delta {n : ℕ} (hn : 0 < n) (beta delta : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) :
    (∫ p, skGibbsRotationKL n beta delta p
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) ≤
      delta * (beta ^ 2 * ((n : ℝ) - 1) / 2) := by
  have hs : 1 - delta ≤ Real.sqrt (1 - delta) :=
    Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd1)])
  have hc : 0 ≤ beta ^ 2 * ((n : ℝ) - 1) / 2 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  exact (skGibbsRotationKL_integral_le_exact hn beta delta hd0 hd1).trans
    (mul_le_mul_of_nonneg_right (by linarith) hc)

theorem goeGibbsRotationKL_reverse_integral {n : ℕ} (sigma beta a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) :
    (∫ p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n),
      finiteKL (gibbsProbability beta (GaussianProposal.goeMatrix sigma (gaussianRotation a b p)))
        (gibbsProbability beta (GaussianProposal.goeMatrix sigma p.1))
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) =
      (1 - a) * (beta * ∫ z, goeGibbsEnergy (n := n) beta sigma z
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  rw [← goe_rotated_pair_integral_swap sigma a b h _ (measurable_gibbs_KL beta)]
  exact goeGibbsRotationKL_integral sigma beta a b h

theorem integrable_goeGibbsKL_rotation_reverse {n : ℕ} (sigma beta a b : ℝ)
    (h : a ^ 2 + b ^ 2 = 1) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n) ↦
      finiteKL (gibbsProbability beta (GaussianProposal.goeMatrix sigma (gaussianRotation a b p)))
        (gibbsProbability beta (GaussianProposal.goeMatrix sigma p.1)))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) :=
  (goe_rotated_pair_integrable_swap_iff sigma a b h _ (measurable_gibbs_KL beta)).mp
    (integrable_goeGibbsKL_rotation sigma beta a b h)

theorem skGibbsRotationKL_reverse_integral_le_delta {n : ℕ} (hn : 0 < n) (beta delta : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) :
    (∫ p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n),
      finiteKL (gibbsProbability beta (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ)))
        (gaussianRotation (Real.sqrt (1 - delta)) (Real.sqrt delta) p)))
        (gibbsProbability beta (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) p.1))
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) ≤
      delta * (beta ^ 2 * ((n : ℝ) - 1) / 2) := by
  have hrot : (Real.sqrt (1 - delta)) ^ 2 + (Real.sqrt delta) ^ 2 = 1 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hd1), Real.sq_sqrt hd0]
    ring
  rw [← goe_rotated_pair_integral_swap (1 / Real.sqrt (2 * (n : ℝ)))
    (Real.sqrt (1 - delta)) (Real.sqrt delta) hrot _ (measurable_gibbs_KL beta)]
  exact skGibbsRotationKL_integral_le_delta hn beta delta hd0 hd1

end SKConstants

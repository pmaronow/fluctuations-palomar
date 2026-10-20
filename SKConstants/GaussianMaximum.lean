module

public import SKConstants.GaussianHamiltonian

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical

namespace SKConstants

@[expose] def finiteMaxAbs {I Ω : Type*} [Fintype I] [Nonempty I]
    (X : I → Ω → ℝ) : Ω → ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ω ↦ |X i ω|)

theorem finiteMaxAbs_nonneg {I Ω : Type*} [Fintype I] [Nonempty I]
    (X : I → Ω → ℝ) (ω : Ω) : 0 ≤ finiteMaxAbs X ω := by
  let i : I := Classical.arbitrary I
  simpa only [finiteMaxAbs, Finset.sup'_apply] using
    (abs_nonneg (X i ω)).trans (Finset.le_sup' (fun j ↦ |X j ω|) (Finset.mem_univ i))

theorem abs_le_finiteMaxAbs {I Ω : Type*} [Fintype I] [Nonempty I]
    (X : I → Ω → ℝ) (i : I) (ω : Ω) : |X i ω| ≤ finiteMaxAbs X ω := by
  simpa only [finiteMaxAbs, Finset.sup'_apply] using
    Finset.le_sup' (fun j ↦ |X j ω|) (Finset.mem_univ i)

theorem integrable_finiteMaxAbs {I Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] (μ : Measure Ω) (X : I → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) μ) : Integrable (finiteMaxAbs X) μ := by
  unfold finiteMaxAbs
  exact Finset.sup'_induction (p := fun f : Ω → ℝ ↦ Integrable f μ)
    _ _ (fun _ hf _ hg ↦ hf.sup hg) (fun i _ ↦ (hX i).abs)

@[expose] def twoSidedExponentialSum {I Ω : Type*} [Fintype I]
    (X : I → Ω → ℝ) (theta : ℝ) (ω : Ω) : ℝ :=
  ∑ i, (Real.exp (theta * X i ω) + Real.exp (-theta * X i ω))

theorem twoSidedExponentialSum_pos {I Ω : Type*} [Fintype I] [Nonempty I]
    (X : I → Ω → ℝ) (theta : ℝ) (ω : Ω) :
    0 < twoSidedExponentialSum X theta ω := by
  exact Finset.sum_pos (fun i _ ↦ add_pos (Real.exp_pos _) (Real.exp_pos _))
    Finset.univ_nonempty

theorem theta_finiteMaxAbs_le_log_sum {I Ω : Type*} [Fintype I] [Nonempty I]
    (X : I → Ω → ℝ) (theta : ℝ) (ω : Ω) :
    theta * finiteMaxAbs X ω ≤ Real.log (twoSidedExponentialSum X theta ω) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i ↦ |X i ω|)
  have hm : finiteMaxAbs X ω = |X i ω| := by
    simpa only [finiteMaxAbs, Finset.sup'_apply] using hi
  rw [hm]
  have he : Real.exp (theta * |X i ω|) ≤
      Real.exp (theta * X i ω) + Real.exp (-theta * X i ω) := by
    by_cases hx : 0 ≤ X i ω
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_neg (lt_of_not_ge hx)]
      have hh : theta * -X i ω = -theta * X i ω := by ring
      rw [hh]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hs : Real.exp (theta * X i ω) + Real.exp (-theta * X i ω) ≤
      twoSidedExponentialSum X theta ω :=
    by
      unfold twoSidedExponentialSum
      exact Finset.single_le_sum (f := fun j ↦ Real.exp (theta * X j ω) +
        Real.exp (-theta * X j ω)) (fun j _ ↦ by positivity) (Finset.mem_univ i)
  have hlog := Real.log_le_log (Real.exp_pos _) (he.trans hs)
  simpa only [Real.log_exp] using hlog

theorem centered_gaussian_exponential_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : HasGaussianLaw X μ) (hmean : ∫ ω, X ω ∂μ = 0) (t : ℝ) :
    (Integrable (fun ω ↦ Real.exp (t * X ω)) μ) ∧
      (∫ ω, Real.exp (t * X ω) ∂μ) = Real.exp (Var[X; μ] * t ^ 2 / 2) := by
  have hlaw : HasLaw X (gaussianReal 0 (Var[X; μ]).toNNReal) μ := by
    refine ⟨hX.aemeasurable, ?_⟩
    simpa only [hmean] using hX.map_eq_gaussianReal
  constructor
  · simpa only [Function.comp_def] using
      hlaw.integrable_comp (integrable_exp_mul_gaussianReal t)
  · change mgf X μ t = _
    rw [mgf_gaussianReal hlaw, Real.toNNReal_of_nonneg (variance_nonneg X μ)]
    simp

theorem finite_gaussian_expected_max_bound {I Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i, HasGaussianLaw (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (V theta : ℝ) (hvariance : ∀ i, Var[X i; μ] ≤ V) (htheta : 0 < theta) :
    ∫ ω, finiteMaxAbs X ω ∂μ ≤
      Real.log (2 * (Fintype.card I : ℝ)) / theta + V * theta / 2 := by
  let S := twoSidedExponentialSum X theta
  let A := 2 * (Fintype.card I : ℝ) * Real.exp (V * theta ^ 2 / 2)
  have hc : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hA : 0 < A := by dsimp [A]; positivity
  have hS : Integrable S μ := by
    apply integrable_finsetSum
    intro i _
    exact ((centered_gaussian_exponential_integral μ (X i) (hX i) (hmean i) theta).1).add
      (centered_gaussian_exponential_integral μ (X i) (hX i) (hmean i) (-theta)).1
  have hES : (∫ ω, S ω ∂μ) ≤ A := by
    dsimp [S, twoSidedExponentialSum]
    rw [integral_finsetSum]
    · calc
        _ ≤ ∑ _i : I, 2 * Real.exp (V * theta ^ 2 / 2) := by
          apply Finset.sum_le_sum
          intro i _
          rw [integral_add
            (centered_gaussian_exponential_integral μ (X i) (hX i) (hmean i) theta).1
            (centered_gaussian_exponential_integral μ (X i) (hX i) (hmean i) (-theta)).1,
            (centered_gaussian_exponential_integral μ (X i) (hX i) (hmean i) theta).2,
            (centered_gaussian_exponential_integral μ (X i) (hX i) (hmean i) (-theta)).2,
            neg_sq]
          have he := Real.exp_le_exp.mpr
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hvariance i) (sq_nonneg theta)) (by norm_num : (0 : ℝ) ≤ 2))
          linarith
        _ = A := by simp [A]; ring
    · intro i _
      exact ((centered_gaussian_exponential_integral μ (X i) (hX i) (hmean i) theta).1).add
        (centered_gaussian_exponential_integral μ (X i) (hX i) (hmean i) (-theta)).1
  have hpoint : ∀ ω, theta * finiteMaxAbs X ω ≤ Real.log A + S ω / A - 1 := by
    intro ω
    have hp : 0 < S ω := twoSidedExponentialSum_pos X theta ω
    have hl := Real.log_le_sub_one_of_pos (div_pos hp hA)
    rw [Real.log_div hp.ne' hA.ne'] at hl
    have hm := theta_finiteMaxAbs_le_log_sum X theta ω
    dsimp [S] at hl ⊢
    linarith
  have hM := integrable_finiteMaxAbs μ X (fun i ↦ (hX i).integrable)
  have hint := integral_mono (hM.const_mul theta)
    (((integrable_const (Real.log A)).add (hS.div_const A)).sub (integrable_const 1)) hpoint
  change (∫ ω, theta * finiteMaxAbs X ω ∂μ) ≤
    ∫ ω, Real.log A + S ω / A - 1 ∂μ at hint
  rw [integral_const_mul, integral_sub, integral_add] at hint
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
      integral_div] at hint
    have hquot : (∫ ω, S ω ∂μ) / A ≤ 1 := (div_le_one hA).mpr hES
    have hlogA : Real.log A = Real.log (2 * (Fintype.card I : ℝ)) + V * theta ^ 2 / 2 := by
      dsimp [A]
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
    rw [hlogA] at hint
    apply (mul_le_mul_iff_right₀ htheta).mp
    have hid : (Real.log (2 * (Fintype.card I : ℝ)) / theta + V * theta / 2) * theta =
        Real.log (2 * (Fintype.card I : ℝ)) + V * theta ^ 2 / 2 := by
      field_simp
    nlinarith [hid]
  · exact integrable_const _
  · exact hS.div_const A
  · exact (integrable_const _).add (hS.div_const A)
  · exact integrable_const _

@[expose] def goeHamiltonianMaximum {n : ℕ} (sigma : ℝ) :
    EuclideanSpace ℝ (Fin n × Fin n) → ℝ :=
  finiteMaxAbs (goeSpinHamiltonian sigma)

@[expose] def gaussianMaximumConstant : ℝ := 2 * Real.log 2 + 1 / 2

theorem integrable_goeHamiltonianMaximum {n : ℕ} (sigma : ℝ) :
    Integrable (goeHamiltonianMaximum (n := n) sigma)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) :=
  integrable_finiteMaxAbs _ _ (fun x ↦ (goeSpinHamiltonian_gaussian sigma x).integrable)

theorem goeHamiltonianMaximum_zero {n : ℕ}
    (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    goeHamiltonianMaximum 0 z = 0 := by
  unfold goeHamiltonianMaximum finiteMaxAbs
  simp only [Finset.sup'_apply]
  apply Finset.sup'_eq_of_forall
  intro x _
  simp [goeSpinHamiltonian, GaussianProposal.goeMatrix, quadraticHamiltonian]

theorem log_twice_spin_card (n : ℕ) :
    Real.log (2 * (Fintype.card (Spin n) : ℝ)) = ((n : ℝ) + 1) * Real.log 2 := by
  have hc : (Fintype.card (Spin n) : ℝ) = (2 : ℝ) ^ n := by simp [Spin]
  rw [hc, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  ring

theorem goeHamiltonianMaximum_expected_bound {n : ℕ} (hn : 0 < n) (sigma : ℝ) :
    ∫ z, goeHamiltonianMaximum sigma z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) ≤
      gaussianMaximumConstant * |sigma| * (n : ℝ) * Real.sqrt n := by
  by_cases hs : sigma = 0
  · subst sigma
    simp only [goeHamiltonianMaximum_zero, integral_zero, abs_zero, mul_zero, zero_mul,
      le_refl]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < |sigma| := abs_pos.mpr hs
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have h := finite_gaussian_expected_max_bound
    (GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (goeSpinHamiltonian sigma) (goeSpinHamiltonian_gaussian sigma)
    (goeSpinHamiltonian_mean sigma) (sigma ^ 2 * (n : ℝ) ^ 2)
    (1 / (|sigma| * Real.sqrt n))
    (fun x ↦ (goeSpinHamiltonian_variance sigma x).le) (by positivity)
  rw [log_twice_spin_card] at h
  have hv : sigma ^ 2 * (n : ℝ) ^ 2 * (1 / (|sigma| * Real.sqrt n)) / 2 =
      |sigma| * Real.sqrt n * (n : ℝ) / 2 := by
    rw [← sq_abs sigma]
    field_simp
    have hr2 := Real.sq_sqrt hnR.le
    nlinarith
  rw [hv] at h
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnum : ((n : ℝ) + 1) * Real.log 2 + (n : ℝ) / 2 ≤
      gaussianMaximumConstant * (n : ℝ) := by
    unfold gaussianMaximumConstant
    nlinarith
  calc
    _ ≤ ((n : ℝ) + 1) * Real.log 2 / (1 / (|sigma| * Real.sqrt n)) +
        |sigma| * Real.sqrt n * (n : ℝ) / 2 := h
    _ = |sigma| * Real.sqrt n * (((n : ℝ) + 1) * Real.log 2 + (n : ℝ) / 2) := by
      simp only [one_div, div_inv_eq_mul]
      ring
    _ ≤ |sigma| * Real.sqrt n * (gaussianMaximumConstant * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by ring

theorem skPerturbationHamiltonianMaximum_expected_bound {n : ℕ} (hn : 0 < n)
    (delta : ℝ) (_hdelta : 0 ≤ delta) :
    ∫ z, goeHamiltonianMaximum (Real.sqrt delta / Real.sqrt (2 * (n : ℝ))) z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) ≤
      gaussianMaximumConstant * (n : ℝ) * Real.sqrt delta := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < Real.sqrt (2 * (n : ℝ)) := by positivity
  have hs : |Real.sqrt delta / Real.sqrt (2 * (n : ℝ))| * Real.sqrt n ≤
      Real.sqrt delta := by
    rw [abs_of_nonneg (by positivity), div_mul_eq_mul_div]
    apply (div_le_iff₀ hr).mpr
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith : (n : ℝ) ≤ 2 * (n : ℝ))) (Real.sqrt_nonneg delta)
  have hC : 0 ≤ gaussianMaximumConstant := by
    unfold gaussianMaximumConstant
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  calc
    _ ≤ gaussianMaximumConstant * |Real.sqrt delta / Real.sqrt (2 * (n : ℝ))| *
        (n : ℝ) * Real.sqrt n := goeHamiltonianMaximum_expected_bound hn _
    _ = (gaussianMaximumConstant * (n : ℝ)) *
        (|Real.sqrt delta / Real.sqrt (2 * (n : ℝ))| * Real.sqrt n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg hC hnR.le)

@[expose] def spinHamiltonianMaximum {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  finiteMaxAbs (fun x W ↦ quadraticHamiltonian W x) W

theorem quadraticHamiltonian_sub {n : ℕ}
    (W V : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    quadraticHamiltonian (W - V) x = quadraticHamiltonian W x - quadraticHamiltonian V x := by
  simp only [quadraticHamiltonian, Matrix.sub_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]

theorem gibbs_KL_le_spinHamiltonianMaximum {n : ℕ} (beta : ℝ)
    (W V : Matrix (Fin n) (Fin n) ℝ) :
    finiteKL (gibbsProbability beta W) (gibbsProbability beta V) ≤
      2 * |beta| * spinHamiltonianMaximum (W - V) := by
  apply gibbs_KL_comparison
  intro x
  rw [← quadraticHamiltonian_sub]
  simpa only [spinHamiltonianMaximum] using
    abs_le_finiteMaxAbs (fun x W ↦ quadraticHamiltonian W x) x (W - V)

theorem spinHamiltonianMaximum_goe {n : ℕ} (sigma : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    spinHamiltonianMaximum (GaussianProposal.goeMatrix sigma z) =
      goeHamiltonianMaximum sigma z := by
  unfold spinHamiltonianMaximum goeHamiltonianMaximum finiteMaxAbs
  simp only [Finset.sup'_apply]
  rfl

theorem continuous_spinHamiltonianMaximum {n : ℕ} :
    Continuous (spinHamiltonianMaximum (n := n)) := by
  unfold spinHamiltonianMaximum finiteMaxAbs
  exact Finset.sup'_induction (p := fun f : Matrix (Fin n) (Fin n) ℝ → ℝ ↦ Continuous f)
    _ _ (fun _ hf _ hg ↦ hf.sup hg)
    (fun x _ ↦ (continuous_quadraticHamiltonian x).abs)

theorem measurable_gibbs_KL {n : ℕ} (beta : ℝ) :
    Measurable (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ↦
      finiteKL (gibbsProbability beta p.1) (gibbsProbability beta p.2)) := by
  unfold finiteKL
  apply Finset.measurable_sum
  intro x _
  exact ((continuous_gibbsProbability beta x).measurable.comp measurable_fst).mul
    (Real.measurable_log.comp
      (((continuous_gibbsProbability beta x).measurable.comp measurable_fst).div
        ((continuous_gibbsProbability beta x).measurable.comp measurable_snd)))

theorem expected_gibbs_KL_le_goe_expected_max_of_difference {n : ℕ} (_hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (beta sigma : ℝ) (W V : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hW : Measurable W) (hV : Measurable V)
    (hdifference : HasLaw (fun ω ↦ W ω - V ω)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix (ι := Fin n) sigma)) μ) :
    (Integrable (fun ω ↦ finiteKL (gibbsProbability beta (W ω))
      (gibbsProbability beta (V ω))) μ) ∧
    (∫ ω, finiteKL (gibbsProbability beta (W ω)) (gibbsProbability beta (V ω)) ∂μ) ≤
      2 * |beta| * (∫ z, goeHamiltonianMaximum sigma z
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  let ν : Measure (Matrix (Fin n) (Fin n) ℝ) := (GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
    (GaussianProposal.goeMatrix (ι := Fin n) sigma)
  have hm : AEStronglyMeasurable (spinHamiltonianMaximum (n := n)) ν :=
    continuous_spinHamiltonianMaximum.measurable.aestronglyMeasurable
  have hi : Integrable (spinHamiltonianMaximum (n := n)) ν := by
    apply (integrable_map_measure hm (continuous_goeMatrix sigma).measurable.aemeasurable).mpr
    simpa only [Function.comp_def, spinHamiltonianMaximum_goe] using
      integrable_goeHamiltonianMaximum (n := n) sigma
  have hid : Integrable (fun ω ↦ spinHamiltonianMaximum (W ω - V ω)) μ :=
    hdifference.integrable_fun_comp hi
  have hmKL : Measurable (fun ω ↦ finiteKL (gibbsProbability beta (W ω))
      (gibbsProbability beta (V ω))) :=
    by
      unfold finiteKL
      apply Finset.measurable_sum
      intro x _
      exact ((continuous_gibbsProbability beta x).measurable.comp hW).mul
        (Real.measurable_log.comp
          (((continuous_gibbsProbability beta x).measurable.comp hW).div
            ((continuous_gibbsProbability beta x).measurable.comp hV)))
  have hb : ∀ ω, |finiteKL (gibbsProbability beta (W ω))
      (gibbsProbability beta (V ω))| ≤ 2 * |beta| * spinHamiltonianMaximum (W ω - V ω) := by
    intro ω
    rw [abs_of_nonneg (finiteKL_nonneg _ _ (gibbsProbability_pos beta (W ω))
      (gibbsProbability_pos beta (V ω)) (gibbsProbability_sum beta (W ω))
      (gibbsProbability_sum beta (V ω)))]
    exact gibbs_KL_le_spinHamiltonianMaximum beta (W ω) (V ω)
  have hKL : Integrable (fun ω ↦ finiteKL (gibbsProbability beta (W ω))
      (gibbsProbability beta (V ω))) μ :=
    (hid.const_mul (2 * |beta|)).mono' hmKL.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hb ω))
  refine ⟨hKL, ?_⟩
  calc
    _ ≤ ∫ ω, 2 * |beta| * spinHamiltonianMaximum (W ω - V ω) ∂μ :=
      integral_mono hKL (hid.const_mul _) (fun ω ↦ gibbs_KL_le_spinHamiltonianMaximum beta _ _)
    _ = 2 * |beta| * (∫ z, goeHamiltonianMaximum sigma z
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
      rw [integral_const_mul]
      apply congrArg (fun a : ℝ ↦ 2 * |beta| * a)
      calc
        _ = ∫ w, spinHamiltonianMaximum w ∂ν := by
          simpa only [Function.comp_def] using hdifference.integral_comp hm
        _ = ∫ z, goeHamiltonianMaximum sigma z
            ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
          have hmap := integral_map (f := spinHamiltonianMaximum (n := n))
            (continuous_goeMatrix (V := Fin n) sigma).measurable.aemeasurable hm
          simpa only [spinHamiltonianMaximum_goe] using hmap

theorem expected_gibbs_KL_bound_of_goe_difference {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (beta sigma : ℝ) (W V : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hW : Measurable W) (hV : Measurable V)
    (hdifference : HasLaw (fun ω ↦ W ω - V ω)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix (ι := Fin n) sigma)) μ) :
    (Integrable (fun ω ↦ finiteKL (gibbsProbability beta (W ω))
      (gibbsProbability beta (V ω))) μ) ∧
    (∫ ω, finiteKL (gibbsProbability beta (W ω)) (gibbsProbability beta (V ω)) ∂μ) ≤
      2 * |beta| * (gaussianMaximumConstant * |sigma| * (n : ℝ) * Real.sqrt n) := by
  have h := expected_gibbs_KL_le_goe_expected_max_of_difference hn μ beta sigma W V
    hW hV hdifference
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (goeHamiltonianMaximum_expected_bound hn sigma)
    (by positivity)

theorem expected_gibbs_KL_bound_of_sk_difference {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (beta delta : ℝ) (_hdelta : 0 ≤ delta) (W V : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hW : Measurable W) (hV : Measurable V)
    (hdifference : HasLaw (fun ω ↦ W ω - V ω)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix (Real.sqrt delta / Real.sqrt (2 * (n : ℝ))))) μ) :
    (Integrable (fun ω ↦ finiteKL (gibbsProbability beta (W ω))
      (gibbsProbability beta (V ω))) μ) ∧
    (∫ ω, finiteKL (gibbsProbability beta (W ω)) (gibbsProbability beta (V ω)) ∂μ) ≤
      2 * |beta| * gaussianMaximumConstant * (n : ℝ) * Real.sqrt delta := by
  have h := expected_gibbs_KL_bound_of_goe_difference hn μ beta
    (Real.sqrt delta / Real.sqrt (2 * (n : ℝ))) W V hW hV hdifference
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < Real.sqrt (2 * (n : ℝ)) := by positivity
  have hs : |Real.sqrt delta / Real.sqrt (2 * (n : ℝ))| * Real.sqrt n ≤
      Real.sqrt delta := by
    rw [abs_of_nonneg (by positivity), div_mul_eq_mul_div]
    apply (div_le_iff₀ hr).mpr
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith : (n : ℝ) ≤ 2 * (n : ℝ))) (Real.sqrt_nonneg delta)
  have hC : 0 ≤ gaussianMaximumConstant := by
    unfold gaussianMaximumConstant
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hscale : gaussianMaximumConstant *
      |Real.sqrt delta / Real.sqrt (2 * (n : ℝ))| * (n : ℝ) * Real.sqrt n ≤
      gaussianMaximumConstant * (n : ℝ) * Real.sqrt delta := by
    calc
      _ = (gaussianMaximumConstant * (n : ℝ)) *
          (|Real.sqrt delta / Real.sqrt (2 * (n : ℝ))| * Real.sqrt n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg hC hnR.le)
  refine ⟨h.1, h.2.trans ?_⟩
  convert mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2 * |beta|) using 1
  ring

theorem expected_gibbs_KL_under_goe_perturbation {n : ℕ} (hn : 0 < n)
    (beta sigma : ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    (Integrable (fun z ↦ finiteKL
      (gibbsProbability beta (V + GaussianProposal.goeMatrix sigma z))
      (gibbsProbability beta V)) (GaussianProposal.primitiveGaussian (Fin n × Fin n))) ∧
    (∫ z, finiteKL (gibbsProbability beta (V + GaussianProposal.goeMatrix sigma z))
      (gibbsProbability beta V) ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤
      2 * |beta| * (gaussianMaximumConstant * |sigma| * (n : ℝ) * Real.sqrt n) := by
  apply expected_gibbs_KL_bound_of_goe_difference hn
    (GaussianProposal.primitiveGaussian (Fin n × Fin n)) beta sigma
    (fun z ↦ V + GaussianProposal.goeMatrix sigma z) (fun _ ↦ V)
    (continuous_const.add (continuous_goeMatrix sigma)).measurable measurable_const
  have h : HasLaw (GaussianProposal.goeMatrix (ι := Fin n) sigma)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix sigma))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) :=
    ⟨(continuous_goeMatrix sigma).measurable.aemeasurable, rfl⟩
  simpa only [add_sub_cancel_left] using h

theorem finite_gaussian_expected_max_sqrt_bound {I Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i, HasGaussianLaw (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (V : ℝ) (hvariance : ∀ i, Var[X i; μ] ≤ V) :
    ∫ ω, finiteMaxAbs X ω ∂μ ≤
      Real.sqrt (2 * V * Real.log (2 * (Fintype.card I : ℝ))) := by
  let L := Real.log (2 * (Fintype.card I : ℝ))
  have hc : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hV : 0 ≤ V := (variance_nonneg (X (Classical.arbitrary I)) μ).trans
    (hvariance (Classical.arbitrary I))
  by_cases hVz : V = 0
  · subst V
    simp only [mul_zero, zero_mul, Real.sqrt_zero]
    by_contra hneg
    have hM : 0 < ∫ ω, finiteMaxAbs X ω ∂μ := lt_of_not_ge hneg
    have h := finite_gaussian_expected_max_bound μ X hX hmean 0
      (2 * L / (∫ ω, finiteMaxAbs X ω ∂μ)) hvariance (by positivity)
    have heq : L / (2 * L / (∫ ω, finiteMaxAbs X ω ∂μ)) =
        (∫ ω, finiteMaxAbs X ω ∂μ) / 2 := by
      field_simp
    change (∫ ω, finiteMaxAbs X ω ∂μ) ≤ L /
      (2 * L / (∫ ω, finiteMaxAbs X ω ∂μ)) + 0 * _ / 2 at h
    rw [heq] at h
    nlinarith
  · have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hVz)
    let a := Real.sqrt (2 * V * L)
    have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a ^ 2 = 2 * V * L := Real.sq_sqrt (by positivity)
    have h := finite_gaussian_expected_max_bound μ X hX hmean V (a / V)
      hvariance (by positivity)
    have heq : L / (a / V) + V * (a / V) / 2 = a := by
      field_simp
      nlinarith [ha2]
    change (∫ ω, finiteMaxAbs X ω ∂μ) ≤ L / (a / V) + V * (a / V) / 2 at h
    rw [heq] at h
    exact h

theorem skPerturbationHamiltonianMaximum_expected_sqrt_bound {n : ℕ} (hn : 0 < n)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    ∫ z, goeHamiltonianMaximum (Real.sqrt delta / Real.sqrt (2 * (n : ℝ))) z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) ≤
      Real.sqrt (2 * Real.log 2) * (n : ℝ) * Real.sqrt delta := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hv : ∀ x : Spin n, Var[goeSpinHamiltonian
      (Real.sqrt delta / Real.sqrt (2 * (n : ℝ))) x;
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] = delta * (n : ℝ) / 2 := by
    intro x
    rw [goeSpinHamiltonian_variance, div_pow, Real.sq_sqrt hdelta,
      Real.sq_sqrt (by positivity)]
    field_simp
  have h := finite_gaussian_expected_max_sqrt_bound
    (GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (goeSpinHamiltonian (Real.sqrt delta / Real.sqrt (2 * (n : ℝ))))
    (goeSpinHamiltonian_gaussian _) (goeSpinHamiltonian_mean _)
    (delta * (n : ℝ) / 2) (fun x ↦ (hv x).le)
  rw [log_twice_spin_card] at h
  apply h.trans
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hh : delta * (n : ℝ) * Real.log 2 * ((n : ℝ) + 1) ≤
      delta * (n : ℝ) * Real.log 2 * (2 * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc
    _ = delta * (n : ℝ) * Real.log 2 * ((n : ℝ) + 1) := by ring
    _ ≤ _ := hh
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log 2),
        Real.sq_sqrt hdelta]
      ring

theorem expected_gibbs_KL_sqrt_bound_of_sk_difference {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (beta delta : ℝ) (hdelta : 0 ≤ delta) (W V : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hW : Measurable W) (hV : Measurable V)
    (hdifference : HasLaw (fun ω ↦ W ω - V ω)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix (Real.sqrt delta / Real.sqrt (2 * (n : ℝ))))) μ) :
    (Integrable (fun ω ↦ finiteKL (gibbsProbability beta (W ω))
      (gibbsProbability beta (V ω))) μ) ∧
    (∫ ω, finiteKL (gibbsProbability beta (W ω)) (gibbsProbability beta (V ω)) ∂μ) ≤
      2 * |beta| * Real.sqrt (2 * Real.log 2) * (n : ℝ) * Real.sqrt delta := by
  have h := expected_gibbs_KL_le_goe_expected_max_of_difference hn μ beta
    (Real.sqrt delta / Real.sqrt (2 * (n : ℝ))) W V hW hV hdifference
  refine ⟨h.1, h.2.trans ?_⟩
  convert mul_le_mul_of_nonneg_left
    (skPerturbationHamiltonianMaximum_expected_sqrt_bound hn delta hdelta)
    (by positivity : 0 ≤ 2 * |beta|) using 1
  ring

theorem quadraticHamiltonian_neg {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    quadraticHamiltonian (-W) x = -quadraticHamiltonian W x := by
  simp [quadraticHamiltonian, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem goeMatrix_neg_scale {n : ℕ} (sigma : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    GaussianProposal.goeMatrix (-sigma) z = -GaussianProposal.goeMatrix sigma z := by
  ext i j
  simp [GaussianProposal.goeMatrix]

theorem goeHamiltonianMaximum_neg_scale {n : ℕ} (sigma : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    goeHamiltonianMaximum (-sigma) z = goeHamiltonianMaximum sigma z := by
  unfold goeHamiltonianMaximum finiteMaxAbs
  simp only [Finset.sup'_apply]
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro x _
  simp only [goeSpinHamiltonian, goeMatrix_neg_scale, quadraticHamiltonian_neg, abs_neg]

theorem goe_difference_law_reverse {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (sigma : ℝ) (W V : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hdifference : HasLaw (fun ω ↦ W ω - V ω)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix (ι := Fin n) sigma)) μ) :
    HasLaw (fun ω ↦ V ω - W ω)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix (ι := Fin n) (-sigma))) μ := by
  have hneg : HasLaw (fun w : Matrix (Fin n) (Fin n) ℝ ↦ -w)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix (ι := Fin n) (-sigma)))
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix (ι := Fin n) sigma)) := by
    refine ⟨measurable_neg.aemeasurable, ?_⟩
    rw [Measure.map_map measurable_neg (continuous_goeMatrix sigma).measurable]
    congr 1
    funext z
    exact (goeMatrix_neg_scale sigma z).symm
  simpa only [neg_sub] using hneg.fun_comp hdifference

theorem expected_reverse_gibbs_KL_sqrt_bound_of_sk_difference {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (beta delta : ℝ) (hdelta : 0 ≤ delta) (W V : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hW : Measurable W) (hV : Measurable V)
    (hdifference : HasLaw (fun ω ↦ W ω - V ω)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (GaussianProposal.goeMatrix (Real.sqrt delta / Real.sqrt (2 * (n : ℝ))))) μ) :
    (Integrable (fun ω ↦ finiteKL (gibbsProbability beta (V ω))
      (gibbsProbability beta (W ω))) μ) ∧
    (∫ ω, finiteKL (gibbsProbability beta (V ω)) (gibbsProbability beta (W ω)) ∂μ) ≤
      2 * |beta| * Real.sqrt (2 * Real.log 2) * (n : ℝ) * Real.sqrt delta := by
  have h := expected_gibbs_KL_le_goe_expected_max_of_difference hn μ beta
    (-(Real.sqrt delta / Real.sqrt (2 * (n : ℝ)))) V W hV hW
    (goe_difference_law_reverse μ _ W V hdifference)
  simp only [goeHamiltonianMaximum_neg_scale] at h
  refine ⟨h.1, h.2.trans ?_⟩
  convert mul_le_mul_of_nonneg_left
    (skPerturbationHamiltonianMaximum_expected_sqrt_bound hn delta hdelta)
    (by positivity : 0 ≤ 2 * |beta|) using 1
  ring

end SKConstants

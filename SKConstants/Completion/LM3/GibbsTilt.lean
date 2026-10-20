module
public import SKConstants.Completion.LC4a.ReplayKL
public import SKConstants.Completion.LC0.TerminalLink
public import SKConstants.Completion.LF0.EnergyMoments
public import SKConstants.ProposalGibbsChangeOfMeasure
public import SKConstants.GaussianRotation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology Classical

namespace SKConstants.Completion.LM3

def matrixGibbsDensity (n : ℕ) (β : ℝ)
    (u : Matrix (Fin n) (Fin n) ℝ × Spin n) : ℝ :=
  (2 : ℝ)^n * gibbsProbability β u.1 u.2

theorem matrixGibbsDensity_pos (n : ℕ) (β : ℝ)
    (u : Matrix (Fin n) (Fin n) ℝ × Spin n) : 0 < matrixGibbsDensity n β u :=
  mul_pos (pow_pos (by norm_num) _) (gibbsProbability_pos β _ _)

theorem measurable_matrixGibbsDensity (n : ℕ) (β : ℝ) :
    Measurable (matrixGibbsDensity n β) := by
  have h : Measurable (fun u : Spin n × Matrix (Fin n) (Fin n) ℝ =>
      matrixGibbsDensity n β (u.2, u.1)) := by
    apply measurable_from_prod_countable_right
    intro x
    change Measurable (fun W : Matrix (Fin n) (Fin n) ℝ =>
      (2 : ℝ)^n * gibbsProbability β W x)
    exact measurable_const.mul (continuous_gibbsProbability β x).measurable
  change Measurable ((fun u : Spin n × Matrix (Fin n) (Fin n) ℝ =>
    matrixGibbsDensity n β (u.2, u.1)) ∘ Prod.swap)
  exact h.comp measurable_swap

theorem log_matrixGibbsDensity (n : ℕ) (β : ℝ)
    (u : Matrix (Fin n) (Fin n) ℝ × Spin n) :
    Real.log (matrixGibbsDensity n β u) = (n : ℝ) * Real.log 2 +
      β * quadraticHamiltonian u.1 u.2 - Real.log (gibbsPartition β u.1) := by
  rw [matrixGibbsDensity, Real.log_mul (pow_ne_zero _ (by norm_num))
    (gibbsProbability_pos β _ _).ne', Real.log_pow, log_gibbsProbability]
  ring

theorem spinPrior_eq_uniformSpinLaw (n : ℕ) : M1.spinPrior n = uniformSpinLaw n := by
  apply Measure.ext_of_singleton
  intro x
  rw [M1.spinPrior, Measure.pi_singleton, uniformSpinLaw,
    finiteWeightMeasure_apply _ _ (measurableSet_singleton x)]
  simp only [mem_singleton_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hb (b : Bool) : scalarHiddenPriorBool 0 {b} = ENNReal.ofReal (1 / 2 : ℝ) := by
    cases b <;> norm_num [scalarHiddenPriorBool, scalarPlusWeight, scalarMinusWeight,
      Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply']
  simp_rw [hb]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [div_pow, one_pow]

theorem matrixGibbsDensity_withDensity (n : ℕ) (β : ℝ) :
    ((skDisorderLaw n).prod (M1.spinPrior n)).withDensity
      (fun u => ENNReal.ofReal (matrixGibbsDensity n β u)) = skJointLaw n β := by
  let g : Matrix (Fin n) (Fin n) ℝ → Spin n → ℝ≥0∞ :=
    fun W x => ENNReal.ofReal (matrixGibbsDensity n β (W, x))
  have hg : Measurable (Function.uncurry g) := (measurable_matrixGibbsDensity n β).ennreal_ofReal
  let κ := Kernel.const (Matrix (Fin n) (Fin n) ℝ) (M1.spinPrior n)
  have hk : κ.withDensity g = gibbsKernel n β := by
    apply Kernel.ext
    intro W
    rw [Kernel.withDensity_apply κ hg]
    change (M1.spinPrior n).withDensity (g W) = finiteWeightMeasure (gibbsProbability β W)
    rw [spinPrior_eq_uniformSpinLaw]
    apply Measure.ext_of_singleton
    intro x
    rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
      uniformSpinLaw, finiteWeightMeasure_apply _ _ (measurableSet_singleton x),
      finiteWeightMeasure_apply _ _ (measurableSet_singleton x)]
    simp only [mem_singleton_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    change ENNReal.ofReal ((2 : ℝ)^n * gibbsProbability β W x) *
      ENNReal.ofReal (1 / (2 : ℝ)^n) = _
    rw [← ENNReal.ofReal_mul
      (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n) (gibbsProbability_pos β W x)).le]
    congr 1
    field_simp
  let _ : IsMarkovKernel (κ.withDensity g) := by rw [hk]; infer_instance
  have ht := Measure.compProd_withDensity (μ := skDisorderLaw n) (κ := κ) hg
  rw [hk, Measure.compProd_const] at ht
  exact ht.symm

theorem gaussian_marginal_pressure_integrable {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsFiniteMeasure μ] {n : ℕ} (β : ℝ)
    (G : U → Matrix (Fin n) (Fin n) ℝ) (hG : Measurable G)
    (hmarg : μ.map G = skDisorderLaw n) :
    Integrable (fun u => Real.log (gibbsPartition β (G u))) μ := by
  have hlaw : HasLaw G (skDisorderLaw n) μ := ⟨hG.aemeasurable, hmarg⟩
  have hM := (hlaw.memLp_fun_comp (LF0.memLp_spinHamiltonianMaximum n)).integrable (by norm_num)
  apply ((integrable_const |Real.log (gibbsPartition β (0 : Matrix (Fin n) (Fin n) ℝ))|).add
    (hM.const_mul |β|)).mono'
      ((Real.measurable_log.comp (continuous_gibbsPartition β).measurable).comp hG).aestronglyMeasurable
  exact ae_of_all _ (fun u => by
    simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_def] using
      gibbsPressure_abs_le_maximum β (G u))

end SKConstants.Completion.LM3

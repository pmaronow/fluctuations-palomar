module

public import SKConstants.Completion.LF0.EnergyMoments
public import SKConstants.Asymptotics
public import SKConstants.GaussianRotation

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology

namespace SKConstants.Completion.LF0

theorem setIntegral_abs_le_sqrt_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, |f ω| ∂μ) ≤
      Real.sqrt (∫ ω, (f ω) ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
  let I : Ω → ℝ := A.indicator (fun _ => 1)
  have hI : MemLp I 2 μ := (memLp_const (1 : ℝ)).indicator hA
  have hI2 : (fun ω => I ω ^ 2) = I := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [I, hω]
  have hIF : (fun ω => |f ω| * I ω) = A.indicator (fun ω => |f ω|) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [I, hω]
  have habs : MemLp (fun ω => |f ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (f := fun ω => |f ω|) (g := I) (μ := μ)
    (ae_of_all _ (fun ω => abs_nonneg _))
    (ae_of_all _ (fun ω => by by_cases hω : ω ∈ A <;> simp [I, hω]))
    (by simpa using habs) (by simpa using hI)
  simp only [Real.rpow_two, sq_abs, one_div] at h
  rw [hIF, hI2, integral_indicator hA,
    show (∫ ω, I ω ∂μ) = μ.real A from integral_indicator_one hA] at h
  simpa only [Real.sqrt_eq_rpow, one_div] using h

theorem setIntegral_abs_le_sqrt_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ)
    (B : ℝ) (hB : (∫ ω, (f ω) ^ 2 ∂μ) ≤ B)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, |f ω| ∂μ) ≤ Real.sqrt (B * μ.real A) := by
  calc
    _ ≤ Real.sqrt (∫ ω, (f ω) ^ 2 ∂μ) * Real.sqrt (μ.real A) :=
      setIntegral_abs_le_sqrt_second_moment μ f hf A hA
    _ ≤ Real.sqrt B * Real.sqrt (μ.real A) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
    _ = _ := (Real.sqrt_mul
      ((integral_nonneg (μ := μ) (fun ω => sq_nonneg (f ω))).trans hB) _).symm

theorem gaussian_marginal_energy_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ}
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (X : Ω → Spin n)
    (hW : Measurable W) (hX : Measurable X)
    (hmarg : μ.map W = skDisorderLaw n) :
    Integrable (fun ω => quadraticHamiltonian (W ω) (X ω)) μ := by
  have hlaw : HasLaw W (skDisorderLaw n) μ := ⟨hW.aemeasurable, hmarg⟩
  have := hlaw.isProbabilityMeasure
  exact (gaussian_marginal_energy_memLp μ W X hW hX hmarg).integrable (by norm_num)

theorem gaussian_marginal_exceptional_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (X : Ω → Spin n)
    (hW : Measurable W) (hX : Measurable X)
    (hmarg : μ.map W = skDisorderLaw n)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, |quadraticHamiltonian (W ω) (X ω)| ∂μ) ≤
      (n : ℝ) / 2 * Real.sqrt (((n : ℝ) + 1) * μ.real A) := by
  have hlaw : HasLaw W (skDisorderLaw n) μ := ⟨hW.aemeasurable, hmarg⟩
  have := hlaw.isProbabilityMeasure
  have h := setIntegral_abs_le_sqrt_budget μ _
    (gaussian_marginal_energy_memLp μ W X hW hX hmarg) _
    (gaussian_marginal_energy_second_moment μ hn W X hW hX hmarg) A hA
  calc
    _ ≤ Real.sqrt ((n : ℝ) ^ 2 * ((n : ℝ) + 1) / 4 * μ.real A) := h
    _ = (n : ℝ) / 2 * Real.sqrt (((n : ℝ) + 1) * μ.real A) := by
      rw [show (n : ℝ) ^ 2 * ((n : ℝ) + 1) / 4 * μ.real A =
        ((n : ℝ) / 2) ^ 2 * (((n : ℝ) + 1) * μ.real A) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

theorem gaussian_marginal_exceptional_energy_normalized {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (X : Ω → Spin n)
    (hW : Measurable W) (hX : Measurable X)
    (hmarg : μ.map W = skDisorderLaw n)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, |quadraticHamiltonian (W ω) (X ω)| / (n : ℝ) ∂μ) ≤
      Real.sqrt (((n : ℝ) + 1) * μ.real A) / 2 := by
  rw [integral_div]
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    _ ≤ ((n : ℝ) / 2 * Real.sqrt (((n : ℝ) + 1) * μ.real A)) / (n : ℝ) :=
      div_le_div_of_nonneg_right
        (gaussian_marginal_exceptional_energy μ hn W X hW hX hmarg A hA) hnR.le
    _ = _ := by field_simp

theorem gaussian_marginal_exceptional_maximum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (hW : Measurable W)
    (hmarg : μ.map W = skDisorderLaw n)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, spinHamiltonianMaximum (W ω) ∂μ) ≤
      (n : ℝ) / 2 * Real.sqrt (((n : ℝ) + 1) * μ.real A) := by
  have hlaw : HasLaw W (skDisorderLaw n) μ := ⟨hW.aemeasurable, hmarg⟩
  have := hlaw.isProbabilityMeasure
  have hmoment : (∫ ω, (spinHamiltonianMaximum (W ω)) ^ 2 ∂μ) ≤
      (n : ℝ) ^ 2 * ((n : ℝ) + 1) / 4 := by
    calc
      _ = ∫ W, (spinHamiltonianMaximum W) ^ 2 ∂skDisorderLaw n :=
        hlaw.integral_comp (continuous_spinHamiltonianMaximum.pow 2).measurable.aestronglyMeasurable
      _ ≤ _ := sk_spinHamiltonianMaximum_second_moment hn
  have h := setIntegral_abs_le_sqrt_budget μ _
    (hlaw.memLp_fun_comp (memLp_spinHamiltonianMaximum n)) _ hmoment A hA
  have hnonneg : ∀ ω, 0 ≤ spinHamiltonianMaximum (W ω) :=
    fun ω => finiteMaxAbs_nonneg _ _
  simp_rw [abs_of_nonneg (hnonneg _)] at h
  calc
    _ ≤ Real.sqrt ((n : ℝ) ^ 2 * ((n : ℝ) + 1) / 4 * μ.real A) := h
    _ = _ := by
      rw [show (n : ℝ) ^ 2 * ((n : ℝ) + 1) / 4 * μ.real A =
        ((n : ℝ) / 2) ^ 2 * (((n : ℝ) + 1) * μ.real A) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

theorem gibbsPressure_abs_le {n : ℕ} (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    |Real.log (gibbsPartition beta W)| ≤
      (n : ℝ) * Real.log 2 + |beta| * spinHamiltonianMaximum W := by
  have hz : gibbsPartition beta (0 : Matrix (Fin n) (Fin n) ℝ) = (2 : ℝ) ^ n := by
    simp [gibbsPartition, quadraticHamiltonian, Spin]
  have hlog : 0 ≤ (n : ℝ) * Real.log 2 := by positivity
  simpa only [hz, Real.log_pow, abs_of_nonneg hlog] using
    gibbsPressure_abs_le_maximum beta W

theorem gaussian_marginal_pressure_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (beta : ℝ)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (hW : Measurable W)
    (hmarg : μ.map W = skDisorderLaw n) :
    MemLp (fun ω => Real.log (gibbsPartition beta (W ω))) 2 μ := by
  have hlaw : HasLaw W (skDisorderLaw n) μ := ⟨hW.aemeasurable, hmarg⟩
  have := hlaw.isProbabilityMeasure
  have hmax := hlaw.memLp_fun_comp (memLp_spinHamiltonianMaximum n)
  apply ((memLp_const ((n : ℝ) * Real.log 2)).add (hmax.const_mul |beta|)).mono'
    (Real.measurable_log.comp ((continuous_gibbsPartition beta).measurable.comp hW)).aestronglyMeasurable
  filter_upwards with ω
  exact gibbsPressure_abs_le beta (W ω)

theorem gaussian_marginal_exceptional_pressure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ) (hW : Measurable W)
    (hmarg : μ.map W = skDisorderLaw n)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, |Real.log (gibbsPartition beta (W ω))| ∂μ) ≤
      (n : ℝ) * Real.log 2 * μ.real A +
        |beta| * ((n : ℝ) / 2 * Real.sqrt (((n : ℝ) + 1) * μ.real A)) := by
  have hlaw : HasLaw W (skDisorderLaw n) μ := ⟨hW.aemeasurable, hmarg⟩
  have := hlaw.isProbabilityMeasure
  have hmax := (hlaw.memLp_fun_comp (memLp_spinHamiltonianMaximum n)).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hpressure := (gaussian_marginal_pressure_memLp μ beta W hW hmarg).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  calc
    _ ≤ ∫ ω in A, (n : ℝ) * Real.log 2 + |beta| * spinHamiltonianMaximum (W ω) ∂μ :=
      setIntegral_mono_on hpressure.abs.integrableOn
        ((integrable_const _).add (hmax.const_mul _)).integrableOn hA
        (fun ω _ => gibbsPressure_abs_le beta (W ω))
    _ = (n : ℝ) * Real.log 2 * μ.real A +
        |beta| * (∫ ω in A, spinHamiltonianMaximum (W ω) ∂μ) := by
      rw [integral_add (integrable_const _).integrableOn (hmax.const_mul _).integrableOn,
        setIntegral_const, integral_const_mul]
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (gaussian_marginal_exceptional_maximum μ hn W hW hmarg A hA) (abs_nonneg beta))

end SKConstants.Completion.LF0

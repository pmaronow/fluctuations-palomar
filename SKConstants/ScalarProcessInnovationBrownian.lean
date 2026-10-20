module

public import SKConstants.ScalarProcessUniformMesh
public import SKConstants.ScalarProcessFiniteDimensional
public import SKConstants.ScalarProcessInnovationPrefixes
public import SKConstants.ScalarProcessPrefixComparison

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem scalarUniformTime_floor_tendsto (T : ℝ≥0) :
    Tendsto (fun n => scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊)
      atTop (𝓝 T) := by
  simp_rw [scalarUniformTime_floor_eq]
  simpa only [Real.toNNReal_coe] using
    tendsto_real_toNNReal (scalarLeftMeshSample_tendsto (T : ℝ) T.coe_nonneg)

theorem scalarUniformInnovationFourier_ae_tendsto {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (theta : ι → ℝ) (T : ι → ℝ≥0) :
    ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      Tendsto (fun n => ∑ i, theta i * scalarEulerInnovation z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊) n u)
        atTop (𝓝 (∑ i, theta i * scalarContinuousInnovation z B (T i) u)) := by
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  filter_upwards [hc] with u hu
  apply tendsto_finsetSum
  intro i hi
  simp_rw [scalarUniformTime_floor_eq]
  exact (scalarEulerInnovation_prefix_tendsto_path z B (T i) u hu).const_mul (theta i)

theorem scalarUniformBrownianFourier_ae_tendsto {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (theta : ι → ℝ) (T : ι → ℝ≥0) :
    ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      Tendsto (fun n => ∑ i, theta i *
        (B (scalarUniformTime n ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊) u.2 - B 0 u.2))
        atTop (𝓝 (∑ i, theta i * B (T i) u.2)) := by
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  filter_upwards [hc, hz] with u hu hz
  apply tendsto_finsetSum
  intro i hi
  have h := ((hu.tendsto (T i)).comp (scalarUniformTime_floor_tendsto (T i))).sub_const (B 0 u.2)
  simpa only [hz, sub_zero, Function.comp_def] using h.const_mul (theta i)

theorem aemeasurable_scalarUniformInnovationFourier {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (theta : ι → ℝ) (T : ι → ℝ≥0) (n : ℕ) :
    AEMeasurable (fun u => ∑ i, theta i * scalarEulerInnovation z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊) n u)
      (scalarHiddenBrownianLaw z P) := by
  apply Finset.aemeasurable_fun_sum
  intro i hi
  exact (aemeasurable_scalarEulerInnovation P z B hB _ n).const_mul (theta i)

theorem aemeasurable_scalarUniformBrownianFourier {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (theta : ι → ℝ) (T : ι → ℝ≥0) (n : ℕ) :
    AEMeasurable (fun u : Bool × Ω => ∑ i, theta i *
      (B (scalarUniformTime n ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊) u.2 - B 0 u.2))
      (scalarHiddenBrownianLaw z P) := by
  apply Finset.aemeasurable_fun_sum
  intro i hi
  exact (((hB.aemeasurable _).comp_snd).sub ((hB.aemeasurable 0).comp_snd)).const_mul (theta i)

theorem scalarContinuousInnovation_linear_characteristic {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (theta : ι → ℝ) (T : ι → ℝ≥0) :
    (∫ u, Complex.exp (((∑ i, theta i * scalarContinuousInnovation z B (T i) u : ℝ) : ℂ) *
      Complex.I) ∂scalarHiddenBrownianLaw z P) =
      ∫ u, Complex.exp (((∑ i, theta i * B (T i) u.2 : ℝ) : ℂ) * Complex.I)
        ∂scalarHiddenBrownianLaw z P := by
  apply integral_characteristic_eq_of_mesh_comparison (scalarHiddenBrownianLaw z P)
    (fun n u => ∑ i, theta i * scalarEulerInnovation z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊) n u)
    (fun n u => ∑ i, theta i *
      (B (scalarUniformTime n ⌊((n : ℝ) + 1) * (T i : ℝ)⌋₊) u.2 - B 0 u.2))
    _ _
    (aemeasurable_scalarUniformInnovationFourier P z B hB.toIsPreBrownianReal theta T)
    (aemeasurable_scalarUniformBrownianFourier P z B hB.toIsPreBrownianReal theta T)
    (scalarUniformInnovationFourier_ae_tendsto P z B hB theta T)
    (scalarUniformBrownianFourier_ae_tendsto P z B hB theta T)
    (fun n => Real.exp (2 * ∑ i, |theta i|) / ((n : ℝ) + 1) *
      (∑ i, |theta i|) ^ 2 * ∑ i, (T i : ℝ))
  · have h := ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (Real.exp (2 * ∑ i, |theta i|))).mul_const ((∑ i, |theta i|) ^ 2)).mul_const
        (∑ i, (T i : ℝ))
    simpa only [mul_zero, zero_mul, div_eq_mul_inv, one_mul] using h
  · intro n
    exact scalarUniformPrefixes_characteristic_error z hB.toIsPreBrownianReal theta T n

theorem scalarContinuousInnovation_isBrownianReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) :
    IsBrownianReal (scalarContinuousInnovation z B) (scalarHiddenBrownianLaw z P) where
  cont := scalarContinuousInnovation_ae_continuous P z B hB
  toIsPreBrownianReal := {
    hasLaw := fun I => by
      have hmX : ∀ i : I, AEMeasurable (scalarContinuousInnovation z B i)
          (scalarHiddenBrownianLaw z P) := fun i =>
        (aestronglyMeasurable_scalarContinuousInnovation P z B hB i).aemeasurable
      have hmY : ∀ i : I, AEMeasurable (fun u : Bool × Ω => B i u.2)
          (scalarHiddenBrownianLaw z P) := fun i => (hB.aemeasurable i).comp_snd
      have heq := map_eq_of_linear_characteristic (scalarHiddenBrownianLaw z P)
        (fun i : I => scalarContinuousInnovation z B i)
        (fun (i : I) (u : Bool × Ω) => B i u.2) hmX hmY
        (fun theta => scalarContinuousInnovation_linear_characteristic P z B hB theta
          (fun i : I => i))
      have hOrig : HasLaw (fun u : Bool × Ω => I.restrict (fun t => B t u.2))
          (BrownianReal.projectiveFamily I) (scalarHiddenBrownianLaw z P) := by
        simpa only [Function.comp_def, scalarHiddenBrownianLaw] using (hB.hasLaw I).comp
          (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).hasLaw
      refine ⟨AEMeasurable.of_eval hmX, ?_⟩
      change (scalarHiddenBrownianLaw z P).map
        (fun u (i : I) => scalarContinuousInnovation z B i u) = _
      rw [heq]
      exact hOrig.map_eq }

theorem scalarHiddenContinuousField_innovation_drift {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : Bool × Ω) :
    scalarHiddenContinuousField z B T u =
      z + scalarContinuousInnovation z B T u + scalarContinuousDrift z B T u := by
  unfold scalarContinuousInnovation
  ring

end SKConstants

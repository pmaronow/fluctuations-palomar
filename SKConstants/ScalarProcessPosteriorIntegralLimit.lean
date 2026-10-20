module

public import SKConstants.ScalarProcessPosteriorIntegral
public import SKConstants.ScalarProcessInnovationBrownian

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem aemeasurable_scalarHiddenContinuousField {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    AEMeasurable (scalarHiddenContinuousField z B T) (scalarHiddenBrownianLaw z P) := by
  have hs : AEMeasurable (fun u : Bool × Ω => scalarHiddenSign u.1)
      (scalarHiddenBrownianLaw z P) :=
    ((measurable_of_finite scalarHiddenSign).comp measurable_fst).aemeasurable
  have hb : AEMeasurable (fun u : Bool × Ω => B T u.2)
      (scalarHiddenBrownianLaw z P) := (hB.aemeasurable T).comp_snd
  exact (aemeasurable_const.add (hs.mul_const (T : ℝ))).add hb

theorem aemeasurable_scalarUniformPosteriorIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    AEMeasurable (scalarUniformPosteriorIntegral z B n T) (scalarHiddenBrownianLaw z P) :=
  (measurable_scalarPosteriorIntegralSum z _ _).comp_aemeasurable
    (scalarUniformObservationHistory_hasLaw hB z n _).aemeasurable

theorem integrable_scalarUniformPosteriorIntegral_square_error {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun u => (Real.tanh (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) - Real.tanh z -
        scalarUniformPosteriorIntegral z B n T u) ^ 2) (scalarHiddenBrownianLaw z P) := by
  let m := ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  let dt := brownianMeshVariance (scalarUniformTime n)
  have hdt : ∀ k, dt k ≤ 1 := scalarUniformMeshVariance_le_one n
  have h := (scalarUniformObservationHistory_hasLaw hB z n m).integrable_comp
    (integrable_scalarPosteriorIntegralSum_square_error z dt hdt m)
  apply h.congr
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  filter_upwards [hz] with u hu
  simp only [Function.comp_def, scalarLastField_uniform z B n m u hu]
  rfl

theorem scalarUniformPosteriorEndpoint_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u,
      (Real.tanh (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
        Real.tanh (scalarHiddenContinuousField z B T u)) ^ 2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 0) := by
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hlim : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      Tendsto (fun n =>
        (Real.tanh (scalarHiddenContinuousField z B
          (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
          Real.tanh (scalarHiddenContinuousField z B T u)) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hc] with u hu
    have hycont : Continuous (fun t => scalarHiddenContinuousField z B t u) :=
      (continuous_const.add (continuous_const.mul NNReal.continuous_coe)).add hu
    have hy := (hycont.tendsto T).comp (scalarUniformTime_floor_tendsto T)
    have hm := (continuous_scalarTanh.tendsto _).comp hy
    simpa only [Function.comp_def, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hm.sub_const (Real.tanh (scalarHiddenContinuousField z B T u))).pow 2
  have h := tendsto_integral_of_dominated_convergence (μ := scalarHiddenBrownianLaw z P) (fun _ => (4 : ℝ))
    (F := fun n u =>
      (Real.tanh (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
        Real.tanh (scalarHiddenContinuousField z B T u)) ^ 2)
    (f := fun _ => (0 : ℝ))
  suffices hres : Tendsto (fun n => ∫ u,
      (Real.tanh (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
        Real.tanh (scalarHiddenContinuousField z B T u)) ^ 2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 (∫ _ : Bool × Ω, (0 : ℝ) ∂scalarHiddenBrownianLaw z P)) by
    simpa only [integral_zero] using hres
  apply h
  · intro n
    exact (((measurable_scalarTanh.comp_aemeasurable
      (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal _)).sub
      (measurable_scalarTanh.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal T))).pow_const 2).aestronglyMeasurable
  · exact integrable_const 4
  · intro n
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb : |Real.tanh (scalarHiddenContinuousField z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
      Real.tanh (scalarHiddenContinuousField z B T u)| ≤ 2 :=
      (abs_sub _ _).trans (by linarith [scalar_tanh_abs_le_one (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u),
        scalar_tanh_abs_le_one (scalarHiddenContinuousField z B T u)])
    nlinarith [abs_nonneg (Real.tanh (scalarHiddenContinuousField z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
      Real.tanh (scalarHiddenContinuousField z B T u)), sq_abs (Real.tanh (scalarHiddenContinuousField z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
      Real.tanh (scalarHiddenContinuousField z B T u))]
  · exact hlim

theorem integrable_scalarUniformPosteriorEndpoint_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun u =>
      (Real.tanh (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
        Real.tanh (scalarHiddenContinuousField z B T u)) ^ 2) (scalarHiddenBrownianLaw z P) := by
  apply Integrable.of_bound
    (((measurable_scalarTanh.comp_aemeasurable
      (aemeasurable_scalarHiddenContinuousField P z B hB _)).sub
      (measurable_scalarTanh.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB T))).pow_const 2).aestronglyMeasurable 4
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (Real.tanh (scalarHiddenContinuousField z B
    (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
    Real.tanh (scalarHiddenContinuousField z B T u)) ^ 2 ≤ 4
  have hb : |Real.tanh (scalarHiddenContinuousField z B
    (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
    Real.tanh (scalarHiddenContinuousField z B T u)| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [scalar_tanh_abs_le_one (scalarHiddenContinuousField z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u),
      scalar_tanh_abs_le_one (scalarHiddenContinuousField z B T u)])
  nlinarith [abs_nonneg (Real.tanh (scalarHiddenContinuousField z B
    (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
    Real.tanh (scalarHiddenContinuousField z B T u)), sq_abs (Real.tanh (scalarHiddenContinuousField z B
    (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
    Real.tanh (scalarHiddenContinuousField z B T u))]

theorem scalarUniformPosteriorIntegral_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u,
      (scalarUniformPosteriorIntegral z B n T u -
        (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z)) ^ 2
        ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  let A := fun n u => Real.tanh (scalarHiddenContinuousField z B
    (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) - Real.tanh z -
      scalarUniformPosteriorIntegral z B n T u
  let D := fun n u => Real.tanh (scalarHiddenContinuousField z B
    (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
      Real.tanh (scalarHiddenContinuousField z B T u)
  let target := fun n u => scalarUniformPosteriorIntegral z B n T u -
      (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z)
  have hbound : ∀ n u, target n u ^ 2 ≤ 2 * A n u ^ 2 + 2 * D n u ^ 2 := by
    intro n u
    have he : target n u = D n u - A n u := by dsimp [target, A, D]; ring
    rw [he]
    nlinarith [sq_nonneg (A n u + D n u)]
  have hA : ∀ n, Integrable (fun u => A n u ^ 2) (scalarHiddenBrownianLaw z P) :=
    fun n => integrable_scalarUniformPosteriorIntegral_square_error P z B hB.toIsPreBrownianReal T n
  have hD : ∀ n, Integrable (fun u => D n u ^ 2) (scalarHiddenBrownianLaw z P) :=
    fun n => integrable_scalarUniformPosteriorEndpoint_sq P z B hB.toIsPreBrownianReal T n
  have htar : ∀ n, Integrable (fun u => target n u ^ 2) (scalarHiddenBrownianLaw z P) := by
    intro n
    apply ((hA n).const_mul 2 |>.add ((hD n).const_mul 2)).mono'
    · exact (((aemeasurable_scalarUniformPosteriorIntegral P z B hB.toIsPreBrownianReal T n).sub
        ((measurable_scalarTanh.comp_aemeasurable
          (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal T)).sub_const
            (Real.tanh z))).pow_const 2).aestronglyMeasurable
    · apply ae_of_all
      intro u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound n u
  have hintbound : ∀ n, (∫ u, target n u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      2 * (82 * (T : ℝ) / ((n : ℝ) + 1)) +
        2 * ∫ u, D n u ^ 2 ∂scalarHiddenBrownianLaw z P := by
    intro n
    have h := integral_mono (htar n) (((hA n).const_mul 2).add ((hD n).const_mul 2)) (hbound n)
    simp only [Pi.add_apply] at h
    rw [integral_add ((hA n).const_mul 2) ((hD n).const_mul 2), integral_const_mul,
      integral_const_mul] at h
    have hb : 2 * (∫ u, A n u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
        2 * (82 * (T : ℝ) / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left
        (scalarUniformPosteriorIntegral_square_error P z B hB.toIsPreBrownianReal T n)
        (by norm_num : (0 : ℝ) ≤ 2)
    exact h.trans (add_le_add hb le_rfl)
  have hfirst : Tendsto (fun (n : ℕ) => 2 * (82 * (T : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (82 * (T : ℝ))).const_mul 2
    simpa only [mul_zero, div_eq_mul_inv, one_mul] using h
  have hlast : Tendsto (fun n => 2 * ∫ u, D n u ^ 2 ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
    simpa only [mul_zero] using (scalarUniformPosteriorEndpoint_tendsto_L2 P z B hB T).const_mul 2
  apply squeeze_zero (fun n => integral_nonneg (fun u => sq_nonneg _)) hintbound
  simpa only [zero_add] using hfirst.add hlast

end SKConstants

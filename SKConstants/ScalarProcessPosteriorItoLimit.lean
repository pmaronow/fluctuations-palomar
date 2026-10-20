module
public import SKConstants.ScalarProcessWeightedMesh
public import SKConstants.ScalarProcessPosteriorIntegralLimit
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma norm_scalarDefect_le_one (y : ℝ) : ‖scalarDefect y‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (scalarDefect_pos y).le]
  exact scalarDefect_le_one y

lemma scalarPosteriorIntegralSum_uniform_eq_weightedInnovationMeshSum {Ω : Type*}
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (n m : ℕ) (u : Bool × Ω) (hzero : B 0 u.2 = 0) :
    scalarPosteriorIntegralSum z (brownianMeshVariance (scalarUniformTime n)) m
      (scalarUniformObservationHistory z B n m u) =
      scalarWeightedInnovationMeshSum scalarDefect z B n m u := by
  induction m with
  | zero => simp [scalarPosteriorIntegralSum, scalarWeightedInnovationMeshSum]
  | succ m ih =>
    change scalarPosteriorIntegralSum z (brownianMeshVariance (scalarUniformTime n)) m
        (scalarUniformObservationHistory z B n m u) +
      scalarDefect (scalarLastField z m (scalarUniformObservationHistory z B n m u)) *
        scalarInnovation (scalarLastField z m (scalarUniformObservationHistory z B n m u))
          (brownianMeshVariance (scalarUniformTime n) m)
          (scalarHiddenContinuousField z B (scalarUniformTime n (m + 1)) u) = _
    rw [ih, scalarLastField_uniform z B n m u hzero]
    exact (Finset.sum_range_succ _ m).symm

lemma scalarUniformPosteriorIntegral_eq_weightedInnovationMeshSum {Ω : Type*}
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (T : ℝ≥0) (u : Bool × Ω) (hzero : B 0 u.2 = 0) :
    scalarUniformPosteriorIntegral z B n T u =
      scalarWeightedInnovationMeshSum scalarDefect z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u :=
  scalarPosteriorIntegralSum_uniform_eq_weightedInnovationMeshSum z B n _ u hzero

lemma integrable_scalarUniformPosteriorIntegral_continuous_square_error {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun u => (scalarUniformPosteriorIntegral z B n T u -
      (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z)) ^ 2)
      (scalarHiddenBrownianLaw z P) := by
  let A := fun u => Real.tanh (scalarHiddenContinuousField z B
    (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) - Real.tanh z -
      scalarUniformPosteriorIntegral z B n T u
  let D := fun u => Real.tanh (scalarHiddenContinuousField z B
    (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
      Real.tanh (scalarHiddenContinuousField z B T u)
  have hA : Integrable (fun u => (A u) ^ 2) (scalarHiddenBrownianLaw z P) :=
    integrable_scalarUniformPosteriorIntegral_square_error P z B hB T n
  have hD : Integrable (fun u => (D u) ^ 2) (scalarHiddenBrownianLaw z P) :=
    integrable_scalarUniformPosteriorEndpoint_sq P z B hB T n
  apply (((hA.const_mul 2).add (hD.const_mul 2))).mono'
  · exact (((aemeasurable_scalarUniformPosteriorIntegral P z B hB T n).sub
      ((measurable_scalarTanh.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB T)).sub_const
          (Real.tanh z))).pow_const 2).aestronglyMeasurable
  · apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (scalarUniformPosteriorIntegral z B n T u -
      (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z)) ^ 2 ≤
        2 * (A u) ^ 2 + 2 * (D u) ^ 2
    have he : scalarUniformPosteriorIntegral z B n T u -
        (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z) = D u - A u := by
      dsimp [D, A]
      ring
    rw [he]
    nlinarith [sq_nonneg (A u + D u)]

lemma scalarWeightedBrownianMeshSum_posterior_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, (scalarWeightedBrownianMeshSum scalarDefect z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u -
      (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z)) ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (nhds 0) := by
  let m : ℕ → ℕ := fun n => ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  let A : ℕ → Bool × Ω → ℝ := fun n u => scalarWeightedInnovationMeshSum scalarDefect z B n (m n) u -
    scalarWeightedBrownianMeshSum scalarDefect z B n (m n) u
  let D : ℕ → Bool × Ω → ℝ := fun n u => scalarUniformPosteriorIntegral z B n T u -
    (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z)
  let target : ℕ → Bool × Ω → ℝ := fun n u => scalarWeightedBrownianMeshSum scalarDefect z B n (m n) u -
    (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z)
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  have hbound (n : ℕ) : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      (target n u) ^ 2 ≤ 2 * (A n u) ^ 2 + 2 * (D n u) ^ 2 := by
    filter_upwards [hz] with u hu
    have he : target n u = D n u - A n u := by
      dsimp only [target, D, A]
      rw [scalarUniformPosteriorIntegral_eq_weightedInnovationMeshSum z B n T u hu]
      ring
    rw [he]
    nlinarith [sq_nonneg (A n u + D n u)]
  have hA (n : ℕ) : Integrable (fun u => (A n u) ^ 2) (scalarHiddenBrownianLaw z P) :=
    integrable_scalarWeightedInnovationMeshSum_sub_sq P scalarDefect measurable_scalarDefect
      norm_scalarDefect_le_one z B hB n (m n)
  have hD (n : ℕ) : Integrable (fun u => (D n u) ^ 2) (scalarHiddenBrownianLaw z P) :=
    integrable_scalarUniformPosteriorIntegral_continuous_square_error P z B hB.toIsPreBrownianReal T n
  have htarget (n : ℕ) : Integrable (fun u => (target n u) ^ 2) (scalarHiddenBrownianLaw z P) := by
    apply (((hA n).const_mul 2).add ((hD n).const_mul 2)).mono'
    · exact (((aemeasurable_scalarWeightedBrownianMeshSum P scalarDefect measurable_scalarDefect
        z B hB n (m n)).sub ((measurable_scalarTanh.comp_aemeasurable
          (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal T)).sub_const
            (Real.tanh z))).pow_const 2).aestronglyMeasurable
    · filter_upwards [hbound n] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hu
  have hint (n : ℕ) : (∫ u, (target n u) ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      2 * (∫ u, (A n u) ^ 2 ∂scalarHiddenBrownianLaw z P) +
      2 * (∫ u, (D n u) ^ 2 ∂scalarHiddenBrownianLaw z P) := by
    have hh := integral_mono_ae (htarget n) (((hA n).const_mul 2).add ((hD n).const_mul 2)) (hbound n)
    simp only [Pi.add_apply] at hh
    rw [integral_add ((hA n).const_mul 2) ((hD n).const_mul 2), integral_const_mul, integral_const_mul] at hh
    exact hh
  have hAlimit := scalarWeightedInnovationMeshSum_sub_tendsto_L2 P scalarDefect measurable_scalarDefect
    norm_scalarDefect_le_one z B hB T
  have hDlimit := scalarUniformPosteriorIntegral_tendsto_L2 P z B hB T
  apply squeeze_zero (fun n => integral_nonneg (fun u => sq_nonneg _)) hint
  simpa only [mul_zero, zero_add] using (hAlimit.const_mul 2).add (hDlimit.const_mul 2)

end SKConstants

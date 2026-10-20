module

public import SKConstants.ScalarProcessSignInnovationMoment
public import SKConstants.ScalarProcessPosteriorIntegralLimit

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

def scalarHiddenExpectedDefectReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ u, scalarDefect (scalarHiddenFieldReal z B s u) ∂scalarHiddenBrownianLaw z P

theorem continuous_scalarDefect_actual : Continuous scalarDefect := by
  exact continuous_const.sub (continuous_scalarTanh.pow 2)

theorem scalarHiddenExpectedDefectReal_norm_le_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ) :
    ‖scalarHiddenExpectedDefectReal P z B s‖ ≤ 1 := by
  have hb : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      ‖scalarDefect (scalarHiddenFieldReal z B s u)‖ ≤ (1 : ℝ) := by
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_pos (scalarDefect_pos _)]
    exact scalarDefect_le_one _
  simpa only [scalarHiddenExpectedDefectReal, probReal_univ, one_mul] using
    norm_integral_le_of_norm_le_const hb

theorem continuous_scalarHiddenExpectedDefectReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) : Continuous (scalarHiddenExpectedDefectReal P z B) := by
  apply continuous_iff_continuousAt.2
  intro s
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun s => (measurable_scalarDefect.comp_aemeasurable
      (aemeasurable_scalarHiddenFieldReal P z B hB.toIsPreBrownianReal s)).aestronglyMeasurable))
    (Eventually.of_forall (fun _ => ae_of_all _ (fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (scalarDefect_pos _)]
      exact scalarDefect_le_one _)))
    (integrable_const 1)
    (hc.mono (fun u hu =>
      (continuous_scalarDefect_actual.comp (continuous_scalarHiddenFieldReal z B u hu)).tendsto s))

theorem scalarHiddenExpectedDefectReal_grid {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (n k : ℕ) :
    scalarHiddenExpectedDefectReal P z B ((k : ℝ) / ((n : ℝ) + 1)) =
      ∫ u, scalarDefect (scalarHiddenContinuousField z B (scalarUniformTime n k) u)
        ∂scalarHiddenBrownianLaw z P := by
  rw [← scalarUniformTime_coe n k]
  unfold scalarHiddenExpectedDefectReal
  congr 1
  funext u
  simp only [scalarHiddenFieldReal, scalarHiddenContinuousField, Real.toNNReal_coe]

theorem scalarUniformHiddenSignInnovation_moment_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, scalarHiddenSign u.1 * scalarEulerInnovation z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) n u ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 (∫ s in Icc 0 (T : ℝ), scalarHiddenExpectedDefectReal P z B s)) := by
  let f := scalarHiddenExpectedDefectReal P z B
  have hb : ∀ s, ‖f s‖ ≤ 1 := scalarHiddenExpectedDefectReal_norm_le_one P z B
  have hfull := scalarEulerDrift_tendsto f (T : ℝ)
    (continuous_scalarHiddenExpectedDefectReal P z B hB) hb
  have hrem : Tendsto (fun (n : ℕ) =>
      ((T : ℝ) - (⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) / ((n : ℝ) + 1)) *
        f ((⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1))
    · intro n
      rw [norm_mul]
      have herror := scalarLeftMeshSample_error n (T : ℝ) T.coe_nonneg
      change |(T : ℝ) - scalarLeftMeshSample n (T : ℝ)| *
        ‖f (scalarLeftMeshSample n (T : ℝ))‖ ≤ 1 / ((n : ℝ) + 1)
      calc
        _ ≤ |(T : ℝ) - scalarLeftMeshSample n (T : ℝ)| := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)
        _ ≤ _ := by simpa only [abs_sub_comm] using herror
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum := hfull.sub hrem
  have he (n : ℕ) : (∫ u, scalarHiddenSign u.1 * scalarEulerInnovation z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) n u ∂scalarHiddenBrownianLaw z P) =
      scalarEulerDrift f (T : ℝ) n -
        (((T : ℝ) - (⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) / ((n : ℝ) + 1)) *
          f ((⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) / ((n : ℝ) + 1))) := by
    rw [integral_scalarUniformHiddenSignInnovation z hB.toIsPreBrownianReal]
    rw [scalarEulerDrift_eq_finite_sum f (T : ℝ) T.coe_nonneg n hb, add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [scalarHiddenExpectedDefectReal_grid]
  simp_rw [he]
  simpa only [sub_zero] using hsum

theorem scalarHiddenSign_norm_one (b : Bool) : ‖scalarHiddenSign b‖ = 1 := by
  cases b <;> norm_num [scalarHiddenSign]

theorem integrable_scalarHiddenSign_brownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    Integrable (fun u : Bool × Ω => scalarHiddenSign u.1 * B T u.2)
      (scalarHiddenBrownianLaw z P) := by
  have hb := (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).integrable_comp_of_integrable
    (hB.integrable_eval T)
  exact hb.bdd_mul
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).aestronglyMeasurable)
    (ae_of_all _ (fun u => (scalarHiddenSign_norm_one u.1).le))

theorem integral_scalarHiddenSign_brownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    (∫ u : Bool × Ω, scalarHiddenSign u.1 * B T u.2 ∂scalarHiddenBrownianLaw z P) = 0 := by
  change (∫ u : Bool × Ω, scalarHiddenSign u.1 * B T u.2
    ∂(scalarHiddenPriorBool z).prod P) = 0
  rw [integral_prod_mul, hB.integral_eval, mul_zero]

theorem integral_scalarHiddenSign_field_sub_drift {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (D : Bool × Ω → ℝ)
    (hD : Integrable (fun u => scalarHiddenSign u.1 * D u) (scalarHiddenBrownianLaw z P)) :
    (∫ u, scalarHiddenSign u.1 * (scalarHiddenContinuousField z B T u - z - D u)
      ∂scalarHiddenBrownianLaw z P) =
      (T : ℝ) - ∫ u, scalarHiddenSign u.1 * D u ∂scalarHiddenBrownianLaw z P := by
  have he : (fun u : Bool × Ω => scalarHiddenSign u.1 *
      (scalarHiddenContinuousField z B T u - z - D u)) =
      (fun u => (T : ℝ) + scalarHiddenSign u.1 * B T u.2 - scalarHiddenSign u.1 * D u) := by
    funext u
    have hs : (scalarHiddenSign u.1) ^ 2 = 1 := by
      cases u.1 <;> norm_num [scalarHiddenSign]
    unfold scalarHiddenContinuousField
    calc
      _ = (scalarHiddenSign u.1) ^ 2 * (T : ℝ) + scalarHiddenSign u.1 * B T u.2 -
          scalarHiddenSign u.1 * D u := by ring
      _ = _ := by rw [hs, one_mul]
  rw [he]
  rw [integral_sub (f := fun u : Bool × Ω => (T : ℝ) + scalarHiddenSign u.1 * B T u.2)
    (g := fun u => scalarHiddenSign u.1 * D u)
    ((integrable_const _).add (integrable_scalarHiddenSign_brownian P z B hB T)) hD]
  rw [integral_add (f := fun _ : Bool × Ω => (T : ℝ))
    (g := fun u => scalarHiddenSign u.1 * B T u.2) (integrable_const _)
    (integrable_scalarHiddenSign_brownian P z B hB T),
    integral_scalarHiddenSign_brownian P z B hB T, integral_const]
  simp

theorem aemeasurable_scalarContinuousDrift_actual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    AEMeasurable (scalarContinuousDrift z B T) (scalarHiddenBrownianLaw z P) := by
  have h := ((aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal T).sub_const z).sub
    (aestronglyMeasurable_scalarContinuousInnovation P z B hB T).aemeasurable
  change AEMeasurable (fun u => scalarHiddenContinuousField z B T u - z -
    scalarContinuousInnovation z B T u) _ at h
  have he : (fun u => scalarHiddenContinuousField z B T u - z -
      scalarContinuousInnovation z B T u) = scalarContinuousDrift z B T := by
    funext u
    dsimp only [scalarContinuousInnovation]
    ring
  rw [he] at h
  exact h

theorem integrable_scalarHiddenSign_continuousDrift {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Integrable (fun u => scalarHiddenSign u.1 * scalarContinuousDrift z B T u)
      (scalarHiddenBrownianLaw z P) := by
  apply Integrable.of_bound
    ((((measurable_of_finite scalarHiddenSign).comp measurable_fst).aemeasurable.mul
      (aemeasurable_scalarContinuousDrift_actual P z B hB T)).aestronglyMeasurable) (T : ℝ)
  apply ae_of_all
  intro u
  change ‖scalarHiddenSign u.1 * scalarContinuousDrift z B T u‖ ≤ (T : ℝ)
  rw [norm_mul, scalarHiddenSign_norm_one, one_mul]
  exact scalarContinuousDrift_norm_le z B T u

theorem integrable_scalarHiddenSign_eulerDrift {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun u => scalarHiddenSign u.1 * scalarEulerDrift
      (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (T : ℝ) n)
      (scalarHiddenBrownianLaw z P) := by
  apply Integrable.of_bound
    ((((measurable_of_finite scalarHiddenSign).comp measurable_fst).aemeasurable.mul
      (aemeasurable_scalarEulerDrift P z B hB T n)).aestronglyMeasurable) (T : ℝ)
  apply ae_of_all
  intro u
  change ‖scalarHiddenSign u.1 * scalarEulerDrift
    (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (T : ℝ) n‖ ≤ (T : ℝ)
  rw [norm_mul, scalarHiddenSign_norm_one, one_mul]
  exact scalarEulerDrift_norm_le z B T n u

theorem scalarUniformHiddenSignInnovation_continuous_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, scalarHiddenSign u.1 * scalarEulerInnovation z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) n u ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 (∫ u, scalarHiddenSign u.1 * scalarContinuousInnovation z B T u
        ∂scalarHiddenBrownianLaw z P)) := by
  let S (n : ℕ) := scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  have hST (n : ℕ) : (S n : ℝ) ≤ (T : ℝ) := by
    dsimp only [S]
    rw [scalarUniformTime_coe]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    simpa only [mul_comm] using Nat.floor_le (show 0 ≤ ((n : ℝ) + 1) * (T : ℝ) by positivity)
  have hcont : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P,
      Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hd : Tendsto (fun n => ∫ u, scalarHiddenSign u.1 * scalarEulerDrift
      (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (S n : ℝ) n ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 (∫ u, scalarHiddenSign u.1 * scalarContinuousDrift z B T u
        ∂scalarHiddenBrownianLaw z P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (T : ℝ))
    · intro n
      exact (((measurable_of_finite scalarHiddenSign).comp measurable_fst).aemeasurable.mul
        (aemeasurable_scalarEulerDrift P z B hB.toIsPreBrownianReal (S n) n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply ae_of_all
      intro u
      rw [norm_mul, scalarHiddenSign_norm_one, one_mul]
      exact (scalarEulerDrift_norm_le z B (S n) n u).trans (hST n)
    · filter_upwards [hcont] with u hu
      have hf : Tendsto (fun n => scalarHiddenContinuousField z B (S n) u) atTop
          (𝓝 (scalarHiddenContinuousField z B T u)) :=
        (((continuous_const.add (continuous_const.mul NNReal.continuous_coe)).add hu).tendsto T).comp
          (scalarUniformTime_floor_tendsto T)
      have hi := scalarEulerInnovation_prefix_tendsto_path z B T u hu
      simp_rw [← scalarUniformTime_floor_eq] at hi
      have hdiff := (hf.sub_const z).sub hi
      have he : (fun n => scalarHiddenContinuousField z B (S n) u - z -
          scalarEulerInnovation z B (S n) n u) =
          (fun n => scalarEulerDrift (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (S n : ℝ) n) := by
        funext n
        dsimp only [scalarEulerInnovation]
        ring
      rw [he] at hdiff
      have hgoal := (tendsto_const_nhds (x := scalarHiddenSign u.1)).mul hdiff
      have hx : scalarHiddenContinuousField z B T u - z - scalarContinuousInnovation z B T u =
          scalarContinuousDrift z B T u := by
        dsimp only [scalarContinuousInnovation]
        ring
      rw [hx] at hgoal
      exact hgoal
  have hs : Tendsto (fun n => (S n : ℝ)) atTop (𝓝 (T : ℝ)) :=
    NNReal.continuous_coe.tendsto T |>.comp (scalarUniformTime_floor_tendsto T)
  have hlim := hs.sub hd
  have he (n : ℕ) : (∫ u, scalarHiddenSign u.1 * scalarEulerInnovation z B (S n) n u
      ∂scalarHiddenBrownianLaw z P) =
      (S n : ℝ) - ∫ u, scalarHiddenSign u.1 * scalarEulerDrift
        (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (S n : ℝ) n ∂scalarHiddenBrownianLaw z P := by
    exact integral_scalarHiddenSign_field_sub_drift P z B hB.toIsPreBrownianReal (S n) _
      (integrable_scalarHiddenSign_eulerDrift P z B hB.toIsPreBrownianReal (S n) n)
  have hc : (∫ u, scalarHiddenSign u.1 * scalarContinuousInnovation z B T u
      ∂scalarHiddenBrownianLaw z P) = (T : ℝ) - ∫ u, scalarHiddenSign u.1 * scalarContinuousDrift z B T u
      ∂scalarHiddenBrownianLaw z P :=
    integral_scalarHiddenSign_field_sub_drift P z B hB.toIsPreBrownianReal T _
      (integrable_scalarHiddenSign_continuousDrift P z B hB T)
  convert hlim using 1
  · funext n
    exact he n
  · exact congrArg nhds hc

theorem integral_scalarHiddenSign_continuousInnovation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    (∫ u, scalarHiddenSign u.1 * scalarContinuousInnovation z B T u
      ∂scalarHiddenBrownianLaw z P) =
      ∫ s in Icc 0 (T : ℝ), scalarHiddenExpectedDefectReal P z B s := by
  exact tendsto_nhds_unique
    (scalarUniformHiddenSignInnovation_continuous_moment_tendsto P z B hB T)
    (scalarUniformHiddenSignInnovation_moment_tendsto P z B hB T)

theorem integrable_scalarHiddenSign_continuousInnovation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Integrable (fun u => scalarHiddenSign u.1 * scalarContinuousInnovation z B T u)
      (scalarHiddenBrownianLaw z P) := by
  have hi := (memLp_scalarContinuousInnovation P z B hB T).integrable (by norm_num)
  exact hi.bdd_mul
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).aestronglyMeasurable)
    (ae_of_all _ (fun u => (scalarHiddenSign_norm_one u.1).le))

theorem integral_scalarHiddenSign_continuousInnovation_sub {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (S T : ℝ≥0) :
    (∫ u, scalarHiddenSign u.1 * (scalarContinuousInnovation z B T u -
      scalarContinuousInnovation z B S u) ∂scalarHiddenBrownianLaw z P) =
      ∫ s in (S : ℝ)..(T : ℝ), scalarHiddenExpectedDefectReal P z B s := by
  have he : (fun u => scalarHiddenSign u.1 * (scalarContinuousInnovation z B T u -
      scalarContinuousInnovation z B S u)) =
      (fun u => scalarHiddenSign u.1 * scalarContinuousInnovation z B T u -
        scalarHiddenSign u.1 * scalarContinuousInnovation z B S u) := by
    funext u
    ring
  rw [he, integral_sub
    (integrable_scalarHiddenSign_continuousInnovation P z B hB T)
    (integrable_scalarHiddenSign_continuousInnovation P z B hB S),
    integral_scalarHiddenSign_continuousInnovation P z B hB T,
    integral_scalarHiddenSign_continuousInnovation P z B hB S,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le T.coe_nonneg,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le S.coe_nonneg]
  have hc := continuous_scalarHiddenExpectedDefectReal P z B hB
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 (S : ℝ))
    (hc.intervalIntegrable (μ := volume) (S : ℝ) (T : ℝ))
  linarith

theorem integral_scalarHiddenSign_normalizedInnovation_sub {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (S T : ℝ≥0) :
    (∫ u, scalarHiddenSign u.1 * ((scalarContinuousInnovation z B T u -
      scalarContinuousInnovation z B S u) / Real.sqrt ((T : ℝ) - (S : ℝ)))
      ∂scalarHiddenBrownianLaw z P) =
      (∫ s in (S : ℝ)..(T : ℝ), scalarHiddenExpectedDefectReal P z B s) /
        Real.sqrt ((T : ℝ) - (S : ℝ)) := by
  simp_rw [← mul_div_assoc]
  rw [integral_div, integral_scalarHiddenSign_continuousInnovation_sub P z B hB S T]

theorem scalarNormalizedInnovation_sub_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (S T : ℝ≥0) (hST : S < T) :
    HasLaw (fun u => (scalarContinuousInnovation z B T u - scalarContinuousInnovation z B S u) /
      Real.sqrt ((T : ℝ) - (S : ℝ))) (gaussianReal 0 1) (scalarHiddenBrownianLaw z P) := by
  have hd : 0 < (T : ℝ) - (S : ℝ) := sub_pos.mpr (by exact_mod_cast hST)
  have hv : (nndist (T : ℝ) (S : ℝ) : ℝ) = (T : ℝ) - (S : ℝ) := by
    change |(T : ℝ) - (S : ℝ)| = (T : ℝ) - (S : ℝ)
    exact abs_of_pos hd
  have hnormal : (nndist (T : ℝ) (S : ℝ) /
      NNReal.mk ((Real.sqrt ((T : ℝ) - (S : ℝ))) ^ 2) (sq_nonneg _) : ℝ≥0) = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one, hv, Real.sq_sqrt hd.le]
    exact div_self hd.ne'
  have hi := (scalarContinuousInnovation_isBrownianReal P z B hB).toIsPreBrownianReal.hasLaw_sub T S
  have hh := gaussianReal_div_const hi (Real.sqrt ((T : ℝ) - (S : ℝ)))
  refine ⟨hi.aemeasurable.div_const _, ?_⟩
  calc
    _ = gaussianReal ((0 : ℝ) / Real.sqrt ((T : ℝ) - (S : ℝ)))
        (nndist (T : ℝ) (S : ℝ) /
          NNReal.mk ((Real.sqrt ((T : ℝ) - (S : ℝ))) ^ 2) (sq_nonneg _)) := hh.map_eq
    _ = gaussianReal 0 1 := congrArg₂ gaussianReal (zero_div _) hnormal

theorem scalarGaussianSign_pair_law_and_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (S T : ℝ≥0) (hST : S < T) :
    HasLaw (fun u => (scalarContinuousInnovation z B T u - scalarContinuousInnovation z B S u) /
      Real.sqrt ((T : ℝ) - (S : ℝ))) (gaussianReal 0 1) (scalarHiddenBrownianLaw z P) ∧
    (∫ u, scalarHiddenSign u.1 * ((scalarContinuousInnovation z B T u -
      scalarContinuousInnovation z B S u) / Real.sqrt ((T : ℝ) - (S : ℝ)))
      ∂scalarHiddenBrownianLaw z P) =
      (∫ s in (S : ℝ)..(T : ℝ), scalarHiddenExpectedDefectReal P z B s) /
        Real.sqrt ((T : ℝ) - (S : ℝ)) :=
  ⟨scalarNormalizedInnovation_sub_hasLaw P z B hB S T hST,
    integral_scalarHiddenSign_normalizedInnovation_sub P z B hB S T⟩

end SKConstants

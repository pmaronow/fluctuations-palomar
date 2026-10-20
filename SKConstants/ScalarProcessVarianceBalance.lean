module
public import SKConstants.ScalarProcessPosteriorItoLimit
public import SKConstants.ScalarObservationPredictableSums
public import SKConstants.ScalarProcessOneTimeLaw
public import SKConstants.ScalarProcessSignInnovationLimit
public import SKConstants.GaussianIntegralCompletion
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

def scalarHiddenExpectedDefectSqReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ u, scalarDefect (scalarHiddenFieldReal z B s u) ^ 2 ∂scalarHiddenBrownianLaw z P

lemma norm_scalarDefect_sq_le_one (y : ℝ) : ‖scalarDefect y ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_scalarDefect_le_one y) 2

lemma scalarHiddenExpectedDefectSqReal_norm_le_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (s : ℝ) :
    ‖scalarHiddenExpectedDefectSqReal P z B s‖ ≤ 1 := by
  simpa only [scalarHiddenExpectedDefectSqReal, probReal_univ, one_mul] using
    norm_integral_le_of_norm_le_const (ae_of_all (scalarHiddenBrownianLaw z P)
      (fun u => norm_scalarDefect_sq_le_one (scalarHiddenFieldReal z B s u)))

lemma continuous_scalarHiddenExpectedDefectSqReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) : Continuous (scalarHiddenExpectedDefectSqReal P z B) := by
  apply continuous_iff_continuousAt.2
  intro s
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun s => ((measurable_scalarDefect.comp_aemeasurable
      (aemeasurable_scalarHiddenFieldReal P z B hB.toIsPreBrownianReal s)).pow_const 2).aestronglyMeasurable))
    (Eventually.of_forall (fun _ => ae_of_all _ (fun u => norm_scalarDefect_sq_le_one _)))
    (integrable_const 1)
    (hc.mono (fun u hu =>
      ((continuous_scalarDefect_actual.comp (continuous_scalarHiddenFieldReal z B u hu)).pow 2).tendsto s))

lemma scalarHiddenExpectedDefectSqReal_grid {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (n k : ℕ) :
    scalarHiddenExpectedDefectSqReal P z B ((k : ℝ) / ((n : ℝ) + 1)) =
      ∫ u, scalarDefect (scalarHiddenContinuousField z B (scalarUniformTime n k) u) ^ 2
        ∂scalarHiddenBrownianLaw z P := by
  rw [← scalarUniformTime_coe n k]
  unfold scalarHiddenExpectedDefectSqReal
  congr 1
  funext u
  simp only [scalarHiddenFieldReal, scalarHiddenContinuousField, Real.toNNReal_coe]

lemma integral_sq_tendsto_of_meanSquare {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hY : MemLp Y 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω ^ 2 ∂P) atTop (𝓝 (∫ ω, Y ω ^ 2 ∂P)) := by
  have he (n : ℕ) : ‖(hX n).toLp (X n) - hY.toLp Y‖ =
      Real.sqrt (∫ ω, (X n ω - Y ω) ^ 2 ∂P) := by
    rw [← norm_toLp_difference_sq_eq_integral (hX n) hY, Real.sqrt_sq (norm_nonneg _)]
  have hlp : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hY.toLp Y)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp_rw [he]
    simpa only [Real.sqrt_zero] using hlim.sqrt
  have hn (f : Ω → ℝ) (hf : MemLp f 2 P) : ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ω hω
    rw [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hh := hlp.norm.pow 2
  simpa only [hn] using hh

lemma scalarWeightedBrownianMeshSum_defect_secondMoment_tendsto {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, scalarWeightedBrownianMeshSum scalarDefect z B n
      ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u ^ 2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 (∫ s in Icc 0 (T : ℝ), scalarHiddenExpectedDefectSqReal P z B s)) := by
  let f := scalarHiddenExpectedDefectSqReal P z B
  have hb : ∀ s, ‖f s‖ ≤ 1 := scalarHiddenExpectedDefectSqReal_norm_le_one P z B
  have hfull := scalarEulerDrift_tendsto f (T : ℝ)
    (continuous_scalarHiddenExpectedDefectSqReal P z B hB) hb
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
  have he (n : ℕ) : (∫ u, scalarWeightedBrownianMeshSum scalarDefect z B n
      ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u ^ 2 ∂scalarHiddenBrownianLaw z P) =
      scalarEulerDrift f (T : ℝ) n -
        (((T : ℝ) - (⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) / ((n : ℝ) + 1)) *
          f ((⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) / ((n : ℝ) + 1))) := by
    rw [(scalarWeightedBrownianMeshSum_defect_L2_isometry P z B hB n _).2,
      Fin.sum_univ_eq_sum_range (fun k : ℕ => (1 / ((n : ℝ) + 1)) *
        ∫ u, scalarDefect (scalarHiddenContinuousField z B (scalarUniformTime n k) u) ^ 2
          ∂scalarHiddenBrownianLaw z P),
      scalarEulerDrift_eq_finite_sum f (T : ℝ) T.coe_nonneg n hb, add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f]
    rw [scalarHiddenExpectedDefectSqReal_grid]
  simp_rw [he]
  simpa only [sub_zero] using hsum

lemma memLp_scalarHiddenPosteriorIncrement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    MemLp (fun u => Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z) 2
      (scalarHiddenBrownianLaw z P) := by
  apply MemLp.of_bound ((measurable_scalarTanh.comp_aemeasurable
    (aemeasurable_scalarHiddenContinuousField P z B hB T)).sub_const _).aestronglyMeasurable 2
  apply ae_of_all
  intro u
  have h1 := norm_tanh_le_one (scalarHiddenContinuousField z B T u)
  have h2 := norm_tanh_le_one z
  exact (norm_sub_le _ _).trans (by dsimp only [Function.comp_apply]; linarith)

lemma integral_scalarHiddenPosteriorIncrement_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    (∫ u, (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z) ^ 2
      ∂scalarHiddenBrownianLaw z P) = scalarDefect z -
      ∫ u, scalarDefect (scalarHiddenContinuousField z B T u) ∂scalarHiddenBrownianLaw z P := by
  let μ := scalarHiddenBrownianLaw z P
  let g := fun u => Real.tanh (scalarHiddenContinuousField z B T u)
  let a := fun u => scalarDefect (scalarHiddenContinuousField z B T u)
  have hg : Integrable g μ := Integrable.of_bound
    (measurable_scalarTanh.comp_aemeasurable
      (aemeasurable_scalarHiddenContinuousField P z B hB T)).aestronglyMeasurable 1
    (ae_of_all _ (fun u => norm_tanh_le_one _))
  have ha : Integrable a μ := Integrable.of_bound
    (measurable_scalarDefect.comp_aemeasurable
      (aemeasurable_scalarHiddenContinuousField P z B hB T)).aestronglyMeasurable 1
    (ae_of_all _ (fun u => norm_scalarDefect_le_one _))
  have hmean : (∫ u, g u ∂μ) = Real.tanh z := by
    exact (integral_scalarHiddenContinuousField_comp hB z T Real.tanh measurable_scalarTanh).trans
      (integral_tanh_scalarTransitionKernel z T)
  have hpoint (u : Bool × Ω) : (g u - Real.tanh z) ^ 2 =
      (1 - a u) - (2 * Real.tanh z) * g u + (Real.tanh z) ^ 2 := by
    dsimp only [g, a, scalarDefect]
    ring
  change (∫ u, (g u - Real.tanh z) ^ 2 ∂μ) = scalarDefect z - ∫ u, a u ∂μ
  simp_rw [hpoint]
  have hadd := integral_add (((integrable_const 1).sub ha).sub (hg.const_mul (2 * Real.tanh z)))
    (integrable_const ((Real.tanh z) ^ 2))
  have hsub := integral_sub ((integrable_const 1).sub ha) (hg.const_mul (2 * Real.tanh z))
  have hsub2 := integral_sub (integrable_const 1) ha
  simp only [Pi.sub_apply] at hadd hsub hsub2
  rw [hadd, hsub, hsub2, integral_const_mul, hmean]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, scalarDefect]
  ring

lemma integral_scalarHiddenContinuousField_defect_variance_balance {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (T : ℝ≥0) :
    (∫ u, scalarDefect (scalarHiddenContinuousField z B T u) ∂scalarHiddenBrownianLaw z P) =
      scalarDefect z - ∫ s in Icc 0 (T : ℝ), scalarHiddenExpectedDefectSqReal P z B s := by
  let X := fun n u => scalarWeightedBrownianMeshSum scalarDefect z B n
    ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u
  let Y := fun u => Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z
  have hX (n : ℕ) : MemLp (X n) 2 (scalarHiddenBrownianLaw z P) := by
    apply (memLp_two_iff_integrable_sq (aemeasurable_scalarWeightedBrownianMeshSum P
      scalarDefect measurable_scalarDefect z B hB n _).aestronglyMeasurable).2
    exact (scalarWeightedBrownianMeshSum_defect_L2_isometry P z B hB n _).1
  have hY : MemLp Y 2 (scalarHiddenBrownianLaw z P) :=
    memLp_scalarHiddenPosteriorIncrement P z B hB.toIsPreBrownianReal T
  have hlimit := integral_sq_tendsto_of_meanSquare hX hY
    (scalarWeightedBrownianMeshSum_posterior_tendsto_L2 P z B hB T)
  have hisometry := scalarWeightedBrownianMeshSum_defect_secondMoment_tendsto P z B hB T
  have he := tendsto_nhds_unique hlimit hisometry
  change (∫ u, (Real.tanh (scalarHiddenContinuousField z B T u) - Real.tanh z) ^ 2
      ∂scalarHiddenBrownianLaw z P) = _ at he
  rw [integral_scalarHiddenPosteriorIncrement_sq P z B hB.toIsPreBrownianReal T] at he
  linarith

lemma scalarHiddenExpectedDefectReal_variance_balance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    scalarHiddenExpectedDefectReal P z B (T : ℝ) =
      scalarDefect z - ∫ s in Icc 0 (T : ℝ), scalarHiddenExpectedDefectSqReal P z B s := by
  simpa only [scalarHiddenExpectedDefectReal, scalarHiddenFieldReal,
    scalarHiddenContinuousField, Real.toNNReal_coe] using
    integral_scalarHiddenContinuousField_defect_variance_balance P z B hB T

lemma scalarHiddenExpectedDefectReal_variance_balance_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ) (hT : 0 ≤ T) :
    scalarHiddenExpectedDefectReal P z B T =
      scalarDefect z - ∫ s in (0 : ℝ)..T, scalarHiddenExpectedDefectSqReal P z B s := by
  have he := scalarHiddenExpectedDefectReal_variance_balance P z B hB T.toNNReal
  simp only [Real.toNNReal_of_nonneg hT, NNReal.coe_mk] at he
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT] at he
  exact he

lemma hasDerivAt_scalarHiddenExpectedDefectReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ) (hT : 0 < T) :
    HasDerivAt (scalarHiddenExpectedDefectReal P z B)
      (-scalarHiddenExpectedDefectSqReal P z B T) T := by
  have hc := continuous_scalarHiddenExpectedDefectSqReal P z B hB
  have hder := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 T)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h := (hasDerivAt_const T (scalarDefect z)).sub hder
  simp only [zero_sub] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hT] with s hs
  simpa only [Pi.sub_apply] using
    scalarHiddenExpectedDefectReal_variance_balance_real P z B hB s hs.le

lemma scalarP_actual_variance_balance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) (hT : T ≠ 0) :
    scalarP z T = scalarDefect z -
      ∫ s in Icc 0 (T : ℝ), scalarHiddenExpectedDefectSqReal P z B s := by
  have he := integral_scalarHiddenContinuousField_defect_variance_balance P z B hB T
  rw [integral_scalarHiddenContinuousField_defect hB.toIsPreBrownianReal z T,
    ite_eq_right hT] at he
  exact he

lemma scalarHiddenExpectedDefectReal_eq_scalarP {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ) (hT : 0 < T) :
    scalarHiddenExpectedDefectReal P z B T = scalarP z T.toNNReal := by
  have hne : T.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hT)
  have he := integral_scalarHiddenContinuousField_defect hB z T.toNNReal
  rw [ite_eq_right hne] at he
  simpa only [scalarHiddenExpectedDefectReal, scalarHiddenContinuousField,
    scalarHiddenFieldReal, Real.coe_toNNReal T hT.le] using he

lemma scalarHiddenExpectedDefectSqReal_eq_scalarR {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ) (hT : 0 < T) :
    scalarHiddenExpectedDefectSqReal P z B T = scalarR z T.toNNReal := by
  have hne : T.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hT)
  have he := integral_scalarHiddenContinuousField_defect_sq hB z T.toNNReal
  rw [ite_eq_right hne] at he
  simpa only [scalarHiddenExpectedDefectSqReal, scalarHiddenContinuousField,
    scalarHiddenFieldReal, Real.coe_toNNReal T hT.le] using he

lemma hasDerivAt_scalarP_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ) (hT : 0 < T) :
    HasDerivAt (fun s : ℝ => scalarP z s.toNNReal) (-scalarR z T.toNNReal) T := by
  have hd := hasDerivAt_scalarHiddenExpectedDefectReal P z B hB T hT
  rw [scalarHiddenExpectedDefectSqReal_eq_scalarR P z B hB.toIsPreBrownianReal T hT] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hT] with s hs
  exact (scalarHiddenExpectedDefectReal_eq_scalarP P z B hB.toIsPreBrownianReal s hs).symm

lemma scalarHiddenExpectedDefectReal_interval_balance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (S T : ℝ≥0) :
    scalarHiddenExpectedDefectReal P z B (S : ℝ) -
      scalarHiddenExpectedDefectReal P z B (T : ℝ) =
        ∫ s in (S : ℝ)..(T : ℝ), scalarHiddenExpectedDefectSqReal P z B s := by
  have hS := scalarHiddenExpectedDefectReal_variance_balance_real P z B hB (S : ℝ) S.coe_nonneg
  have hT := scalarHiddenExpectedDefectReal_variance_balance_real P z B hB (T : ℝ) T.coe_nonneg
  have hc := continuous_scalarHiddenExpectedDefectSqReal P z B hB
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (S : ℝ)) (hc.intervalIntegrable (S : ℝ) (T : ℝ))
  linarith

lemma integral_scalarHiddenContinuousField_defect_interval_balance {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (S T : ℝ≥0) :
    (∫ u, scalarDefect (scalarHiddenContinuousField z B S u) ∂scalarHiddenBrownianLaw z P) -
      (∫ u, scalarDefect (scalarHiddenContinuousField z B T u) ∂scalarHiddenBrownianLaw z P) =
        ∫ s in (S : ℝ)..(T : ℝ), scalarHiddenExpectedDefectSqReal P z B s := by
  simpa only [scalarHiddenExpectedDefectReal, scalarHiddenFieldReal,
    scalarHiddenContinuousField, Real.toNNReal_coe] using
    scalarHiddenExpectedDefectReal_interval_balance P z B hB S T

lemma scalarP_actual_interval_balance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (S T : ℝ≥0) (hS : S ≠ 0) (hT : T ≠ 0) :
    scalarP z S - scalarP z T =
      ∫ s in (S : ℝ)..(T : ℝ), scalarHiddenExpectedDefectSqReal P z B s := by
  have he := integral_scalarHiddenContinuousField_defect_interval_balance P z B hB S T
  rw [integral_scalarHiddenContinuousField_defect hB.toIsPreBrownianReal z S,
    integral_scalarHiddenContinuousField_defect hB.toIsPreBrownianReal z T,
    ite_eq_right hS, ite_eq_right hT] at he
  exact he

end SKConstants

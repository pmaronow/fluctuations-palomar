module

public import SKConstants.ScalarProcessMixedRow
public import SKConstants.ScalarProcessInnovationFiltration
public import Mathlib.Probability.Independence.Integration

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

private theorem integral_linearForm_mul_of_secondMoment
    (μ : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin d))
    (hLp : ∀ a, MemLp (fun u => ⟪X u,a⟫_ℝ) 2 μ)
    (hE : ∀ a, (∫ u, ⟪X u,a⟫_ℝ^2 ∂μ) = ‖a‖^2)
    (a b : EuclideanSpace ℝ (Fin d)) :
    (∫ u, ⟪X u,a⟫_ℝ*⟪X u,b⟫_ℝ ∂μ) = ⟪a,b⟫_ℝ := by
  have hA := (hLp a).integrable_sq
  have hB := (hLp b).integrable_sq
  have hAB := (hLp a).integrable_mul (hLp b)
  have hp : (fun u => ⟪X u,a+b⟫_ℝ^2) =
      fun u => ⟪X u,a⟫_ℝ^2 + 2*(⟪X u,a⟫_ℝ*⟪X u,b⟫_ℝ) + ⟪X u,b⟫_ℝ^2 := by
    ext u
    rw [inner_add_right]
    ring
  have he := hE (a+b)
  rw [hp] at he
  have hsum := integral_add (hA.add (hAB.const_mul 2)) hB
  have hsum2 := integral_add hA (hAB.const_mul 2)
  simp only [Pi.add_apply, Pi.mul_apply] at hsum hsum2
  rw [hsum, hsum2, integral_const_mul, hE a, hE b, norm_add_sq_real] at he
  linarith

theorem scalarActualNormalizedPosteriorRow_bilinearMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V)
    (a b : EuclideanSpace ℝ (Fin d)) :
    (∫ u, ⟪scalarNormalizedPosteriorRow z B t
        (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,a⟫_ℝ *
      ⟪scalarNormalizedPosteriorRow z B t
        (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) u,b⟫_ℝ
      ∂scalarHiddenBrownianLaw z P) = ⟪a,b⟫_ℝ := by
  exact integral_linearForm_mul_of_secondMoment _ _
    (fun a => (scalarNormalizedPosteriorRow_linearForm_hasSubgaussianMGF P z B hB t ht.monotone
      (fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))) a).memLp 2)
    (scalarActualNormalizedPosteriorRow_secondMoment P z B hB R hR hz t ht V ht1 htV) a b

theorem scalarNormalizedInnovationRow_bilinearMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q)
    (a b : EuclideanSpace ℝ (Fin d)) :
    (∫ u, ⟪scalarNormalizedInnovationRow z B q u,a⟫_ℝ *
      ⟪scalarNormalizedInnovationRow z B q u,b⟫_ℝ ∂scalarHiddenBrownianLaw z P) = ⟪a,b⟫_ℝ := by
  exact integral_linearForm_mul_of_secondMoment _ _
    (fun a => (scalarNormalizedInnovationRow_linearForm_hasSubgaussianMGF P z B hB q hq a).memLp 2)
    (scalarNormalizedInnovationRow_linearForm_secondMoment P z B hB q hq) a b

theorem scalarActualNormalizedPosteriorRow_coordinateMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V) (i j : Fin d) :
    (∫ u, scalarNormalizedPosteriorRow z B t
        (fun k => scalarPosteriorIntervalScale z (t k) (t (k+1))) u i *
      scalarNormalizedPosteriorRow z B t
        (fun k => scalarPosteriorIntervalScale z (t k) (t (k+1))) u j
      ∂scalarHiddenBrownianLaw z P) = if i=j then 1 else 0 := by
  simpa only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul, PiLp.single_apply, eq_comm] using
    scalarActualNormalizedPosteriorRow_bilinearMoment P z B hB R hR hz t ht V ht1 htV
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

theorem scalarNormalizedInnovationRow_coordinateMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (q : ℕ → ℝ≥0) (hq : StrictMono q) (i j : Fin d) :
    (∫ u, scalarNormalizedInnovationRow z B q u i * scalarNormalizedInnovationRow z B q u j
      ∂scalarHiddenBrownianLaw z P) = if i=j then 1 else 0 := by
  simpa only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul, PiLp.single_apply, eq_comm] using
    scalarNormalizedInnovationRow_bilinearMoment P z B hB q hq
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

theorem scalarNormalizedInnovationRow_hiddenSign_moment
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (q : ℕ → ℝ≥0) (i : Fin d) :
    (∫ u, scalarHiddenSign u.1 * scalarNormalizedInnovationRow z B q u i
      ∂scalarHiddenBrownianLaw z P) =
      (∫ v in (q i : ℝ)..(q (i+1) : ℝ), scalarHiddenExpectedDefectReal P z B v) /
        Real.sqrt ((q (i+1) : ℝ)-(q i : ℝ)) := by
  have he : (fun u => scalarHiddenSign u.1 * scalarNormalizedInnovationRow z B q u i) =
      fun u => (scalarHiddenSign u.1 * (scalarContinuousInnovation z B (q (i+1)) u -
        scalarContinuousInnovation z B (q i) u)) / Real.sqrt ((q (i+1) : ℝ)-(q i : ℝ)) := by
    ext u
    simp only [scalarNormalizedInnovationRow, WithLp.ofLp_toLp]
    ring
  rw [he, integral_div, integral_scalarHiddenSign_continuousInnovation_sub P z B hB]

theorem integral_scalarHiddenSign_tanhField
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    (∫ u, scalarHiddenSign u.1 * Real.tanh (scalarHiddenContinuousField z B T u)
      ∂scalarHiddenBrownianLaw z P) =
    ∫ u, (Real.tanh (scalarHiddenContinuousField z B T u))^2 ∂scalarHiddenBrownianLaw z P := by
  let t : ℕ → ℝ≥0 := fun k => (k : ℝ≥0)*T
  have ht : Monotone t := fun _ _ hij =>
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)
  have ht0 : t 0 = 0 := by simp [t]
  let f : ScalarObservationHistory 1 → ℝ := fun H => Real.tanh (scalarLastField z 1 H)
  have hf : Measurable f := measurable_scalarTanh.comp (measurable_scalarLastField z 1)
  have hi : Integrable f (scalarObservationHistoryLaw z (brownianMeshVariance t) 1) :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ (fun _ => norm_tanh_le_one _))
  have hJoint := scalarBrownianPriorField_jointHistory_hasLaw hB z t ht ht0 1
  have hObs := scalarBrownianPriorField_history_hasLaw hB z t ht ht0 1
  have hJointInt := hJoint.integral_comp
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul (hf.comp measurable_snd)).aestronglyMeasurable
  have hObsInt := hObs.integral_comp (hf.mul hf).aestronglyMeasurable
  have hFilter := integral_scalarHiddenJoint_sign_mul z (brownianMeshVariance t) 1 f hi
  calc
    _ = ∫ u, scalarHiddenSign u.1*f u.2 ∂scalarHiddenJointHistoryLaw z (brownianMeshVariance t) 1 := by
      simpa only [f, scalarSampledFieldHistory, scalarLastField, t, Nat.zero_add,
        Nat.cast_one, one_mul, Function.comp_def, Pi.mul_apply, scalarHiddenContinuousField,
        scalarHiddenBrownianLaw, scalarHiddenPriorBool] using hJointInt
    _ = _ := hFilter
    _ = _ := by
      simpa only [f, scalarSampledFieldHistory, scalarLastField, t, Nat.zero_add,
        Nat.cast_one, one_mul, Function.comp_def, Pi.mul_apply, scalarHiddenContinuousField,
        scalarHiddenBrownianLaw, scalarHiddenPriorBool, pow_two] using hObsInt.symm

theorem scalarActualNormalizedPosteriorRow_hiddenSign_moment
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V) (i : Fin d) :
    (∫ u, scalarHiddenSign u.1 * scalarNormalizedPosteriorRow z B t
        (fun k => scalarPosteriorIntervalScale z (t k) (t (k+1))) u i
      ∂scalarHiddenBrownianLaw z P) = (scalarPosteriorIntervalScale z (t i) (t (i+1)) : ℝ) := by
  let s := scalarPosteriorIntervalScale z (t i) (t (i+1))
  let m : ℝ≥0 → Bool × Ω → ℝ := fun T u => Real.tanh (scalarHiddenContinuousField z B T u)
  have hSi : 1 ≤ (t i : ℝ) := ht1.trans (NNReal.coe_le_coe.mpr (ht.monotone (Nat.zero_le _)))
  have hTi : t (i+1) ≤ V := (ht.monotone (by omega)).trans htV
  have hs : 0 < s := scalarPosteriorIntervalScale_pos P z B hB R hR hz
    (t i) (t (i+1)) V hSi (ht (Nat.lt_succ_self _)) hTi
  have hi0 : t i ≠ 0 := by intro he; simp only [he, NNReal.coe_zero] at hSi; linarith
  have hi1 : t (i+1) ≠ 0 := (ne_of_gt ((NNReal.coe_pos.mp (by linarith : 0 < (t i : ℝ))).trans
    (ht (Nat.lt_succ_self _))))
  have hMint (T : ℝ≥0) : Integrable (fun u => scalarHiddenSign u.1*m T u) (scalarHiddenBrownianLaw z P) := by
    have hmeas := ((measurable_of_finite scalarHiddenSign).comp measurable_fst).aemeasurable.mul
      (measurable_scalarTanh.comp_aemeasurable (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal T))
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    exact ae_of_all _ (fun u => by
      change ‖scalarHiddenSign u.1 * Real.tanh (scalarHiddenContinuousField z B T u)‖ ≤ 1
      rw [norm_mul, scalarHiddenSign_norm_one, one_mul]
      exact norm_tanh_le_one _)
  have hE (T : ℝ≥0) (hT : T ≠ 0) :
      (∫ u, scalarHiddenSign u.1*m T u ∂scalarHiddenBrownianLaw z P) = 1-scalarP z T := by
    rw [integral_scalarHiddenSign_tanhField P z B hB.toIsPreBrownianReal]
    have hi : Integrable (fun u => scalarDefect (scalarHiddenContinuousField z B T u))
        (scalarHiddenBrownianLaw z P) := Integrable.of_bound
      (measurable_scalarDefect.comp_aemeasurable (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal T)).aestronglyMeasurable
      1 (ae_of_all _ (fun _ => norm_scalarDefect_le_one _))
    have hpoint : (fun u => (m T u)^2) = fun u => 1-scalarDefect (scalarHiddenContinuousField z B T u) := by
      ext u; dsimp [m,scalarDefect]; ring
    rw [hpoint, integral_sub (integrable_const _) hi, integral_const,
      integral_scalarHiddenContinuousField_defect hB.toIsPreBrownianReal z T]
    simp only [hT, ite_false, probReal_univ, smul_eq_mul, one_mul]
  have hs2 : (s : ℝ)^2 = scalarP z (t i)-scalarP z (t (i+1)) := by
    dsimp [s,scalarPosteriorIntervalScale] at hs ⊢
    have hd : 0 < scalarP z (t i)-scalarP z (t (i+1)) := by
      simpa only [NNReal.sqrt_pos, Real.toNNReal_pos] using hs
    rw [← NNReal.coe_pow, NNReal.sq_sqrt, Real.coe_toNNReal _ hd.le]
  have he : (fun u => scalarHiddenSign u.1*scalarNormalizedPosteriorRow z B t
      (fun k => scalarPosteriorIntervalScale z (t k) (t (k+1))) u i) =
      fun u => (scalarHiddenSign u.1*m (t (i+1)) u-scalarHiddenSign u.1*m (t i) u)/(s : ℝ) := by
    ext u
    simp only [scalarNormalizedPosteriorRow, scalarContinuousPosteriorIncrement, WithLp.ofLp_toLp]
    dsimp [s,m]
    ring
  rw [he, integral_div, integral_sub (hMint _) (hMint _), hE _ hi1, hE _ hi0]
  change (1-scalarP z (t (i+1))-(1-scalarP z (t i)))/(s : ℝ) = (s : ℝ)
  rw [show 1-scalarP z (t (i+1))-(1-scalarP z (t i)) = (s : ℝ)^2 by rw [hs2]; ring]
  field_simp [(NNReal.coe_pos.mpr hs).ne']

theorem scalarNormalizedPosteriorInnovationRow_indepFun
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t q : ℕ → ℝ≥0) (s : Fin d → ℝ≥0)
    (hq : Monotone q) (i j : Fin d) (hi : t i ≤ q j) (hi1 : t (i+1) ≤ q j) :
    IndepFun (fun u => scalarNormalizedInnovationRow z B q u j)
      (fun u => scalarNormalizedPosteriorRow z B t s u i) (scalarHiddenBrownianLaw z P) := by
  have h := scalarContinuousInnovation_indepFun_shift_observationPast P (q j) z B hB
  let φ : (ℝ≥0 → ℝ) → ℝ := fun f => f (q (j+1)-q j) /
    Real.sqrt ((q (j+1) : ℝ)-(q j : ℝ))
  let ψ : (Set.Iic (q j) → ℝ) → ℝ := fun y =>
    (Real.tanh (y ⟨t (i+1),hi1⟩)-Real.tanh (y ⟨t i,hi⟩)) / (s i : ℝ)
  have hφ : Measurable φ := (measurable_pi_apply _).div_const _
  have hψ : Measurable ψ := ((measurable_scalarTanh.comp (measurable_pi_apply _)).sub
    (measurable_scalarTanh.comp (measurable_pi_apply _))).div_const _
  have hx := h.comp hφ hψ
  have he : q j+(q (j+1)-q j) = q (j+1) :=
    add_tsub_cancel_of_le (hq (by omega))
  convert hx using 1 <;> ext u <;>
    simp only [φ, ψ, Function.comp_def, scalarNormalizedInnovationRow,
      scalarNormalizedPosteriorRow, WithLp.ofLp_toLp, scalarContinuousPosteriorIncrement, he]

theorem scalarNormalizedPosteriorInnovationRow_crossMoment_eq_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t q : ℕ → ℝ≥0) (s : Fin d → ℝ≥0)
    (hq : StrictMono q) (i j : Fin d) (hi : t i ≤ q j) (hi1 : t (i+1) ≤ q j) :
    (∫ u, scalarNormalizedPosteriorRow z B t s u i * scalarNormalizedInnovationRow z B q u j
      ∂scalarHiddenBrownianLaw z P) = 0 := by
  have hl := scalarNormalizedInnovationRow_coordinate_hasLaw P z B hB q hq j
  have hG := hl.aemeasurable.aestronglyMeasurable
  have hT : AEStronglyMeasurable (fun u => scalarNormalizedPosteriorRow z B t s u i)
      (scalarHiddenBrownianLaw z P) := by
    simpa only [scalarNormalizedPosteriorRow, WithLp.ofLp_toLp, scalarContinuousPosteriorIncrement,
      Pi.sub_apply, Function.comp_def] using ((measurable_scalarTanh.comp_aemeasurable
      (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal (t (i+1)))).sub
      (measurable_scalarTanh.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal (t i)))).div_const _ |>.aestronglyMeasurable
  have hm : (∫ u, scalarNormalizedInnovationRow z B q u j ∂scalarHiddenBrownianLaw z P) = 0 := by
    rw [hl.integral_eq, integral_id_gaussianReal]
  have hx := (scalarNormalizedPosteriorInnovationRow_indepFun P z B hB t q s hq.monotone i j hi hi1).symm
  rw [hx.integral_fun_mul_eq_mul_integral hT hG, hm, mul_zero]

end SKConstants

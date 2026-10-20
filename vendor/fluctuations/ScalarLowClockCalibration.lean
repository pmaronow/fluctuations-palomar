module

public import SKFluctuationsOAI.Probability.SKFluctuations.ScalarFlattenedContinuity

@[expose] public section

noncomputable section
set_option maxHeartbeats 800000
namespace OAI.SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

private def positiveProfile (α : boundedMassProfiles) (n : ℕ) : boundedMassProfiles :=
  ⟨fun s => max (α.val s) (1 / (n + 2 : ℝ)), by
    constructor
    · intro s
      exact ⟨(α.property.1 s).1.trans (le_max_left _ _),
        max_le (α.property.1 s).2 (by
          apply (div_le_one₀ (by positivity : (0 : ℝ) < n + 2)).mpr
          linarith [Nat.cast_nonneg (α := ℝ) n])⟩
    · exact α.property.2.max monotone_const⟩

private theorem positiveProfile_pos (α : boundedMassProfiles) (n : ℕ) (s : ℝ) :
    0 < (positiveProfile α n).val s :=
  (by positivity : (0 : ℝ) < 1 / (n + 2 : ℝ)).trans_le (le_max_right _ _)

private theorem positiveProfile_tendsto (α : boundedMassProfiles) :
    Tendsto (positiveProfile α) atTop (𝓝 α) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro s
  have ht : Tendsto (fun n : ℕ => 1 / (n + 2 : ℝ)) atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1 <;> simp [Function.comp_def, Nat.cast_add]
  simpa only [positiveProfile, max_eq_left (α.property.1 s).1] using
    ((tendsto_const_nhds (x := α.val s)).max ht)

private theorem positiveProfile_right_continuous (α : boundedMassProfiles)
    {q : ℝ} (hc : ContinuousWithinAt α.val (Ici q) q) (n : ℕ) :
    ContinuousWithinAt (positiveProfile α n).val (Ici q) q :=
  hc.max continuousWithinAt_const

theorem scalarPlantedEnergy_integral_nonnegative {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : ∀ x ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    scalarPlantedEnergy hT α q - scalarPlantedEnergy hT α 0 =
      T * ∫ x in 0..q, scalarPlantedCurvature hT α x := by
  obtain rfl | hq := hq.eq_or_lt
  · simp
  have ht := positiveProfile_tendsto α
  have hi := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun n x => scalarPlantedCurvature hT (positiveProfile α n) x)
    (f := scalarPlantedCurvature hT α) (μ := volume) (a := 0) (b := q) (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun n => (scalarPlantedCurvature_continuous hT _).aestronglyMeasurable))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (scalarPlantedCurvature_bounds hT _ x).1]
      exact (scalarPlantedCurvature_bounds hT _ x).2)))
    intervalIntegrable_const
    (Eventually.of_forall (fun x _ => scalarPlantedCurvature_parameter_tendsto hT ht x))
  have hl := (scalarPlantedEnergy_parameter_tendsto hT ht q).sub
    (scalarPlantedEnergy_parameter_tendsto hT ht 0)
  have he (n) := scalarPlantedEnergy_integral hT (positiveProfile α n) hq hq1
    (positiveProfile_pos α n q) (fun x hx => positiveProfile_right_continuous α (hc x hx) n)
  simp_rw [he] at hl
  exact tendsto_nhds_unique hl (hi.const_mul T)

theorem scalarPlantedCurvature_integral_nonnegative {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : ∀ x ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    scalarPlantedCurvature hT α q - scalarPlantedCurvature hT α 0 =
      T * ∫ x in 0..q, scalarCurvatureFlux hT α x := by
  obtain rfl | hq := hq.eq_or_lt
  · simp
  have ht := positiveProfile_tendsto α
  have hi := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun n x => scalarCurvatureFlux hT (positiveProfile α n) x)
    (f := scalarCurvatureFlux hT α) (μ := volume) (a := 0) (b := q)
    (fun _ => (ReplicaTree.attachmentCount 1 2 : ℝ)^2 +
      2 * (ReplicaTree.attachmentCount 1 1 : ℝ)^3)
    (Eventually.of_forall (fun n => (scalarCurvatureFlux_measurable hT _).aestronglyMeasurable))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun x _ => by
      rw [Real.norm_eq_abs]
      exact scalarCurvatureFlux_abs_le hT _ x)))
    intervalIntegrable_const
    (Eventually.of_forall (fun x _ => scalarCurvatureFlux_parameter_tendsto hT ht x))
  have hl := (scalarPlantedCurvature_parameter_tendsto hT ht q).sub
    (scalarPlantedCurvature_parameter_tendsto hT ht 0)
  have he (n) := scalarPlantedCurvature_integral hT (positiveProfile α n) hq hq1
    (positiveProfile_pos α n q) (fun x hx => positiveProfile_right_continuous α (hc x hx) n)
  simp_rw [he] at hl
  exact tendsto_nhds_unique hl (hi.const_mul T)

noncomputable def scalarThirdMomentConstant (T : ℝ) : ℝ :=
  T * (ReplicaTree.attachmentCount 1 3 : ℝ)^2 *
    (∫ x : ℝ, x^2 * Real.exp (2 * |x|) ∂gaussianReal 0 1) /
      gaussianLinearEnvelopeMass 1 (-2)

private theorem smallClock_envelope_bound {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hTq : T*q ≤ 1) :
    scalarThirdGaussianEnvelope hT α 2 q /
      gaussianLinearEnvelopeMass (T*q) (-2) ≤ scalarThirdMomentConstant T := by
  have hs : 0 ≤ Real.sqrt (T*q) ∧ Real.sqrt (T*q) ≤ 1 :=
    ⟨Real.sqrt_nonneg _, (Real.sqrt_le_iff).mpr ⟨zero_le_one, by simpa using hTq⟩⟩
  let B : ℝ := ReplicaTree.attachmentCount 1 3
  let I : ℝ := ∫ x : ℝ, x^2 * Real.exp (2 * |x|) ∂gaussianReal 0 1
  have hi : Integrable (fun x : ℝ => x^2 * Real.exp (2 * |x|)) (gaussianReal 0 1) :=
    gaussianStandard_expabs_sq_integrable 2
  have hb (x : ℝ) :
      0 ≤ x^2 * (scalarThirdSlope hT α q (Real.sqrt (T*q)*x))^2 *
        Real.exp (2*Real.sqrt (T*q)*|x|) := by positivity
  have hle (x : ℝ) :
      x^2 * (scalarThirdSlope hT α q (Real.sqrt (T*q)*x))^2 *
        Real.exp (2*Real.sqrt (T*q)*|x|) ≤
      B^2 * (x^2 * Real.exp (2 * |x|)) := by
    have hj := pow_le_pow_left₀ (abs_nonneg _)
      (scalarThirdSlope_bound hT α q (Real.sqrt (T*q)*x)) 2
    rw [sq_abs] at hj
    have he : 2*Real.sqrt (T*q)*|x| ≤ 2*|x| := by
      nlinarith [mul_le_mul_of_nonneg_right hs.2 (abs_nonneg x)]
    calc
      _ ≤ x^2 * B^2 * Real.exp (2*|x|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hj (sq_nonneg x))
          (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by positivity)
      _ = _ := by ring
  have hfi : Integrable (fun x : ℝ =>
      x^2 * (scalarThirdSlope hT α q (Real.sqrt (T*q)*x))^2 *
        Real.exp (2*Real.sqrt (T*q)*|x|)) (gaussianReal 0 1) :=
    (hi.const_mul (B^2)).mono' (by
      have hpair : Continuous (fun x : ℝ => (q, Real.sqrt (T*q)*x)) := by fun_prop
      have hrc := (scalarThirdSlope_continuous hT α).comp hpair
      exact (((continuous_pow 2).mul (hrc.pow 2)).mul
        (Real.continuous_exp.comp
          ((continuous_const.mul continuous_const).mul continuous_abs))).aestronglyMeasurable)
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb x)]
        exact hle x))
  have hn : scalarThirdGaussianEnvelope hT α 2 q ≤ T * B^2 * I := by
    rw [scalarThirdGaussianEnvelope_rescale hT α 2 hq]
    have hh := integral_mono hfi (hi.const_mul (B^2)) hle
    rw [integral_const_mul] at hh
    nlinarith
  have hden : gaussianLinearEnvelopeMass 1 (-2) ≤
      gaussianLinearEnvelopeMass (T*q) (-2) := by
    rw [gaussianLinearEnvelopeMass_rescale zero_lt_one,
      gaussianLinearEnvelopeMass_rescale (mul_pos hT hq)]
    simp only [Real.sqrt_one, mul_one]
    apply integral_mono
    · exact integrable_exp_mul_abs_gaussianReal (-2) 1
    · exact integrable_exp_mul_abs_gaussianReal (-2*Real.sqrt (T*q)) 1
    · intro x
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hs.2 (abs_nonneg x)]
  have hp := gaussianLinearEnvelopeMass_pos zero_lt_one (-2)
  have hpq := gaussianLinearEnvelopeMass_pos (mul_pos hT hq) (-2)
  have hn0 : 0 ≤ scalarThirdGaussianEnvelope hT α 2 q := by
    rw [scalarThirdGaussianEnvelope_rescale hT α 2 hq]
    exact mul_nonneg hT.le (integral_nonneg hb)
  calc
    _ ≤ scalarThirdGaussianEnvelope hT α 2 q / gaussianLinearEnvelopeMass 1 (-2) :=
      div_le_div_of_nonneg_left hn0 hp hden
    _ ≤ T * B^2 * I / gaussianLinearEnvelopeMass 1 (-2) :=
      div_le_div_of_nonneg_right hn hp.le
    _ = _ := rfl

theorem scalarPlantedThirdSquare_smallClock {T q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hq : 0 < q) (hq1 : q ≤ 1) (hTq : T*q ≤ 1)
    (hc : ∀ x ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici x) x) :
    scalarPlantedJetPower hT α 2 2 q ≤ scalarThirdMomentConstant T * q := by
  have ht := positiveProfile_tendsto α
  apply le_of_tendsto (scalarPlantedJetPower_parameter_tendsto hT ht 2 2 q)
  apply Eventually.of_forall
  intro n
  have hh := (scalarPlantedThirdSquare_envelope hT (positiveProfile α n) hq hq1
    (positiveProfile_pos α n q)
    (fun x hx => positiveProfile_right_continuous α (hc x hx) n)).2
  exact (div_le_iff₀ hq).mp (hh.trans (smallClock_envelope_bound hT _ hq hTq))

theorem scalarPlantedThirdSquare_zero {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) : scalarPlantedJetPower hT α 2 2 0 = 0 := by
  rw [scalarPlantedJetPower_zero]
  have hp := scalarProfileJet_parity (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) 0 (Real.toNNReal T) 3 0
  norm_num only [neg_zero, show (-1 : ℝ)^3 = -1 by norm_num, neg_one_mul] at hp
  have hz' : scalarProfileJet (rescaledMassProfile α hT) 0 (Real.toNNReal T) 3 0 = 0 := by
    linarith
  have hz : scalarTailSpatialJet hT α 3 0 0 = 0 := by
    simpa only [scalarTailSpatialJet, mul_zero, sub_zero, mul_one, Pi.zero_apply] using hz'
  rw [hz]
  norm_num

noncomputable def scalarSmallClockFluxConstant (T A R : ℝ) : ℝ :=
  |scalarThirdMomentConstant T| * R +
    2*A*(ReplicaTree.attachmentCount 1 1 : ℝ)^3

theorem scalarCurvatureFlux_smallClock {T x A R q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hx : 0 ≤ x) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hq : 0 ≤ q) (hqR : q ≤ R*x) (hq1 : q ≤ 1) (hTq : T*q ≤ 1)
    (hmass : α.val q ≤ A*x)
    (hc : ∀ s ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici s) s) :
    |scalarCurvatureFlux hT α q| ≤ scalarSmallClockFluxConstant T A R * x := by
  have hthird : |scalarPlantedJetPower hT α 2 2 q| ≤
      |scalarThirdMomentConstant T| * R*x := by
    have hn : 0 ≤ scalarPlantedJetPower hT α 2 2 q :=
      (scalarJetPowerTest hT α 2 2 q).nonnegativeProfileTest_nonneg
        (fun y => sq_nonneg _) (rescaledMassProfile α hT)
        (fun s => (α.property.1 (s/T)).2) 0 _ 0
    rw [abs_of_nonneg hn]
    obtain rfl | hq := hq.eq_or_lt
    · simp [scalarPlantedThirdSquare_zero]
      positivity
    · have hh := scalarPlantedThirdSquare_smallClock hT α hq hq1 hTq hc
      exact hh.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) hq.le).trans
        (by simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hqR (abs_nonneg (scalarThirdMomentConstant T))))
  have hcube := scalarPlantedJetPower_abs_le hT α 1 3 q
  have hm0 := (α.property.1 q).1
  unfold scalarCurvatureFlux
  calc
    _ ≤ |scalarPlantedJetPower hT α 2 2 q| +
      |2*α.val q*scalarPlantedJetPower hT α 1 3 q| := abs_sub _ _
    _ ≤ |scalarThirdMomentConstant T| * R*x +
      (2*(A*x))*(ReplicaTree.attachmentCount 1 1 : ℝ)^3 := by
      apply add_le_add hthird
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hm0)]
      exact mul_le_mul (by linarith : 2*α.val q ≤ 2*(A*x)) hcube
        (abs_nonneg _) (by positivity)
    _ = _ := by unfold scalarSmallClockFluxConstant; ring

theorem scalarPlantedCurvature_smallClock {T x A R q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hx : 0 ≤ x) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hq : 0 ≤ q) (hqR : q ≤ R*x) (hq1 : q ≤ 1) (hTq : T*q ≤ 1)
    (hmass : α.val q ≤ A*x)
    (hc : ∀ s ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici s) s) :
    |scalarPlantedCurvature hT α q - scalarPlantedCurvature hT α 0| ≤
      T * scalarSmallClockFluxConstant T A R * x * q := by
  rw [scalarPlantedCurvature_integral_nonnegative hT α hq hq1 hc, abs_mul, abs_of_pos hT]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := q) (C := scalarSmallClockFluxConstant T A R * x)
    (f := scalarCurvatureFlux hT α) (fun s hs => by
      rw [uIoc_of_le hq] at hs
      rw [Real.norm_eq_abs]
      exact scalarCurvatureFlux_smallClock hT α hx hA hR hs.1.le
        (hs.2.trans hqR) (hs.2.trans hq1)
        ((mul_le_mul_of_nonneg_left hs.2 hT.le).trans hTq)
        ((α.property.2 hs.2).trans hmass)
        (fun r hr => hc r ⟨hr.1, hr.2.trans_le hs.2⟩))
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hq] at hh
  nlinarith [mul_le_mul_of_nonneg_left hh hT.le]

theorem scalarPlantedEnergy_smallClock_taylor {T x A R q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hx : 0 ≤ x) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hq : 0 ≤ q) (hqR : q ≤ R*x) (hq1 : q ≤ 1) (hTq : T*q ≤ 1)
    (hmass : α.val q ≤ A*x)
    (hc : ∀ s ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici s) s) :
    |scalarPlantedEnergy hT α q - scalarPlantedEnergy hT α 0 -
        T * scalarPlantedCurvature hT α 0 * q| ≤
      T^2 * scalarSmallClockFluxConstant T A R * x * q^2 := by
  let F := scalarSmallClockFluxConstant T A R
  have hF : 0 ≤ F := by dsimp [F, scalarSmallClockFluxConstant]; positivity
  have he : scalarPlantedEnergy hT α q - scalarPlantedEnergy hT α 0 -
      T * scalarPlantedCurvature hT α 0 * q =
      T * ∫ s in 0..q, scalarPlantedCurvature hT α s - scalarPlantedCurvature hT α 0 := by
    rw [intervalIntegral.integral_sub ((scalarPlantedCurvature_continuous hT α).intervalIntegrable 0 q)
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    rw [scalarPlantedEnergy_integral_nonnegative hT α hq hq1 hc]
    ring
  rw [he, abs_mul, abs_of_pos hT]
  have hb : ∀ s ∈ Icc (0 : ℝ) q,
      |scalarPlantedCurvature hT α s - scalarPlantedCurvature hT α 0| ≤ T*F*x*q := by
    intro s hs
    have hh := scalarPlantedCurvature_smallClock hT α hx hA hR hs.1
      (hs.2.trans hqR) (hs.2.trans hq1)
      ((mul_le_mul_of_nonneg_left hs.2 hT.le).trans hTq)
      ((α.property.2 hs.2).trans hmass)
      (fun r hr => hc r ⟨hr.1, hr.2.trans_le hs.2⟩)
    exact hh.trans (mul_le_mul_of_nonneg_left hs.2 (by positivity : 0 ≤ T*F*x))
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := q) (C := T*F*x*q)
    (f := fun s => scalarPlantedCurvature hT α s - scalarPlantedCurvature hT α 0)
    (fun s hs => by
      rw [uIoc_of_le hq] at hs
      rw [Real.norm_eq_abs]
      exact hb s ⟨hs.1.le, hs.2⟩)
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hq] at hh
  nlinarith [mul_le_mul_of_nonneg_left hh hT.le]

theorem scalarPlantedEnergy_zero {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) : scalarPlantedEnergy hT α 0 = 0 := by
  unfold scalarPlantedEnergy
  rw [mul_zero, Real.toNNReal_zero, HeatJet.nonnegativeProfileTest_zero _ _
    (fun s => (α.property.1 (s/T)).2)]
  simp only [HeatJet.square, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have hp := scalarProfileJet_parity (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) 0 (Real.toNNReal T) 1 0
  norm_num only [neg_zero, neg_one_mul, pow_one] at hp
  have hz : scalarProfileJet (rescaledMassProfile α hT) 0 (Real.toNNReal T) 1 0 = 0 := by
    linarith
  simpa only [scalarTailJet, scalarProfileHeatJet, Pi.zero_apply, mul_zero,
    sub_zero, mul_one, hz, zero_pow (by decide : 2 ≠ 0)]

theorem scalarPlantedEnergy_calibrated_slope {T x A R c B q : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hx : 0 < x) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hc : 0 < c) (hB : 0 ≤ B) (hq : c*x ≤ q) (hqR : q ≤ R*x)
    (hq1 : q ≤ 1) (hTq : T*q ≤ 1) (hmass : α.val q ≤ A*x)
    (hcont : ∀ s ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici s) s)
    (hcal : |scalarPlantedEnergy hT α q - q| ≤ B*x^3) :
    |T*scalarPlantedCurvature hT α 0 - 1| ≤
      ((B + T^2*scalarSmallClockFluxConstant T A R*R^2)/c)*x^2 := by
  have hq0 : 0 < q := (mul_pos hc hx).trans_le hq
  have ht := scalarPlantedEnergy_smallClock_taylor hT α hx.le hA hR
    hq0.le hqR hq1 hTq hmass hcont
  rw [scalarPlantedEnergy_zero] at ht
  simp only [sub_zero] at ht
  have hF : 0 ≤ scalarSmallClockFluxConstant T A R := by
    unfold scalarSmallClockFluxConstant; positivity
  have hs : |(T*scalarPlantedCurvature hT α 0 - 1)*q| ≤
      B*x^3 + T^2*scalarSmallClockFluxConstant T A R*x*q^2 := by
    have hh := abs_sub (scalarPlantedEnergy hT α q - q)
      (scalarPlantedEnergy hT α q - T*scalarPlantedCurvature hT α 0*q)
    have he : (scalarPlantedEnergy hT α q - q) -
        (scalarPlantedEnergy hT α q - T*scalarPlantedCurvature hT α 0*q) =
        (T*scalarPlantedCurvature hT α 0 - 1)*q := by ring
    rw [he] at hh
    exact hh.trans (add_le_add hcal ht)
  rw [abs_mul, abs_of_pos hq0] at hs
  have hq2 : q^2 ≤ R^2*x^2 := by nlinarith [sq_nonneg (R*x-q)]
  have hcap := mul_le_mul_of_nonneg_left hq2
    (by positivity : 0 ≤ T^2*scalarSmallClockFluxConstant T A R*x)
  have hbase := mul_le_mul_of_nonneg_left hq
    (abs_nonneg (T*scalarPlantedCurvature hT α 0 - 1))
  have hdivision : c*((B + T^2*scalarSmallClockFluxConstant T A R*R^2)/c)=
      B + T^2*scalarSmallClockFluxConstant T A R*R^2 :=
    mul_div_cancel₀ _ hc.ne'
  apply (mul_le_mul_iff_left₀ hx).mp
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c * (|T*scalarPlantedCurvature hT α 0 - 1| * x) ≤
        B*x^3 + T^2*scalarSmallClockFluxConstant T A R*x*q^2 := by
      nlinarith [hbase, hs]
    _ ≤ (B + T^2*scalarSmallClockFluxConstant T A R*R^2)*x^3 := by
      nlinarith [hcap]
    _ = c * (((B + T^2*scalarSmallClockFluxConstant T A R*R^2)/c)*x^2*x) := by
      rw [show c * (((B + T^2*scalarSmallClockFluxConstant T A R*R^2)/c)*x^2*x) =
        (c*((B + T^2*scalarSmallClockFluxConstant T A R*R^2)/c))*x^3 by ring,
        hdivision]

theorem scalarPlantedEnergy_calibrated_uniform {T x A R c B q r : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hx : 0 < x) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hc : 0 < c) (hB : 0 ≤ B) (hq : c*x ≤ q) (hqR : q ≤ R*x)
    (hq1 : q ≤ 1) (hTq : T*q ≤ 1) (hmass : α.val q ≤ A*x)
    (hcont : ∀ s ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici s) s)
    (hcal : |scalarPlantedEnergy hT α q - q| ≤ B*x^3)
    (hr : 0 ≤ r) (hrq : r ≤ q) :
    |scalarPlantedEnergy hT α r - r| ≤
      (((B + T^2*scalarSmallClockFluxConstant T A R*R^2)/c)*R +
        T^2*scalarSmallClockFluxConstant T A R*R^2)*x^3 := by
  let F := scalarSmallClockFluxConstant T A R
  let C := (B + T^2*F*R^2)/c
  have hF : 0 ≤ F := by dsimp [F, scalarSmallClockFluxConstant]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := scalarPlantedEnergy_calibrated_slope hT α hx hA hR hc hB
    hq hqR hq1 hTq hmass hcont hcal
  have ht := scalarPlantedEnergy_smallClock_taylor hT α hx.le hA hR
    hr (hrq.trans hqR) (hrq.trans hq1)
    ((mul_le_mul_of_nonneg_left hrq hT.le).trans hTq)
    ((α.property.2 hrq).trans hmass)
    (fun s hs => hcont s ⟨hs.1, hs.2.trans_le hrq⟩)
  rw [scalarPlantedEnergy_zero] at ht
  simp only [sub_zero] at ht
  have hlinear : |(T*scalarPlantedCurvature hT α 0 - 1)*r| ≤ C*R*x^3 := by
    rw [abs_mul, abs_of_nonneg hr]
    calc
      _ ≤ (C*x^2)*r := mul_le_mul_of_nonneg_right hs hr
      _ ≤ (C*x^2)*(R*x) :=
        mul_le_mul_of_nonneg_left (hrq.trans hqR) (by positivity)
      _ = _ := by ring
  have hr2 : r^2 ≤ R^2*x^2 := by
    have hh := hrq.trans hqR
    nlinarith [sq_nonneg (R*x-r)]
  have hrem : T^2*F*x*r^2 ≤ T^2*F*R^2*x^3 := by
    have hh := mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ T^2*F*x)
    nlinarith
  have hadd := abs_add_le
    (scalarPlantedEnergy hT α r - T*scalarPlantedCurvature hT α 0*r)
    ((T*scalarPlantedCurvature hT α 0 - 1)*r)
  have he : (scalarPlantedEnergy hT α r - T*scalarPlantedCurvature hT α 0*r) +
      (T*scalarPlantedCurvature hT α 0 - 1)*r = scalarPlantedEnergy hT α r - r := by ring
  rw [he] at hadd
  exact (hadd.trans (add_le_add (ht.trans hrem) hlinear)).trans_eq (by dsimp [C, F]; ring)

theorem scalarPlantedEnergy_origin_derivative {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles)
    (hc : ∀ s ∈ Ico (0 : ℝ) 1, ContinuousWithinAt α.val (Ici s) s) :
    HasDerivWithinAt (scalarPlantedEnergy hT α)
      (T*scalarPlantedCurvature hT α 0) (Ici 0) 0 := by
  have hC := scalarPlantedCurvature_continuous hT α
  have hd := intervalIntegral.integral_hasDerivAt_right (hC.intervalIntegrable 0 0)
    hC.stronglyMeasurable.stronglyMeasurableAtFilter hC.continuousAt
  have hh := (hd.const_mul T).add_const (scalarPlantedEnergy hT α 0)
  apply hh.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with q hq hq1
    have he := scalarPlantedEnergy_integral_nonnegative hT α hq hq1.le
      (fun s hs => hc s ⟨hs.1, hs.2.trans hq1⟩)
    linarith
  · simp

noncomputable def scalarCovarianceResponse {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (K : ℝ) : ℝ := scalarPlantedEnergy hT α (K/T)

theorem scalarCovarianceResponse_origin_derivative {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles)
    (hc : ∀ s ∈ Ico (0 : ℝ) 1, ContinuousWithinAt α.val (Ici s) s) :
    HasDerivWithinAt (scalarCovarianceResponse hT α)
      (scalarPlantedCurvature hT α 0) (Ici 0) 0 := by
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  have hd := (scalarPlantedEnergy_origin_derivative hT α hc).scomp_of_eq (0 : ℝ)
    (((hasDerivAt_id (0 : ℝ)).div_const T).hasDerivWithinAt)
    (fun K hK => div_nonneg hK hT.le) (by simp)
  have he : (1/T)*(T*scalarPlantedCurvature hT α 0) = scalarPlantedCurvature hT α 0 := by
    field_simp
  rw [smul_eq_mul, he] at hd
  convert! hd using 1 <;> rfl

theorem scalarCovarianceResponse_calibrated_uniform {T x A R c B q K : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hx : 0 < x) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hc : 0 < c) (hB : 0 ≤ B) (hq : c*x ≤ q) (hqR : q ≤ R*x)
    (hq1 : q ≤ 1) (hTq : T*q ≤ 1) (hmass : α.val q ≤ A*x)
    (hcont : ∀ s ∈ Ico (0 : ℝ) q, ContinuousWithinAt α.val (Ici s) s)
    (hcal : |scalarPlantedEnergy hT α q - q| ≤ B*x^3)
    (hK : 0 ≤ K) (hKq : K ≤ T*q) :
    |scalarCovarianceResponse hT α K - K/T| ≤
      (((B + T^2*scalarSmallClockFluxConstant T A R*R^2)/c)*R +
        T^2*scalarSmallClockFluxConstant T A R*R^2)*x^3 := by
  exact scalarPlantedEnergy_calibrated_uniform hT α hx hA hR hc hB hq hqR hq1 hTq
    hmass hcont hcal (div_nonneg hK hT.le) ((div_le_iff₀ hT).mpr (by simpa [mul_comm] using hKq))

end OAI.SKFluctuations.Hierarchy

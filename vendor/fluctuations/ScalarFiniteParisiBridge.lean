module

public import SKFluctuationsOAI.Probability.SKFluctuations.NonnegativeProfileValueStep
public import SKFluctuationsOAI.Probability.ParisiFinite.DyadicMeshTendsto

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.Hierarchy

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

theorem scalarTerminal_normalized_parisi {β : ℝ} (hβ : 0 < β)
    (x : Fin 1 → ℝ) :
    scalarTerminal.F x = β * ParisiFinite.terminal β (x 0 / β) - Real.log 2 := by
  rw [scalarTerminal_F]
  unfold ParisiFinite.terminal
  rw [mul_div_cancel₀ _ hβ.ne', Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (Real.cosh_pos _).ne']
  field_simp
  <;> ring

theorem scalarClock_normalized_parisi {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (d : ℝ≥0) (x : Fin 1 → ℝ) :
    clockContinuation (a / β) (fun y : Fin 1 → ℝ =>
      β * f (y 0 / β) - Real.log 2) (β ^ 2 * d) x =
      β * ParisiFinite.step a (Real.sqrt d) f (x 0 / β) - Real.log 2 := by
  have hF : Continuous (fun y : Fin 1 → ℝ => β * f (y 0 / β) - Real.log 2) := by
    have hd : Continuous (fun y : Fin 1 → ℝ => y 0 / β) := by fun_prop
    exact (hf.continuous.comp hd).const_mul β |>.sub continuous_const
  have hfc := hf.continuous
  rw [clockContinuation_eq hF (a / β) (mul_nonneg (sq_nonneg _) d.coe_nonneg)]
  have hsqrt : Real.sqrt (β ^ 2 * (d : ℝ)) = β * Real.sqrt d := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hβ]
  rw [hsqrt]
  have he (z : Fin 1 → ℝ) :
      Real.exp ((a / β) * (β * f ((x + (β * Real.sqrt d) • z) 0 / β) - Real.log 2)) =
      Real.exp (a * f (x 0 / β + Real.sqrt d * z 0)) *
        Real.exp (-(a / β) * Real.log 2) := by
    have hx : (x + (β * Real.sqrt d) • z) 0 / β = x 0 / β + Real.sqrt d * z 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      <;> ring
    rw [hx, ← Real.exp_add]
    congr 1
    field_simp
    <;> ring
  simp_rw [he]
  rw [integral_mul_const, integral_gaussian_eval (0 : Fin 1) 1
    (f := fun z => Real.exp (a * f (x 0 / β + Real.sqrt d * z))) (by fun_prop)]
  have hp : 0 < ∫ z, Real.exp (a * f (x 0 / β + Real.sqrt d * z)) ∂gaussianReal 0 1 :=
    ParisiFinite.integral_exp_pos (ParisiFinite.integrable_exp_shift hf a (x 0 / β) (Real.sqrt d))
  rw [Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_exp]
  simp only [ParisiFinite.step, ParisiFinite.logMean, ha.ne', ↓reduceIte]
  field_simp
  <;> ring

def parisiScheduleOfHeat (β : ℝ≥0) (cs : List HeatClock) : ParisiFinite.Schedule :=
  cs.map (fun c => (β * Real.toNNReal c.mass, c.time / β ^ 2))

theorem scalar_schedule_normalized_parisi {β : ℝ≥0} (hβ : 0 < β)
    (cs : List HeatClock) (x : Fin 1 → ℝ) :
    (scalarTerminal.schedule cs).F x =
      (β : ℝ) * ParisiFinite.recursion β (parisiScheduleOfHeat β cs) (x 0 / β) - Real.log 2 := by
  induction cs generalizing x with
  | nil => exact scalarTerminal_normalized_parisi hβ x
  | cons c cs ih =>
    have hb : (0 : ℝ) < β := hβ
    have hm : (0 : ℝ) < (β : ℝ) * c.mass := mul_pos hb c.positive
    have hdiv : (β : ℝ) * c.mass / β = c.mass := mul_div_cancel_left₀ _ hb.ne'
    have htime : (β : ℝ) ^ 2 * ((c.time / β ^ 2 : ℝ≥0) : ℝ) = c.time := by
      simp only [NNReal.coe_div, NNReal.coe_pow]
      field_simp
    change clockContinuation c.mass (scalarTerminal.schedule cs).F c.time x = _
    rw [funext ih]
    have hh := scalarClock_normalized_parisi hb hm
      (ParisiFinite.recursion_lipschitz hb (parisiScheduleOfHeat β cs)) (c.time / β ^ 2) x
    rw [hdiv, htime] at hh
    simpa only [parisiScheduleOfHeat, List.map_cons, ParisiFinite.recursion,
      NNReal.coe_mul, Real.coe_toNNReal _ c.positive.le] using hh

def scalarProfileOfParisiMeasure (ρ : ProbabilityMeasure ParisiFinite.OrderPoint) :
    boundedMassProfiles :=
  ⟨fun s => (ρ : Measure ParisiFinite.OrderPoint).real {q | (q : ℝ) ≤ s},
    (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩),
    fun s t hst => measureReal_mono (fun q hq => hq.trans hst)⟩

theorem scalarProfileOfParisiMeasure_mem (ρ : ProbabilityMeasure ParisiFinite.OrderPoint) :
    scalarProfileOfParisiMeasure ρ ∈ scalarProfiles := by
  constructor
  · intro s hs
    have he : {q : ParisiFinite.OrderPoint | (q : ℝ) ≤ s} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr (hs.trans_le q.property.1)
    simp only [scalarProfileOfParisiMeasure, he, Measure.real, measure_empty,
      ENNReal.toReal_zero]
  · intro s hs
    have he : {q : ParisiFinite.OrderPoint | (q : ℝ) ≤ s} = univ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact q.property.2.trans hs.le
    simp only [scalarProfileOfParisiMeasure, he, Measure.real, measure_univ,
      ENNReal.toReal_one]

theorem parisi_measureCoefficient_scalarProfile
    (ρ : ProbabilityMeasure ParisiFinite.OrderPoint) (β s : ℝ≥0) :
    ParisiFinite.measureCoefficient ρ β s =
      β * Real.toNNReal ((scalarProfileOfParisiMeasure ρ).val s) := by
  simp only [ParisiFinite.measureCoefficient, scalarProfileOfParisiMeasure, mul_comm]

def coefficientOfPositiveScalarProfile (β : ℝ≥0) (α : PositiveMassProfile)
    (s : ℝ≥0) : ℝ≥0 := β * Real.toNNReal (α.mass s)

def rescaledPositiveScalarProfile (β : ℝ≥0) (hβ : 0 < β)
    (α : PositiveMassProfile) : PositiveMassProfile where
  mass u := α.mass (u / (β : ℝ) ^ 2)
  positive u := α.positive _
  monotone := α.monotone.comp (monotone_id.div_const (sq_pos_of_pos hβ).le)

theorem parisiScheduleOfHeat_rescaled_grid {β : ℝ≥0} (hβ : 0 < β)
    (α : PositiveMassProfile) (t d : ℝ≥0) (k : ℕ) :
    parisiScheduleOfHeat β ((rescaledPositiveScalarProfile β hβ α).grid
      ((β : ℝ) ^ 2 * t) (β ^ 2 * d) k) =
      ParisiFinite.dyadicSchedule (coefficientOfPositiveScalarProfile β α) false t d k := by
  have hb : (β : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hβ).ne'
  induction k generalizing t d with
  | zero =>
    simp only [PositiveMassProfile.grid, parisiScheduleOfHeat, List.map_cons,
      List.map_nil, ParisiFinite.dyadicSchedule, Bool.false_eq_true, ↓reduceIte,
      coefficientOfPositiveScalarProfile, rescaledPositiveScalarProfile]
    congr 2
    · congr 2
      field_simp
    · field_simp
  | succ k ih =>
    have hd : β ^ 2 * d / 2 = β ^ 2 * (d / 2) := by ring
    have ht : (β : ℝ) ^ 2 * (t : ℝ) + ((β ^ 2 * d : ℝ≥0) : ℝ) / 2 =
        (β : ℝ) ^ 2 * ((t + d / 2 : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_div,
        NNReal.coe_ofNat]
      ring
    simp only [PositiveMassProfile.grid, parisiScheduleOfHeat, List.map_append,
      ParisiFinite.dyadicSchedule, hd, ht]
    exact congrArg₂ List.append (ih t (d / 2)) (ih (t + d / 2) (d / 2))

theorem coefficientOfPositiveScalarProfile_monotone (β : ℝ≥0)
    (α : PositiveMassProfile) : Monotone (coefficientOfPositiveScalarProfile β α) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left (Real.toNNReal_mono (α.monotone hst)) zero_le

theorem scalar_positive_profile_normalized_parisi {β : ℝ≥0} (hβ : 0 < β)
    (α : PositiveMassProfile) (t d : ℝ≥0) (x : Fin 1 → ℝ) :
    scalarTerminal.profileValue (rescaledPositiveScalarProfile β hβ α)
      ((β : ℝ) ^ 2 * t) (β ^ 2 * d) x =
      (β : ℝ) * ParisiFinite.dyadicEvolution (coefficientOfPositiveScalarProfile β α)
        t d (ParisiFinite.terminal β) (x 0 / β) - Real.log 2 := by
  have hleft := scalarTerminal.grid_tendsto (rescaledPositiveScalarProfile β hβ α)
    ((β : ℝ) ^ 2 * t) (β ^ 2 * d) x
  have hright := ((ParisiFinite.dyadic_low_tendsto
    (ParisiFinite.terminal_lipschitz (NNReal.coe_pos.mpr hβ))
    (coefficientOfPositiveScalarProfile_monotone β α) t d (x 0 / β)).const_mul
      (β : ℝ)).sub_const (Real.log 2)
  apply tendsto_nhds_unique hleft
  apply hright.congr
  intro k
  rw [scalar_schedule_normalized_parisi hβ,
    parisiScheduleOfHeat_rescaled_grid hβ, ParisiFinite.recursion_eq_evolve]

private theorem parisi_step_continuous_coefficient {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (s x a : ℝ) :
    ContinuousAt (fun r => ParisiFinite.step r s f x) a := by
  let X : ℝ → ℝ := fun z => f (x + s * z)
  have hm (v : ℝ) : v ∈ interior (integrableExpSet X (gaussianReal 0 1)) := by
    have he : integrableExpSet X (gaussianReal 0 1) = univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro v
      exact ParisiFinite.integrable_exp_shift hf v x s
    rw [he, interior_univ]
    trivial
  have he : (fun r => ParisiFinite.step r s f x) = dslope (cgf X (gaussianReal 0 1)) 0 := by
    funext r
    by_cases hr : r = 0
    · subst r
      rw [dslope_same, deriv_cgf_zero (hm 0)]
      simp [ParisiFinite.step, ParisiFinite.logMean, X]
    · rw [dslope_of_ne _ hr]
      simp [ParisiFinite.step, ParisiFinite.logMean, hr, slope, cgf, mgf, X,
        div_eq_mul_inv, mul_comm]
  rw [he]
  by_cases ha : a = 0
  · subst a
    exact continuousAt_dslope_same.mpr (analyticAt_cgf (hm 0)).differentiableAt
  · exact (continuousAt_dslope_of_ne ha).mpr (analyticAt_cgf (hm a)).continuousAt

private theorem parisi_step_tendsto_coefficient_field {L : ℝ≥0}
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, LipschitzWith L (F n)) (hf : LipschitzWith L f)
    (hfn : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {A : ℕ → ℝ} {a : ℝ} (hA : ∀ n, 0 ≤ A n) (ha : 0 ≤ a)
    (hAn : Tendsto A atTop (𝓝 a)) (s x : ℝ) :
    Tendsto (fun n => ParisiFinite.step (A n) s (F n) x) atTop
      (𝓝 (ParisiFinite.step a s f x)) := by
  have he := SKCavity.tendsto_succ_reciprocal
  have hp (k : ℕ) : 0 < (1 : ℝ) / (k + 1 : ℕ) := by positivity
  have hlo : Tendsto (fun k : ℕ => max 0 (a - 1 / (k + 1 : ℕ))) atTop (𝓝 a) := by
    simpa only [sub_zero, max_eq_right ha] using
      (tendsto_const_nhds (x := (0 : ℝ))).max ((tendsto_const_nhds (x := a)).sub he)
  have hup : Tendsto (fun k : ℕ => a + 1 / (k + 1 : ℕ)) atTop (𝓝 a) := by
    simpa only [add_zero] using tendsto_const_nhds.add he
  have hs := parisi_step_continuous_coefficient hf s x a
  rw [tendsto_order]
  constructor
  · intro v hv
    by_cases hz : a = 0
    · subst a
      filter_upwards [(ParisiFinite.step_tendsto hF hf hfn 0 s x).eventually (lt_mem_nhds hv)] with n hn
      exact hn.trans_le (ParisiFinite.step_parameter_mono (hF n) le_rfl (hA n) s x)
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
      obtain ⟨k, hk⟩ := ((hs.tendsto.comp hlo).eventually (lt_mem_nhds hv)).exists
      have hlt : max 0 (a - 1 / (k + 1 : ℕ)) < a := max_lt hap (sub_lt_self _ (hp k))
      filter_upwards [hAn.eventually (lt_mem_nhds hlt),
        (ParisiFinite.step_tendsto hF hf hfn (max 0 (a - 1 / (k + 1 : ℕ))) s x).eventually
          (lt_mem_nhds hk)] with n hn hn'
      exact hn'.trans_le (ParisiFinite.step_parameter_mono (hF n) (le_max_left _ _) hn.le s x)
  · intro v hv
    obtain ⟨k, hk⟩ := ((hs.tendsto.comp hup).eventually (gt_mem_nhds hv)).exists
    have hlt : a < a + 1 / (k + 1 : ℕ) := lt_add_of_pos_right _ (hp k)
    filter_upwards [hAn.eventually (gt_mem_nhds hlt),
      (ParisiFinite.step_tendsto hF hf hfn (a + 1 / (k + 1 : ℕ)) s x).eventually
        (gt_mem_nhds hk)] with n hn hn'
    exact (ParisiFinite.step_parameter_mono (hF n) (hA n) hn.le s x).trans_lt hn'

private theorem parisi_dyadic_fixed_tendsto_coefficient {L : ℝ≥0}
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, LipschitzWith L (F n)) (hf : LipschitzWith L f)
    (hfn : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {G : ℕ → ℝ≥0 → ℝ≥0} {γ : ℝ≥0 → ℝ≥0}
    (hG : ∀ t, Tendsto (fun n => G n t) atTop (𝓝 (γ t)))
    (u : Bool) (t d : ℝ≥0) (k : ℕ) (x : ℝ) :
    Tendsto (fun n => ParisiFinite.evolve (ParisiFinite.dyadicSchedule (G n) u t d k) (F n) x)
      atTop (𝓝 (ParisiFinite.evolve (ParisiFinite.dyadicSchedule γ u t d k) f x)) := by
  induction k generalizing F f t d x with
  | zero =>
    simp only [ParisiFinite.dyadicSchedule, ParisiFinite.evolve]
    exact parisi_step_tendsto_coefficient_field hF hf hfn (fun n => (G n _).coe_nonneg)
      (γ _).coe_nonneg (NNReal.continuous_coe.continuousAt.tendsto.comp (hG _)) _ _
  | succ k ih =>
    simp only [ParisiFinite.dyadicSchedule, ParisiFinite.evolve_append]
    exact ih (fun n => ParisiFinite.evolve_lipschitz (hF n) _)
      (ParisiFinite.evolve_lipschitz hf _)
      (fun y => ih hF hf hfn (t + d / 2) (d / 2) y) t (d / 2) x

private theorem parisi_dyadicEvolution_tendsto_coefficient
    {G : ℕ → ℝ≥0 → ℝ≥0} {γ : ℝ≥0 → ℝ≥0}
    (hGm : ∀ n, Monotone (G n)) (hγ : Monotone γ) {B : ℝ}
    (hb : ∀ t, (γ t : ℝ) ≤ B) (hG : ∀ t, Tendsto (fun n => G n t) atTop (𝓝 (γ t)))
    {f : ℝ → ℝ} (hf : LipschitzWith 1 f) (t d : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => ParisiFinite.dyadicEvolution (G n) t d f x) atTop
      (𝓝 (ParisiFinite.dyadicEvolution γ t d f x)) := by
  rw [tendsto_order]
  constructor
  · intro v hv
    obtain ⟨k, hk⟩ := ((ParisiFinite.dyadic_low_tendsto hf hγ t d x).eventually (lt_mem_nhds hv)).exists
    filter_upwards [(parisi_dyadic_fixed_tendsto_coefficient (fun _ => hf) hf
      (fun _ => tendsto_const_nhds) hG false t d k x).eventually (lt_mem_nhds hk)] with n hn
    exact hn.trans_le (le_ciSup (ParisiFinite.dyadic_low_bddAbove hf (hGm n) t d x) k)
  · intro v hv
    obtain ⟨k, hk⟩ := ((ParisiFinite.dyadic_high_tendsto hf hγ hb t d x).eventually (gt_mem_nhds hv)).exists
    filter_upwards [(parisi_dyadic_fixed_tendsto_coefficient (fun _ => hf) hf
      (fun _ => tendsto_const_nhds) hG true t d k x).eventually (gt_mem_nhds hk)] with n hn
    apply lt_of_le_of_lt ?_ hn
    apply le_of_tendsto (ParisiFinite.dyadic_low_tendsto hf (hGm n) t d x)
    filter_upwards [eventually_ge_atTop k] with j hj
    exact (ParisiFinite.dyadicSchedule_low_le_high hf (hGm n) t d j x).trans
      (ParisiFinite.dyadic_high_antitone hf (hGm n) t d x hj)

def coefficientOfScalarProfile (β : ℝ≥0) (α : boundedMassProfiles)
    (s : ℝ≥0) : ℝ≥0 := β * Real.toNNReal (α.val s)

theorem coefficientOfScalarProfile_monotone (β : ℝ≥0)
    (α : boundedMassProfiles) : Monotone (coefficientOfScalarProfile β α) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left (Real.toNNReal_mono (α.property.2 hst)) zero_le

theorem coefficientOfScalarProfile_bound (β : ℝ≥0)
    (α : boundedMassProfiles) (s : ℝ≥0) : (coefficientOfScalarProfile β α s : ℝ) ≤ β := by
  simp only [coefficientOfScalarProfile, NNReal.coe_mul,
    Real.coe_toNNReal _ (α.property.1 s).1]
  exact mul_le_of_le_one_right β.coe_nonneg (α.property.1 s).2

theorem scalar_nonnegative_profile_normalized_parisi {β : ℝ≥0} (hβ : 0 < β)
    (α : boundedMassProfiles) (x : Fin 1 → ℝ) :
    scalarTerminal.nonnegativeProfileValue
      (rescaledMassProfile α (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)))
      0 (β ^ 2) x =
      (β : ℝ) * ParisiFinite.dyadicEvolution (coefficientOfScalarProfile β α)
        0 1 (ParisiFinite.terminal β) (x 0 / β) - Real.log 2 := by
  let A := boundedNonnegativeProfile α
  let G : ℕ → ℝ≥0 → ℝ≥0 := fun k => coefficientOfPositiveScalarProfile β (A.positiveApprox k)
  have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hG (s : ℝ≥0) : Tendsto (fun k => G k s) atTop
      (𝓝 (coefficientOfScalarProfile β α s)) := by
    have hs := continuous_real_toNNReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := α.val s)).add hp)
    simpa only [Function.comp_def, add_zero, G, coefficientOfPositiveScalarProfile, A,
      boundedNonnegativeProfile, NonnegativeMassProfile.positiveApprox,
      coefficientOfScalarProfile] using hs.const_mul β
  have hright := ((parisi_dyadicEvolution_tendsto_coefficient
    (fun k => coefficientOfPositiveScalarProfile_monotone β (A.positiveApprox k))
    (coefficientOfScalarProfile_monotone β α) (coefficientOfScalarProfile_bound β α)
    hG (ParisiFinite.terminal_lipschitz (NNReal.coe_pos.mpr hβ)) 0 1
    (x 0 / β)).const_mul (β : ℝ)).sub_const (Real.log 2)
  have hleft := scalarTerminal.regularized_tendsto
    (rescaledMassProfile α (sq_pos_of_pos (NNReal.coe_pos.mpr hβ))) 0 (β ^ 2) x
  apply tendsto_nhds_unique hleft
  apply hright.congr
  intro k
  have hh := scalar_positive_profile_normalized_parisi hβ (A.positiveApprox k) 0 1 x
  simpa only [NNReal.coe_zero, mul_zero, mul_one, G, A, rescaledPositiveScalarProfile,
    boundedNonnegativeProfile, rescaledMassProfile, NonnegativeMassProfile.positiveApprox] using hh.symm

theorem parisi_coefficientPenalty_scalarProfile (β : ℝ≥0) (α : boundedMassProfiles) :
    (β : ℝ) * ParisiFinite.coefficientPenalty (coefficientOfScalarProfile β α) 0 1 =
      (β : ℝ) ^ 2 / 2 * scalarPenalty α := by
  rw [scalarPenalty_eq]
  simp only [ParisiFinite.coefficientPenalty, NNReal.coe_zero, zero_add, NNReal.coe_one]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  simp only [coefficientOfScalarProfile, NNReal.coe_mul,
    Real.coe_toNNReal _ (α.property.1 _).1, Real.coe_toNNReal s hs.1]
  ring

theorem scalarParisiValue_eq_orderParameterFunctional {β : ℝ≥0} (hβ : 0 < β)
    (α : boundedMassProfiles) :
    scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α =
      (β : ℝ) * ParisiFinite.orderParameterFunctional β (coefficientOfScalarProfile β α) -
        Real.log 2 - (β : ℝ) ^ 2 / 4 := by
  unfold scalarParisiValue
  have hv := scalar_nonnegative_profile_normalized_parisi hβ α 0
  have he := congrArg (fun v : ℝ => v - (β : ℝ) ^ 2 / 2 * scalarPenalty α -
    (β : ℝ) ^ 2 / 4) hv
  simp only [Pi.zero_apply, zero_div] at he
  unfold ParisiFinite.orderParameterFunctional
  rw [mul_sub, parisi_coefficientPenalty_scalarProfile]
  convert he using 1 <;> first | rfl | ring

theorem scalarParisiValue_eq_measureFunctional {β : ℝ≥0} (hβ : 0 < β)
    (ρ : ProbabilityMeasure ParisiFinite.OrderPoint) :
    scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ))
      (scalarProfileOfParisiMeasure ρ) =
      (β : ℝ) * ParisiFinite.measureFunctional β ρ - Real.log 2 - (β : ℝ) ^ 2 / 4 := by
  rw [scalarParisiValue_eq_orderParameterFunctional hβ]
  have he : coefficientOfScalarProfile β (scalarProfileOfParisiMeasure ρ) =
      ParisiFinite.measureCoefficient ρ β := by
    funext s
    exact (parisi_measureCoefficient_scalarProfile ρ β s).symm
  rw [he]
  rfl

def normalizedScalarParisiReference (β : ℝ≥0) : ℝ :=
  (β : ℝ) * SKQAOA.limitingFreeEnergy β - Real.log 2 - (β : ℝ) ^ 2 / 4

theorem normalizedScalarParisiReference_le_value {β : ℝ≥0} (hβ : 0 < β)
    (α : boundedMassProfiles) :
    normalizedScalarParisiReference β ≤
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α := by
  rw [scalarParisiValue_eq_orderParameterFunctional hβ]
  have hp := ParisiFinite.limitingFreeEnergy_le_orderParameterFunctional
    (coefficientOfScalarProfile_monotone β α) (NNReal.coe_pos.mpr hβ)
    (coefficientOfScalarProfile_bound β α)
  unfold normalizedScalarParisiReference
  nlinarith [β.coe_nonneg]

theorem exists_scalarProfile_eq_normalizedScalarParisiReference {β : ℝ≥0}
    (hβ : 0 < β) :
    ∃ α ∈ scalarProfiles,
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α =
        normalizedScalarParisiReference β ∧
      ∀ γ ∈ scalarProfiles,
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α ≤
          scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) γ := by
  obtain ⟨ρ, _, hp⟩ := ParisiFinite.exists_minimizing_Parisi_measure hβ
  refine ⟨scalarProfileOfParisiMeasure ρ, scalarProfileOfParisiMeasure_mem ρ, ?_, ?_⟩
  · rw [scalarParisiValue_eq_measureFunctional hβ, hp]
    rfl
  · intro γ _
    rw [scalarParisiValue_eq_measureFunctional hβ, hp]
    exact normalizedScalarParisiReference_le_value hβ γ

theorem scalar_minimizer_value_eq_normalizedScalarParisiReference {β : ℝ≥0}
    (hβ : 0 < β) (α : boundedMassProfiles)
    (hmin : ∀ γ ∈ scalarProfiles,
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α ≤
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) γ) :
    scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α =
      normalizedScalarParisiReference β := by
  obtain ⟨γ, hγ, hv, _⟩ := exists_scalarProfile_eq_normalizedScalarParisiReference hβ
  exact le_antisymm ((hmin γ hγ).trans_eq hv)
    (normalizedScalarParisiReference_le_value hβ α)

end OAI.SKFluctuations.Hierarchy

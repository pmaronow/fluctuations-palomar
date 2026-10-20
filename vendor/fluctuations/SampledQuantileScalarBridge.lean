module

public import FiniteQuantileCDF
public import QuantileLawContinuity

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def sampleHeatClocks (h : ℝ → ℝ) : ℝ → List PositiveMass → List HeatClock
  | _, [] => []
  | a, b :: bs =>
    { mass := b.val, positive := b.property,
      time := Real.toNNReal (h b.val - h a) } :: sampleHeatClocks h b.val bs

theorem sampleHeatClocks_ordered (h : ℝ → ℝ) {a : ℝ}
    (as : List PositiveMass) (ha : MassOrdered a as) :
    OrderedSteps a (heatSteps (ι := Fin 1) (sampleHeatClocks h a as)) := by
  induction as generalizing a with
  | nil => exact ha
  | cons b bs ih =>
    exact ⟨ha.1, ha.2.1, b.property, ih ha.2.2⟩

theorem sampleHeatClocks_duration (h : ℝ → ℝ)
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) {a : ℝ}
    (as : List PositiveMass) (ha : MassOrdered a as) :
    h a + scheduleDuration (sampleHeatClocks h a as) = h (partitionEnd a as) := by
  induction as generalizing a with
  | nil => simp [sampleHeatClocks, scheduleDuration, partitionEnd]
  | cons b bs ih =>
    have hab := hh (massOrdered_bounds ha) (massOrdered_bounds ha.2.2) ha.2.1
    have hit := ih ha.2.2
    simp only [sampleHeatClocks, scheduleDuration, NNReal.coe_add,
      Real.coe_toNNReal _ (sub_nonneg.mpr hab), partitionEnd]
    linarith

theorem sampleHeatClocks_quantile (h : ℝ → ℝ)
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) {a : ℝ}
    (as : List PositiveMass) (ha : MassOrdered a as) (u : ℝ) :
    scheduleRadiusQuantile (h a) (sampleHeatClocks h a as) u =
      partitionSample h a as u := by
  induction as generalizing a with
  | nil => simp [sampleHeatClocks, scheduleRadiusQuantile, stepClockFunction,
      heatSteps, partitionSample_nil]
  | cons b bs ih =>
    have hab := hh (massOrdered_bounds ha) (massOrdered_bounds ha.2.2) ha.2.1
    rw [sampleHeatClocks, scheduleRadiusQuantile_cons, partitionSample_cons]
    by_cases hu : b.val ≤ u
    · rw [if_pos hu, if_neg (not_lt.mpr hu)]
      simp only [Real.coe_toNNReal _ (sub_nonneg.mpr hab)]
      have he : h a + (h b.val - h a) = h b.val := by ring
      rw [he]
      exact ih ha.2.2
    · rw [if_neg hu, if_pos (lt_of_not_ge hu)]
      exact scheduleRadiusQuantile_before (sampleHeatClocks_ordered h bs ha.2.2)
        (lt_of_not_ge hu)

theorem sampleHeatClocks_steps (h : ℝ → ℝ)
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) {a : ℝ}
    (as : List PositiveMass) (ha : MassOrdered a as) (ha0 : 0 ≤ h a) :
    heatSteps (ι := Fin 1) (sampleHeatClocks h a as) =
      sampleClockSteps (fun u _ => Real.toNNReal (h u)) a as := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have hab := hh (massOrdered_bounds ha) (massOrdered_bounds ha.2.2) ha.2.1
    have hb0 := ha0.trans hab
    simp only [sampleHeatClocks, heatSteps, sampleClockSteps, List.map_cons]
    congr 1
    · congr 1
      funext i
      apply NNReal.coe_injective
      rw [NNReal.coe_sub, Real.coe_toNNReal _ (sub_nonneg.mpr hab),
        Real.coe_toNNReal _ hb0, Real.coe_toNNReal _ ha0]
      exact Real.toNNReal_mono hab
    · exact ih ha.2.2 hb0

theorem scalarSamplePressure_eq_field (h : ℝ → ℝ)
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) (h0 : 0 ≤ h 0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    scalarSchedulePressure (h 0) (sampleHeatClocks h 0 as) =
      scalarFieldPressure as (fun j => h (partitionPoint 0 as j)) := by
  unfold scalarSchedulePressure
  rw [sampleHeatClocks_steps h hh as ha h0]
  change sampledDisorderPressure (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature
    (fun _ => 1) (fun (u : ℝ) (_ : Fin 1) => Real.toNNReal (h u)) as 0 = _
  rw [sampledDisorderPressure_eq _ _ _ _ (fun _ => toNNReal_monotoneOn hh) as ha]
  unfold scalarFieldPressure
  congr 2
  funext j i
  have hj := partitionPoint_mem as ha j
  exact Real.coe_toNNReal _ (h0.trans (hh (by norm_num) hj hj.1))

theorem partitionSample_unit_bounds (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    {mesh : ℝ} (as : List PositiveMass) (ha : MassOrdered 0 as)
    (hm : PartitionMesh mesh 0 as) :
    ∀ u ∈ Icc (0 : ℝ) 1, partitionSample q 0 as u ∈ Icc (0 : ℝ) 1 := by
  intro u hu
  have hs := partitionSample_id_bounds as ha hm hu
  rw [partitionSample_comp q]
  exact hqb _ ⟨hs.1, hs.2.1.trans hu.2⟩

theorem partitionSample_quantile_le (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    {mesh : ℝ} (as : List PositiveMass) (ha : MassOrdered 0 as)
    (hm : PartitionMesh mesh 0 as) :
    ∀ u ∈ Icc (0 : ℝ) 1, partitionSample q 0 as u ≤ q u := by
  intro u hu
  have hs := partitionSample_id_bounds as ha hm hu
  rw [partitionSample_comp q]
  exact hq ⟨hs.1, hs.2.1.trans hu.2⟩ hu hs.2.1

theorem partitionSample_quantile_monotone (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    Monotone (partitionSample q 0 as) := by
  have he : scheduleRadiusQuantile (q 0) (sampleHeatClocks q 0 as) =
      partitionSample q 0 as := by
    funext u
    exact sampleHeatClocks_quantile q hq as ha u
  rw [← he]
  exact scheduleRadiusQuantile_monotone _ _

theorem sampleHeatClocks_normalized_quantile {T : ℝ} (hT : 0 < T)
    (q : ℝ → ℝ) (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    normalizedScheduleQuantile T (T * q 0) (sampleHeatClocks (fun u => T * q u) 0 as) =
      partitionSample q 0 as := by
  funext u
  unfold normalizedScheduleQuantile
  rw [sampleHeatClocks_quantile _
    (fun _ hu _ hv huv => mul_le_mul_of_nonneg_left (hq hu hv huv) hT.le) as ha,
    partitionSample_comp (fun v => T * q v), partitionSample_comp q]
  exact mul_div_cancel_left₀ _ hT.ne'

theorem quantileMassProfile_congr {q r : ℝ → ℝ}
    {hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1}
    {hrb : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1} (he : q = r) :
    quantileMassProfile q hqb = quantileMassProfile r hrb := by
  cases he
  rfl

theorem scalar_sample_value_eq_ordered_pressure (n : ℕ) (hn : 0 < n)
    {T mesh : ℝ} (hT : 0 < T) (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (hm : PartitionMesh mesh 0 as) :
    scalarParisiValue hT (quantileMassProfile (partitionSample q 0 as)
      (partitionSample_unit_bounds q hqb as ha hm)) =
      orderedSKPressure n as (fun _ => 0)
        (fun j => T * q (partitionPoint 0 as j)) 0 +
        T / 4 * (∫ u in (0 : ℝ)..1, partitionSample q 0 as u ^ 2) := by
  let h : ℝ → ℝ := fun u => T * q u
  have hh : MonotoneOn h (Icc (0 : ℝ) 1) :=
    fun _ hu _ hv huv => mul_le_mul_of_nonneg_left (hq hu hv huv) hT.le
  have h0 : 0 ≤ h 0 := mul_nonneg hT.le (hqb 0 (by norm_num)).1
  have ht : h 0 + scheduleDuration (sampleHeatClocks h 0 as) ≤ T := by
    rw [sampleHeatClocks_duration h hh as ha]
    exact mul_le_of_le_one_right hT.le (hqb _ ha.end_bounds).2
  have hv := scalar_schedule_value_eq_pressure hT h0 (sampleHeatClocks h 0 as) ht
    (sampleHeatClocks_ordered h as ha)
  rw [scalarSamplePressure_eq_field h hh h0 as ha] at hv
  have he := sampleHeatClocks_normalized_quantile hT q hq as ha
  change normalizedScheduleQuantile T (h 0) (sampleHeatClocks h 0 as) = _ at he
  have hprofile : quantileMassProfile
      (normalizedScheduleQuantile T (h 0) (sampleHeatClocks h 0 as))
      (normalizedScheduleQuantile_bounds hT h0 (sampleHeatClocks h 0 as) ht) =
      quantileMassProfile (partitionSample q 0 as) (partitionSample_unit_bounds q hqb as ha hm) :=
    quantileMassProfile_congr he
  have hint := congrArg (fun f : ℝ → ℝ => ∫ u in (0 : ℝ)..1, f u ^ 2) he
  rw [hprofile, hint] at hv
  rw [orderedSKPressure_pure_field n hn as ha.pairwise ha.members_le_one]
  exact hv

theorem unit_square_integral_l1 (q r : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hr : MonotoneOn r (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (hrb : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1) :
    |(∫ u in (0 : ℝ)..1, q u ^ 2) - (∫ u in (0 : ℝ)..1, r u ^ 2)| ≤
      2 * (∫ u in (0 : ℝ)..1, |q u - r u|) := by
  have hqi : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0 : ℝ) 1) by simpa using hq).intervalIntegrable
  have hri : IntervalIntegrable r volume 0 1 :=
    (show MonotoneOn r (uIcc (0 : ℝ) 1) by simpa using hr).intervalIntegrable
  have hqs : MonotoneOn (fun u => q u ^ 2) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact pow_le_pow_left₀ (hqb u hu).1 (hq hu hv huv) 2
  have hrs : MonotoneOn (fun u => r u ^ 2) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact pow_le_pow_left₀ (hrb u hu).1 (hr hu hv huv) 2
  have hqsi : IntervalIntegrable (fun u => q u ^ 2) volume 0 1 :=
    (show MonotoneOn (fun u => q u ^ 2) (uIcc (0 : ℝ) 1) by simpa using hqs).intervalIntegrable
  have hrsi : IntervalIntegrable (fun u => r u ^ 2) volume 0 1 :=
    (show MonotoneOn (fun u => r u ^ 2) (uIcc (0 : ℝ) 1) by simpa using hrs).intervalIntegrable
  rw [← intervalIntegral.integral_sub hqsi hrsi]
  apply (show |∫ u in (0 : ℝ)..1, q u ^ 2 - r u ^ 2| ≤
    ∫ u in (0 : ℝ)..1, |q u ^ 2 - r u ^ 2| from by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
        (f := fun u => q u ^ 2 - r u ^ 2) (by norm_num : (0 : ℝ) ≤ 1)).trans
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
    (hqsi.sub hrsi).abs ((hqi.sub hri).abs.const_mul 2)
  intro u hu
  exact unit_square_difference_le (hqb u ⟨hu.1.le, hu.2.le⟩) (hrb u ⟨hu.1.le, hu.2.le⟩)

theorem scalar_physical_quantile_value (n : ℕ) (hn : 0 < n)
    {T : ℝ} (hT : 0 < T) (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    scalarParisiValue hT (quantileMassProfile q hqb) =
      physicalScalarQuantileValue n T q := by
  let qs := fun k => partitionSample q 0 (uniformMasses k)
  have hqm : ∀ k, MonotoneOn (qs k) (Icc (0 : ℝ) 1) := fun k =>
    (partitionSample_quantile_monotone q hq _ (uniformMasses_ordered k)).monotoneOn _
  have hqbs : ∀ k, ∀ u ∈ Icc (0 : ℝ) 1, qs k u ∈ Icc (0 : ℝ) 1 := fun k =>
    partitionSample_unit_bounds q hqb _ (uniformMasses_ordered k) (uniformMasses_mesh k)
  have hqs : ∀ k, ∀ u ∈ Icc (0 : ℝ) 1, qs k u ≤ q u := fun k =>
    partitionSample_quantile_le q hq _ (uniformMasses_ordered k) (uniformMasses_mesh k)
  have hl1 : Tendsto (fun k => ∫ u in (0 : ℝ)..1, |qs k u - q u|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ => abs_nonneg _)) _
      (show Tendsto (fun k => ((k + 1 : ℕ) : ℝ)⁻¹ * (q 1 - q 0)) atTop (𝓝 0) from by
        simpa using uniformMasses_mesh_tendsto.mul_const (q 1 - q 0))
    intro k
    simp_rw [abs_sub_comm]
    exact partitionSample_l1_error hq _ (uniformMasses_ordered k) (uniformMasses_mesh k)
  have hscalar : Tendsto (fun k => scalarParisiValue hT (quantileMassProfile (qs k) (hqbs k)))
      atTop (𝓝 (scalarParisiValue hT (quantileMassProfile q hqb))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero (fun _ => abs_nonneg _) (fun k =>
      scalar_quantile_value_ordered_l1 hT _ q (hqm k) hq (hqbs k) hqb (hqs k))
    simpa using hl1.const_mul T
  have hsq : Tendsto (fun k => ∫ u in (0 : ℝ)..1, qs k u ^ 2) atTop
      (𝓝 (∫ u in (0 : ℝ)..1, q u ^ 2)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero (fun _ => abs_nonneg _) (fun k =>
      unit_square_integral_l1 _ q (hqm k) hq (hqbs k) hqb)
    simpa using hl1.const_mul 2
  have hp := orderedSKPressure_samples_tendsto n hn (fun _ => 0) (fun u => T * q u)
    (fun _ _ _ _ _ => le_rfl)
    (fun _ hu _ hv huv => mul_le_mul_of_nonneg_left (hq hu hv huv) hT.le)
    le_rfl (mul_nonneg hT.le (hqb 0 (by norm_num)).1) 0
  apply tendsto_nhds_unique hscalar
  unfold physicalScalarQuantileValue
  apply (hp.add (hsq.const_mul (T / 4))).congr'
  apply Eventually.of_forall
  intro k
  exact (scalar_sample_value_eq_ordered_pressure n hn hT q hq hqb _
    (uniformMasses_ordered k) (uniformMasses_mesh k)).symm

end OAI.SKFluctuations.LaplaceWindowFormalization

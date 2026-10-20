module

public import QuantileLaw

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

attribute [local instance] Measure.Subtype.measureSpace

theorem quantileLaw_integral_id (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    (∫ x : ParisiFinite.OrderPoint, (x : ℝ)
        ∂(quantileLaw q hqb : Measure ParisiFinite.OrderPoint)) =
      ∫ u in (0 : ℝ)..1, q u := by
  unfold quantileLaw
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map_of_stronglyMeasurable (quantileOrderMap_measurable q hq hqb)
      (by fun_prop : StronglyMeasurable (fun x : ParisiFinite.OrderPoint => (x : ℝ)))]
  change (∫ u : ParisiFinite.OrderPoint, q u) = _
  rw [integral_subtype measurableSet_Icc (fun u : ℝ => q u),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

theorem quantileMassProfile_integral (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, (quantileMassProfile q hqb).val t) =
      1 - (∫ u in (0 : ℝ)..1, q u) := by
  let ρ := quantileLaw q hqb
  have hs : Integrable (fun x : ParisiFinite.OrderPoint => (x : ℝ))
      (ρ : Measure ParisiFinite.OrderPoint) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg x.property.1] using x.property.2)
  have hc := ParisiFinite.integral_cdf_mul ρ (continuous_const (y := (1 : ℝ)))
    (by norm_num : (0 : ℝ) ≤ 1) (by intro t ht; norm_num)
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hc
  rw [integral_sub (integrable_const 1) hs, integral_const] at hc
  change (∫ t in (0 : ℝ)..1, (ρ : Measure ParisiFinite.OrderPoint).real
    {x | (x : ℝ) ≤ t}) = _
  rw [hc, quantileLaw_integral_id q hq hqb]
  simp [Measure.real]

theorem quantileMassProfile_antitone (q r : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hr : MonotoneOn r (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (hrb : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1)
    (hqr : ∀ u ∈ Icc (0 : ℝ) 1, q u ≤ r u) (t : ℝ) :
    (quantileMassProfile r hrb).val t ≤ (quantileMassProfile q hqb).val t := by
  rw [quantileMassProfile_cdf q hq hqb, quantileMassProfile_cdf r hr hrb]
  apply measureReal_mono (fun (u : ParisiFinite.OrderPoint) hu => (hqr u u.property).trans hu)

theorem quantileMassProfile_ordered_l1 (q r : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hr : MonotoneOn r (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (hrb : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1)
    (hqr : ∀ u ∈ Icc (0 : ℝ) 1, q u ≤ r u) :
    (∫ t in (0 : ℝ)..1,
        |(quantileMassProfile q hqb).val t - (quantileMassProfile r hrb).val t|) =
      ∫ u in (0 : ℝ)..1, |q u - r u| := by
  have hiq : IntervalIntegrable (quantileMassProfile q hqb).val volume 0 1 :=
    (quantileMassProfile q hqb).property.2.intervalIntegrable
  have hir : IntervalIntegrable (quantileMassProfile r hrb).val volume 0 1 :=
    (quantileMassProfile r hrb).property.2.intervalIntegrable
  have hqi : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0 : ℝ) 1) by simpa using hq).intervalIntegrable
  have hri : IntervalIntegrable r volume 0 1 :=
    (show MonotoneOn r (uIcc (0 : ℝ) 1) by simpa using hr).intervalIntegrable
  calc
    _ = ∫ t in (0 : ℝ)..1,
        (quantileMassProfile q hqb).val t - (quantileMassProfile r hrb).val t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact abs_of_nonneg (sub_nonneg.mpr (quantileMassProfile_antitone q r hq hr hqb hrb hqr t))
    _ = (∫ u in (0 : ℝ)..1, r u) - (∫ u in (0 : ℝ)..1, q u) := by
      rw [intervalIntegral.integral_sub hiq hir, quantileMassProfile_integral q hq hqb,
        quantileMassProfile_integral r hr hrb]
      ring
    _ = ∫ u in (0 : ℝ)..1, r u - q u := by
      rw [intervalIntegral.integral_sub hri hqi]
    _ = ∫ u in (0 : ℝ)..1, |q u - r u| := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro u hu
      dsimp only
      rw [abs_of_nonpos (sub_nonpos.mpr (hqr u ⟨hu.1.le, hu.2.le⟩))]
      ring

theorem scalar_quantile_value_ordered_l1 {T : ℝ} (hT : 0 < T)
    (q r : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hr : MonotoneOn r (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (hrb : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1)
    (hqr : ∀ u ∈ Icc (0 : ℝ) 1, q u ≤ r u) :
    |scalarParisiValue hT (quantileMassProfile q hqb) -
        scalarParisiValue hT (quantileMassProfile r hrb)| ≤
      T * (∫ u in (0 : ℝ)..1, |q u - r u|) := by
  let α := quantileMassProfile q hqb
  let β := quantileMassProfile r hrb
  have hroot := scalarTerminal.nonnegativeProfileValue_L1_comparison
    (fun _ => 1) scalarTerminal_G_bound (rescaledMassProfile α hT)
    (rescaledMassProfile β hT) 0 (NNReal.mk T hT.le) 0
  have hcdf : (∫ s in (0 : ℝ)..T, |α.val (s / T) - β.val (s / T)|) =
      T * (∫ u in (0 : ℝ)..1, |q u - r u|) := by
    rw [intervalIntegral.integral_comp_div (fun z => |α.val z - β.val z|) hT.ne']
    simp only [zero_div, div_self hT.ne', smul_eq_mul]
    rw [quantileMassProfile_ordered_l1 q r hq hr hqb hrb hqr]
  norm_num only [one_pow, Fin.sum_univ_one, NNReal.coe_mk, zero_add] at hroot
  change |_ - _| ≤ (1 : ℝ) / 2 * (∫ s in (0 : ℝ)..T, |α.val (s / T) - β.val (s / T)|) at hroot
  rw [hcdf] at hroot
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
  have hsq : |(∫ u in (0 : ℝ)..1, q u ^ 2) -
      (∫ u in (0 : ℝ)..1, r u ^ 2)| ≤
      2 * (∫ u in (0 : ℝ)..1, |q u - r u|) := by
    rw [← intervalIntegral.integral_sub hqsi hrsi]
    apply (show |∫ u in (0 : ℝ)..1, q u ^ 2 - r u ^ 2| ≤
      ∫ u in (0 : ℝ)..1, |q u ^ 2 - r u ^ 2| from by
        simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
          (f := fun u => q u ^ 2 - r u ^ 2) (by norm_num : (0 : ℝ) ≤ 1)).trans
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (hqsi.sub hrsi).abs ((hqi.sub hri).abs.const_mul 2)
    intro u hu
    exact unit_square_difference_le (hqb u ⟨hu.1.le, hu.2.le⟩)
      (hrb u ⟨hu.1.le, hu.2.le⟩)
  unfold scalarParisiValue
  change |(scalarTerminal.nonnegativeProfileValue (rescaledMassProfile α hT)
    0 (NNReal.mk T hT.le) 0 - T / 2 * scalarPenalty α - T / 4) -
    (scalarTerminal.nonnegativeProfileValue (rescaledMassProfile β hT)
    0 (NNReal.mk T hT.le) 0 - T / 2 * scalarPenalty β - T / 4)| ≤ _
  dsimp only [α, β]
  rw [quantileMassProfile_penalty q hq hqb, quantileMassProfile_penalty r hr hrb]
  have htri := abs_add_le
    (scalarTerminal.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (NNReal.mk T hT.le) 0 -
      scalarTerminal.nonnegativeProfileValue (rescaledMassProfile β hT) 0 (NNReal.mk T hT.le) 0)
    (-(T / 4 * ((∫ u in (0 : ℝ)..1, r u ^ 2) - (∫ u in (0 : ℝ)..1, q u ^ 2))))
  rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ T / 4),
    abs_sub_comm (∫ u in (0 : ℝ)..1, r u ^ 2) (∫ u in (0 : ℝ)..1, q u ^ 2)] at htri
  have heq :
      scalarTerminal.nonnegativeProfileValue (rescaledMassProfile (quantileMassProfile q hqb) hT)
        0 (NNReal.mk T hT.le) 0 - T / 2 * ((1 - (∫ u in (0 : ℝ)..1, q u ^ 2)) / 2) - T / 4 -
      (scalarTerminal.nonnegativeProfileValue (rescaledMassProfile (quantileMassProfile r hrb) hT)
        0 (NNReal.mk T hT.le) 0 - T / 2 * ((1 - (∫ u in (0 : ℝ)..1, r u ^ 2)) / 2) - T / 4) =
      (scalarTerminal.nonnegativeProfileValue (rescaledMassProfile α hT) 0 (NNReal.mk T hT.le) 0 -
        scalarTerminal.nonnegativeProfileValue (rescaledMassProfile β hT) 0 (NNReal.mk T hT.le) 0) -
        T / 4 * ((∫ u in (0 : ℝ)..1, r u ^ 2) - (∫ u in (0 : ℝ)..1, q u ^ 2)) := by
    dsimp [α, β]
    ring
  change |_
    - _| ≤ _
  rw [heq]
  simp only [← sub_eq_add_neg] at htri
  linarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ T / 4)]

end OAI.SKFluctuations.LaplaceWindowFormalization

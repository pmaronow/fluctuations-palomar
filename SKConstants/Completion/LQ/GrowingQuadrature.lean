module

public import SKConstants.Completion.LQ.AdjacentCell
public import SKConstants.Completion.LQ.InformationCell

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal BigOperators Interval
namespace SKConstants.Completion.LQ

def growingEnergySum (r g : ℝ → ℝ) (δ : ℝ≥0) (q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range q,
    posteriorScale r (meshTime δ i) (meshTime δ (i + 1)) *
      queryMean g (meshTime δ (i + 1)) (meshTime δ (i + 2))

def energyReference (r g : ℝ → ℝ) (V : ℝ) : ℝ :=
  ∫ v in 0..V, Real.sqrt (r v) * g v

def growingInformationAll (r k : ℝ → ℝ) (weight : ℝ) (δ : ℝ≥0) (q : ℕ) : ℝ :=
  (weight / 2) * ∑ i ∈ Finset.range (q + 1),
    r (meshTime δ i) * ∫ v in meshTime δ i..meshTime δ (i + 1), k v

def growingInformationQueries (r k : ℝ → ℝ) (weight : ℝ) (δ : ℝ≥0) (q : ℕ) : ℝ :=
  (weight / 2) * ∑ i ∈ Finset.range q,
    r (meshTime δ (i + 1)) * ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), k v

def informationReference (r k : ℝ → ℝ) (weight V : ℝ) : ℝ :=
  (weight / 2) * ∫ v in 0..V, r v * k v

lemma energy_integrand_bounds {r g : ℝ → ℝ} {v : ℝ}
    (hr : 0 ≤ r v) (hg : 0 ≤ g v ∧ g v ≤ Real.sqrt (r v)) :
    0 ≤ Real.sqrt (r v) * g v ∧ Real.sqrt (r v) * g v ≤ r v := by
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hg.1, ?_⟩
  calc
    _ ≤ Real.sqrt (r v) * Real.sqrt (r v) :=
      mul_le_mul_of_nonneg_left hg.2 (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt hr

lemma auxiliary_energy_bound (r g : ℝ → ℝ) (δ : ℝ≥0)
    (hr0 : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hrmono : AntitoneOn r (Ici 0))
    (hg : ∀ t, 0 ≤ t → 0 ≤ g t ∧ g t ≤ Real.sqrt (r t)) :
    |energyReference r g δ| ≤ r 0 * (δ : ℝ) := by
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (δ : ℝ)) (f := fun v => Real.sqrt (r v) * g v)
    (C := r 0) (by
      intro v hv
      rw [uIoc_of_le δ.coe_nonneg] at hv
      have hv0 := hv.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg (energy_integrand_bounds (hr0 v hv0) (hg v hv0)).1]
      exact (energy_integrand_bounds (hr0 v hv0) (hg v hv0)).2.trans
        (hrmono le_rfl hv0 hv0))
  simpa only [energyReference, Real.norm_eq_abs, sub_zero, abs_of_nonneg δ.coe_nonneg] using H

theorem growing_energy_error (r g : ℝ → ℝ) (A : ℝ) (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ)
    (hr0 : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hrmono : AntitoneOn r (Ici 0))
    (hrdrop : ∀ s t, 0 ≤ s → s ≤ t → r s - r t ≤ 2 * r s * (t - s))
    (htail : ∀ t, 0 ≤ t → r t ≤ A * Real.exp (-t / 2))
    (hg : ∀ t, 0 ≤ t → 0 ≤ g t ∧ g t ≤ Real.sqrt (r t))
    (hrint : IntervalIntegrable r volume 0 (meshTime δ (q + 1)))
    (hgint : IntervalIntegrable g volume 0 (meshTime δ (q + 1)))
    (heint : IntervalIntegrable (fun v => Real.sqrt (r v) * g v) volume 0 (meshTime δ (q + 1)))
    (hsmall : ∀ i < q + 1, meshDuration δ i ≤ 1) :
    |growingEnergySum r g δ q - energyReference r g (meshTime δ (q + 1))| ≤
      (r 0 + 33 * A * Real.exp (1 / 2)) * (δ : ℝ) := by
  have hA : 0 ≤ A := by
    have H := htail 0 le_rfl
    simp only [neg_zero, zero_div, Real.exp_zero, mul_one] at H
    exact (hr0 0 le_rfl).trans H
  have hcell (i : ℕ) (hi : i < q) :
      |posteriorScale r (meshTime δ i) (meshTime δ (i + 1)) *
          queryMean g (meshTime δ (i + 1)) (meshTime δ (i + 2)) -
        ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v| ≤
      (33 / 8 : ℝ) * A * Real.exp (1 / 2) * (δ : ℝ)^2 := by
    have H := growing_energy_cell_error r g δ hδ i hr0 hrmono hrdrop
      (intervalIntegrable_meshCell hrint (by omega))
      (intervalIntegrable_meshCell hgint (i := i + 1) (by omega))
      (intervalIntegrable_meshCell heint (i := i + 1) (by omega))
      (fun v hv => hg v ((meshTime_nonneg δ (i + 1)).trans hv.1))
    have Hgeom := mesh_adjacent_profile_square_le r A hA δ i
      (htail _ (meshTime_nonneg δ i)) (hsmall i (by omega))
    calc
      _ ≤ (33 / 8 : ℝ) * (r (meshTime δ i) * meshDuration δ (i + 1)^2) := by
        convert H using 1
        ring
      _ ≤ (33 / 8 : ℝ) * (A * Real.exp (1 / 2) * (δ : ℝ)^2) :=
        mul_le_mul_of_nonneg_left Hgeom (by norm_num)
      _ = _ := by ring
  have hcount : (q : ℝ) * (δ : ℝ) ≤ 8 := by
    have H := mesh_count_mul δ hδ (q + 1) hsmall
    have hq : (q : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast Nat.le_succ q
    exact (mul_le_mul_of_nonneg_right hq δ.coe_nonneg).trans H
  have hsum := Finset.abs_sum_le_sum_abs
    (fun i => posteriorScale r (meshTime δ i) (meshTime δ (i + 1)) *
        queryMean g (meshTime δ (i + 1)) (meshTime δ (i + 2)) -
      ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v)
    (Finset.range q)
  have hsum' : |growingEnergySum r g δ q -
      ∑ i ∈ Finset.range q, ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v| ≤
        33 * A * Real.exp (1 / 2) * (δ : ℝ) := by
    calc
      _ = |∑ i ∈ Finset.range q,
          (posteriorScale r (meshTime δ i) (meshTime δ (i + 1)) *
              queryMean g (meshTime δ (i + 1)) (meshTime δ (i + 2)) -
            ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v)| := by
        rw [Finset.sum_sub_distrib]; rfl
      _ ≤ _ := hsum
      _ ≤ ∑ _i ∈ Finset.range q, (33 / 8 : ℝ) * A * Real.exp (1 / 2) * (δ : ℝ)^2 :=
        Finset.sum_le_sum (fun i hi => hcell i (Finset.mem_range.mp hi))
      _ = ((33 / 8 : ℝ) * A * Real.exp (1 / 2) * (δ : ℝ)) * ((q : ℝ) * (δ : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ ((33 / 8 : ℝ) * A * Real.exp (1 / 2) * (δ : ℝ)) * 8 :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = _ := by ring
  have hsplit := mesh_integral_split δ q heint
  change energyReference r g (meshTime δ (q + 1)) = energyReference r g δ + _ at hsplit
  rw [hsplit]
  calc
    _ ≤ |growingEnergySum r g δ q -
        ∑ i ∈ Finset.range q, ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v| +
          |energyReference r g δ| := by
      convert abs_sub_le (growingEnergySum r g δ q)
        (∑ i ∈ Finset.range q, ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v)
        (energyReference r g δ +
          ∑ i ∈ Finset.range q, ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v) using 1
      rw [show (∑ i ∈ Finset.range q, ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v) -
          (energyReference r g δ + ∑ i ∈ Finset.range q, ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v) =
          -energyReference r g δ by ring, abs_neg]
    _ ≤ 33 * A * Real.exp (1 / 2) * (δ : ℝ) + r 0 * (δ : ℝ) :=
      add_le_add hsum' (auxiliary_energy_bound r g δ hr0 hrmono hg)
    _ = _ := by ring

theorem growing_information_error (r k : ℝ → ℝ) (weight A : ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ) (hw : 0 ≤ weight)
    (hrmono : AntitoneOn r (Ici 0))
    (hrdrop : ∀ s t, 0 ≤ s → s ≤ t → r s - r t ≤ 2 * r s * (t - s))
    (htail : ∀ t, 0 ≤ t → r t ≤ A * Real.exp (-t / 2))
    (hk : ∀ t, 0 ≤ t → 0 ≤ k t ∧ k t ≤ 1)
    (hkint : IntervalIntegrable k volume 0 (meshTime δ (q + 1)))
    (hrkint : IntervalIntegrable (fun v => r v * k v) volume 0 (meshTime δ (q + 1)))
    (hsmall : ∀ i < q + 1, meshDuration δ i ≤ 1) :
    0 ≤ growingInformationAll r k weight δ q - informationReference r k weight (meshTime δ (q + 1)) ∧
      growingInformationAll r k weight δ q - informationReference r k weight (meshTime δ (q + 1)) ≤
        4 * weight * A * (δ : ℝ) := by
  let err := fun i => (weight / 2) *
    (r (meshTime δ i) * (∫ v in meshTime δ i..meshTime δ (i + 1), k v) -
      ∫ v in meshTime δ i..meshTime δ (i + 1), r v * k v)
  have hcell (i : ℕ) (hi : i < q + 1) :
      0 ≤ err i ∧ err i ≤ (weight / 2) * A * (δ : ℝ)^2 := by
    have H := information_cell_bounds r k weight (meshTime δ i) (meshTime δ (i + 1)) hw
      (meshTime_mono δ (Nat.le_succ i)) (intervalIntegrable_meshCell hkint hi)
      (intervalIntegrable_meshCell hrkint hi) (fun v hv =>
        ⟨sub_nonneg.mpr (hrmono (meshTime_nonneg δ i) ((meshTime_nonneg δ i).trans hv.1) hv.1),
          hrdrop _ v (meshTime_nonneg δ i) hv.1⟩)
      (fun v hv => hk v ((meshTime_nonneg δ i).trans hv.1))
    have hlen : meshTime δ (i + 1) - meshTime δ i = meshDuration δ i :=
      growingQueryTime_sub δ i
    rw [hlen] at H
    refine ⟨H.1, H.2.trans ?_⟩
    have HG := mesh_profile_square_le r A δ i (htail _ (meshTime_nonneg δ i))
    convert mul_le_mul_of_nonneg_left HG (by positivity : 0 ≤ weight / 2) using 1 <;> ring
  have heq : growingInformationAll r k weight δ q - informationReference r k weight (meshTime δ (q + 1)) =
      ∑ i ∈ Finset.range (q + 1), err i := by
    have hs := intervalIntegral.sum_integral_adjacent_intervals (a := meshTime δ) (n := q + 1)
      (fun i hi => intervalIntegrable_meshCell hrkint hi)
    rw [meshTime_zero] at hs
    unfold growingInformationAll informationReference err
    rw [← hs, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [heq]
  refine ⟨Finset.sum_nonneg (fun i hi => (hcell i (Finset.mem_range.mp hi)).1), ?_⟩
  calc
    _ ≤ ∑ _i ∈ Finset.range (q + 1), (weight / 2) * A * (δ : ℝ)^2 :=
      Finset.sum_le_sum (fun i hi => (hcell i (Finset.mem_range.mp hi)).2)
    _ = ((weight / 2) * A * (δ : ℝ)) * (((q + 1 : ℕ) : ℝ) * (δ : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ ((weight / 2) * A * (δ : ℝ)) * 8 := by
      have hA : 0 ≤ A := by
        have H := hrdrop 0 1 le_rfl (by norm_num)
        have HM := hrmono (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show (1 : ℝ) ∈ Ici 0 by norm_num) (by norm_num)
        have Htail := htail 0 le_rfl
        simp only [neg_zero, zero_div, Real.exp_zero, mul_one] at Htail
        nlinarith
      exact mul_le_mul_of_nonneg_left (mesh_count_mul δ hδ (q + 1) hsmall) (by positivity)
    _ = _ := by ring

theorem growing_information_auxiliary (r k : ℝ → ℝ) (weight : ℝ) (δ : ℝ≥0) (q : ℕ) :
    growingInformationAll r k weight δ q - growingInformationQueries r k weight δ q =
      (weight / 2) * r 0 * ∫ v in 0..(δ : ℝ), k v := by
  unfold growingInformationAll growingInformationQueries
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.reduceAdd, meshTime_zero, meshTime_one, Nat.add_assoc]
  ring

theorem growing_information_auxiliary_bounds (r k : ℝ → ℝ) (weight : ℝ)
    (δ : ℝ≥0) (q : ℕ) (hw : 0 ≤ weight) (hr : 0 ≤ r 0)
    (hki : IntervalIntegrable k volume 0 δ)
    (hk : ∀ t ∈ Icc 0 (δ : ℝ), 0 ≤ k t ∧ k t ≤ 1) :
    0 ≤ growingInformationAll r k weight δ q - growingInformationQueries r k weight δ q ∧
      growingInformationAll r k weight δ q - growingInformationQueries r k weight δ q ≤
        (weight / 2) * r 0 * (δ : ℝ) := by
  rw [growing_information_auxiliary]
  constructor
  · exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg δ.coe_nonneg (fun t ht => (hk t ht).1))
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    have H := intervalIntegral.integral_mono_on δ.coe_nonneg hki
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 δ)
      (fun t ht => (hk t ht).2)
    simpa using H

theorem growing_information_queries_error (r k : ℝ → ℝ) (weight A : ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (q : ℕ) (hw : 0 ≤ weight) (hr : 0 ≤ r 0)
    (hrmono : AntitoneOn r (Ici 0))
    (hrdrop : ∀ s t, 0 ≤ s → s ≤ t → r s - r t ≤ 2 * r s * (t - s))
    (htail : ∀ t, 0 ≤ t → r t ≤ A * Real.exp (-t / 2))
    (hk : ∀ t, 0 ≤ t → 0 ≤ k t ∧ k t ≤ 1)
    (hkint : IntervalIntegrable k volume 0 (meshTime δ (q + 1)))
    (hrkint : IntervalIntegrable (fun v => r v * k v) volume 0 (meshTime δ (q + 1)))
    (hsmall : ∀ i < q + 1, meshDuration δ i ≤ 1) :
    |growingInformationQueries r k weight δ q - informationReference r k weight (meshTime δ (q + 1))| ≤
      (4 * weight * A + (weight / 2) * r 0) * (δ : ℝ) := by
  have H := growing_information_error r k weight A δ hδ q hw hrmono hrdrop htail hk hkint hrkint hsmall
  have hki : IntervalIntegrable k volume 0 δ := by
    simpa only [Nat.zero_add, meshTime_zero, meshTime_one] using
      intervalIntegrable_meshCell hkint (i := 0) (by omega)
  have HC := growing_information_auxiliary_bounds r k weight δ q hw hr hki
    (fun t ht => hk t ht.1)
  have hA : 0 ≤ A := by
    have HA := htail 0 le_rfl
    simp only [neg_zero, zero_div, Real.exp_zero, mul_one] at HA
    exact hr.trans HA
  have hC : 0 ≤ 4 * weight * A * (δ : ℝ) := by positivity
  have haux : 0 ≤ (weight / 2) * r 0 * (δ : ℝ) := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith only [H.1, H.2, HC.1, HC.2, hC, haux]

end SKConstants.Completion.LQ

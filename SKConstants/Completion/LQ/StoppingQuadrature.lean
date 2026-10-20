module

public import SKConstants.Completion.LQ.GrowingQuadrature

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal BigOperators Interval
namespace SKConstants.Completion.LQ

theorem energy_overshoot (r g : ℝ → ℝ) {T V : ℝ} (hT : 0 ≤ T) (hTV : T ≤ V)
    (hr0 : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hrmono : AntitoneOn r (Ici 0))
    (hg : ∀ t, 0 ≤ t → 0 ≤ g t ∧ g t ≤ Real.sqrt (r t))
    (hei : IntervalIntegrable (fun v => Real.sqrt (r v) * g v) volume 0 V) :
    0 ≤ energyReference r g V - energyReference r g T ∧
      energyReference r g V - energyReference r g T ≤ r T * (V - T) := by
  have heT : IntervalIntegrable (fun v => Real.sqrt (r v) * g v) volume 0 T :=
    hei.mono_set (by rw [uIcc_of_le hT, uIcc_of_le (hT.trans hTV)]; exact Icc_subset_Icc le_rfl hTV)
  have heTV := hei.symm.trans heT
  have hs := intervalIntegral.integral_interval_sub_left hei heT
  unfold energyReference
  rw [hs]
  constructor
  · exact intervalIntegral.integral_nonneg hTV
      (fun v hv => (energy_integrand_bounds (hr0 v (hT.trans hv.1)) (hg v (hT.trans hv.1))).1)
  · have H := intervalIntegral.integral_mono_on hTV heTV.symm intervalIntegrable_const (fun v hv =>
      (energy_integrand_bounds (hr0 v (hT.trans hv.1)) (hg v (hT.trans hv.1))).2.trans
        (hrmono hT (hT.trans hv.1) hv.1))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using H

theorem information_overshoot (r k : ℝ → ℝ) (weight : ℝ) (hw : 0 ≤ weight)
    {T V : ℝ} (hT : 0 ≤ T) (hTV : T ≤ V)
    (hr0 : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hrmono : AntitoneOn r (Ici 0))
    (hk : ∀ t, 0 ≤ t → 0 ≤ k t ∧ k t ≤ 1)
    (hrki : IntervalIntegrable (fun v => r v * k v) volume 0 V) :
    0 ≤ informationReference r k weight V - informationReference r k weight T ∧
      informationReference r k weight V - informationReference r k weight T ≤
        (weight / 2) * r T * (V - T) := by
  have hiT : IntervalIntegrable (fun v => r v * k v) volume 0 T :=
    hrki.mono_set (by rw [uIcc_of_le hT, uIcc_of_le (hT.trans hTV)]; exact Icc_subset_Icc le_rfl hTV)
  have hiTV := hrki.symm.trans hiT
  have hs := intervalIntegral.integral_interval_sub_left hrki hiT
  unfold informationReference
  rw [← mul_sub, hs]
  constructor
  · exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hTV
      (fun v hv => mul_nonneg (hr0 v (hT.trans hv.1)) (hk v (hT.trans hv.1)).1))
  · have H : (∫ v in T..V, r v * k v) ≤ r T * (V - T) := by
      have H' := intervalIntegral.integral_mono_on hTV hiTV.symm intervalIntegrable_const
        (fun v hv => (mul_le_of_le_one_right (hr0 v (hT.trans hv.1)) (hk v (hT.trans hv.1)).2).trans
          (hrmono hT (hT.trans hv.1) hv.1))
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using H'
    convert mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ weight / 2) using 1
    ring

lemma weighted_overshoot_scale (r : ℝ → ℝ) (A : ℝ) (δ : ℝ≥0) (T : ℝ)
    (htail : r T ≤ A * Real.exp (-T / 2)) :
    r T * (δ : ℝ) * Real.exp (T / 4) ≤ A * (δ : ℝ) * Real.exp (-T / 4) := by
  calc
    _ ≤ (A * Real.exp (-T / 2)) * (δ : ℝ) * Real.exp (T / 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htail δ.coe_nonneg) (Real.exp_pos _).le
    _ = A * (δ : ℝ) * (Real.exp (-T / 2) * Real.exp (T / 4)) := by ring
    _ = _ := by rw [← Real.exp_add, show -T / 2 + T / 4 = -T / 4 by ring]

theorem growing_stopped_energy_error (r g : ℝ → ℝ) (A : ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (T : ℝ≥0) (hT : 0 < T)
    (hscale : (δ : ℝ) * Real.exp ((T : ℝ) / 4) ≤ 1)
    (hr0 : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hrmono : AntitoneOn r (Ici 0))
    (hrdrop : ∀ s t, 0 ≤ s → s ≤ t → r s - r t ≤ 2 * r s * (t - s))
    (htail : ∀ t, 0 ≤ t → r t ≤ A * Real.exp (-t / 2))
    (hg : ∀ t, 0 ≤ t → 0 ≤ g t ∧ g t ≤ Real.sqrt (r t))
    (hrint : IntervalIntegrable r volume 0 (meshTime δ (growingQueryStop δ hδ T)))
    (hgint : IntervalIntegrable g volume 0 (meshTime δ (growingQueryStop δ hδ T)))
    (heint : IntervalIntegrable (fun v => Real.sqrt (r v) * g v) volume 0
      (meshTime δ (growingQueryStop δ hδ T))) :
    |growingEnergySum r g δ (growingQueryStop δ hδ T - 1) - energyReference r g T| ≤
      (r 0 + 33 * A * Real.exp (1 / 2)) * (δ : ℝ) +
        r T * (δ : ℝ) * Real.exp ((T : ℝ) / 4) := by
  obtain ⟨hK, _hcount, hreach, hover, hcell⟩ := mesh_stop_geometry δ hδ T hT hscale
  have HE := growing_energy_error r g A δ hδ (growingQueryStop δ hδ T - 1) hr0 hrmono hrdrop htail hg
    (by simpa only [hK] using hrint) (by simpa only [hK] using hgint)
    (by simpa only [hK] using heint) (by
      intro i hi
      rw [hK] at hi
      exact (hcell i hi).trans hscale)
  rw [hK] at HE
  have HO := energy_overshoot r g T.coe_nonneg hreach hr0 hrmono hg heint
  have HO' : |energyReference r g (meshTime δ (growingQueryStop δ hδ T)) - energyReference r g T| ≤
      r T * (δ : ℝ) * Real.exp ((T : ℝ) / 4) := by
    rw [abs_of_nonneg HO.1]
    calc
      _ ≤ r T * (meshTime δ (growingQueryStop δ hδ T) - T) := HO.2
      _ ≤ r T * ((δ : ℝ) * Real.exp ((T : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (by linarith) (hr0 T T.coe_nonneg)
      _ = _ := by ring
  exact (abs_sub_le _ (energyReference r g (meshTime δ (growingQueryStop δ hδ T))) _).trans
    (add_le_add HE HO')

theorem growing_stopped_information_error (r k : ℝ → ℝ) (weight A : ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (T : ℝ≥0) (hT : 0 < T)
    (hscale : (δ : ℝ) * Real.exp ((T : ℝ) / 4) ≤ 1) (hw : 0 ≤ weight)
    (hr0 : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hrmono : AntitoneOn r (Ici 0))
    (hrdrop : ∀ s t, 0 ≤ s → s ≤ t → r s - r t ≤ 2 * r s * (t - s))
    (htail : ∀ t, 0 ≤ t → r t ≤ A * Real.exp (-t / 2))
    (hk : ∀ t, 0 ≤ t → 0 ≤ k t ∧ k t ≤ 1)
    (hkint : IntervalIntegrable k volume 0 (meshTime δ (growingQueryStop δ hδ T)))
    (hrkint : IntervalIntegrable (fun v => r v * k v) volume 0
      (meshTime δ (growingQueryStop δ hδ T))) :
    0 ≤ growingInformationAll r k weight δ (growingQueryStop δ hδ T - 1) - informationReference r k weight T ∧
      growingInformationAll r k weight δ (growingQueryStop δ hδ T - 1) - informationReference r k weight T ≤
        4 * weight * A * (δ : ℝ) +
          (weight / 2) * r T * (δ : ℝ) * Real.exp ((T : ℝ) / 4) := by
  obtain ⟨hK, _hcount, hreach, hover, hcell⟩ := mesh_stop_geometry δ hδ T hT hscale
  have HI := growing_information_error r k weight A δ hδ (growingQueryStop δ hδ T - 1) hw
    hrmono hrdrop htail hk (by simpa only [hK] using hkint) (by simpa only [hK] using hrkint) (by
      intro i hi
      rw [hK] at hi
      exact (hcell i hi).trans hscale)
  rw [hK] at HI
  have HO := information_overshoot r k weight hw T.coe_nonneg hreach hr0 hrmono hk hrkint
  have HO' : informationReference r k weight (meshTime δ (growingQueryStop δ hδ T)) -
      informationReference r k weight T ≤ (weight / 2) * r T * (δ : ℝ) * Real.exp ((T : ℝ) / 4) := by
    calc
      _ ≤ (weight / 2) * r T * (meshTime δ (growingQueryStop δ hδ T) - T) := HO.2
      _ ≤ (weight / 2) * r T * ((δ : ℝ) * Real.exp ((T : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by positivity) (hr0 T T.coe_nonneg))
      _ = _ := by ring
  constructor <;> linarith [HI.1, HI.2, HO.1]

end SKConstants.Completion.LQ

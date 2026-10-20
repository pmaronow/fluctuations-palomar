module

public import PureFieldFactorization
public import SKFluctuationsOAI.Probability.SKFluctuations.RealSKPressureL1

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def mixedQuantile (T : ℝ) (e r z : ℝ → ℝ) (u : ℝ) : ℝ :=
  (e u * r u + (T - e u) * z u) / T

def physicalScalarQuantileValue (n : ℕ) (T : ℝ) (r : ℝ → ℝ) : ℝ :=
  realOrderedSKPathPressure n (fun _ => 0) (fun u => T * r u) 0 +
    T / 4 * (∫ u in (0 : ℝ)..1, r u ^ 2)

def physicalJointQuantileValue (n : ℕ) (T : ℝ) (e r z : ℝ → ℝ) : ℝ :=
  realOrderedSKPathPressure n (fun _ => 0)
    (fun u => e u * r u + (T - e u) * z u) 0 +
      (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..1,
        e u * r u ^ 2 + (T - e u) * z u ^ 2)

theorem mixedQuantile_square_completion {T e r z : ℝ} (hT : T ≠ 0) :
    e * r ^ 2 + (T - e) * z ^ 2 =
      T * ((e * r + (T - e) * z) / T) ^ 2 +
        e * (T - e) / T * (r - z) ^ 2 := by
  field_simp
  ring

theorem mixedQuantile_unit_bounds {T e r z : ℝ} (hT : 0 < T)
    (he : e ∈ Icc (0 : ℝ) T) (hr : r ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    (e * r + (T - e) * z) / T ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (add_nonneg (mul_nonneg he.1 hr.1)
      (mul_nonneg (sub_nonneg.mpr he.2) hz.1)) hT.le
  · apply (div_le_one hT).mpr
    nlinarith [mul_le_mul_of_nonneg_left hr.2 he.1,
      mul_le_mul_of_nonneg_left hz.2 (sub_nonneg.mpr he.2)]

theorem physical_joint_square_completion (n : ℕ) {T : ℝ} (hT : T ≠ 0)
    (e r z : ℝ → ℝ)
    (hiq : IntervalIntegrable (fun u => mixedQuantile T e r z u ^ 2) volume 0 1)
    (hid : IntervalIntegrable (fun u => e u * (T - e u) / T * (r u - z u) ^ 2)
      volume 0 1) :
    physicalJointQuantileValue n T e r z =
      physicalScalarQuantileValue n T (mixedQuantile T e r z) +
        (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..1,
          e u * (T - e u) / T * (r u - z u) ^ 2) := by
  have hmix : (fun u => T * mixedQuantile T e r z u) =
      fun u => e u * r u + (T - e u) * z u := by
    funext u
    simp [mixedQuantile, mul_div_cancel₀ _ hT]
  have hs : (∫ u in (0 : ℝ)..1, e u * r u ^ 2 + (T - e u) * z u ^ 2) =
      T * (∫ u in (0 : ℝ)..1, mixedQuantile T e r z u ^ 2) +
        ∫ u in (0 : ℝ)..1, e u * (T - e u) / T * (r u - z u) ^ 2 := by
    calc
      _ = ∫ u in (0 : ℝ)..1,
          T * mixedQuantile T e r z u ^ 2 +
            e u * (T - e u) / T * (r u - z u) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro u _
        exact mixedQuantile_square_completion hT
      _ = _ := by
        rw [intervalIntegral.integral_add (hiq.const_mul T) hid,
          intervalIntegral.integral_const_mul]
  unfold physicalJointQuantileValue physicalScalarQuantileValue
  rw [hmix, hs]
  ring

theorem physical_joint_coercive (n : ℕ) {T c : ℝ} (hT : 0 < T) (hc : 0 ≤ c)
    (e r z : ℝ → ℝ)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, c ≤ e u)
    (hb : ∀ u ∈ Icc (0 : ℝ) 1, c ≤ T - e u)
    (hiq : IntervalIntegrable (fun u => mixedQuantile T e r z u ^ 2) volume 0 1)
    (hid : IntervalIntegrable (fun u => e u * (T - e u) / T * (r u - z u) ^ 2)
      volume 0 1)
    (hirz : IntervalIntegrable (fun u => (r u - z u) ^ 2) volume 0 1) :
    physicalScalarQuantileValue n T (mixedQuantile T e r z) +
      c ^ 2 / (4 * T) * (∫ u in (0 : ℝ)..1, (r u - z u) ^ 2) ≤
        physicalJointQuantileValue n T e r z := by
  rw [physical_joint_square_completion n hT.ne' e r z hiq hid]
  have hh : c ^ 2 / T * (∫ u in (0 : ℝ)..1, (r u - z u) ^ 2) ≤
      ∫ u in (0 : ℝ)..1, e u * (T - e u) / T * (r u - z u) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (hirz.const_mul _) hid
    intro u hu
    have hui : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply div_le_div_of_nonneg_right _ hT.le
    simpa only [pow_two] using mul_le_mul (he u hui) (hb u hui)
      hc (hc.trans (he u hui))
  have heq : c ^ 2 / (4 * T) = (1 / 4 : ℝ) * (c ^ 2 / T) := by
    field_simp
  rw [heq, mul_assoc]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hh
    (by norm_num : (0 : ℝ) ≤ 1 / 4))

theorem unit_square_difference_le {r z : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |r ^ 2 - z ^ 2| ≤ 2 * |r - z| := by
  have hf : r ^ 2 - z ^ 2 = (r - z) * (r + z) := by ring
  rw [hf, abs_mul, abs_of_nonneg (add_nonneg hr.1 hz.1)]
  have hh : r + z ≤ 2 := by linarith [hr.2, hz.2]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (abs_nonneg (r - z))

theorem physical_scalar_quantile_value_l1 (n : ℕ) (hn : 0 < n)
    {T : ℝ} (hT : 0 ≤ T) (r z : ℝ → ℝ)
    (hr : MonotoneOn r (Icc (0 : ℝ) 1))
    (hz : MonotoneOn z (Icc (0 : ℝ) 1))
    (hrb : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1)
    (hzb : ∀ u ∈ Icc (0 : ℝ) 1, z u ∈ Icc (0 : ℝ) 1) :
    |physicalScalarQuantileValue n T r - physicalScalarQuantileValue n T z| ≤
      T * (∫ u in (0 : ℝ)..1, |r u - z u|) := by
  have hir : IntervalIntegrable r volume 0 1 :=
    (show MonotoneOn r (uIcc (0 : ℝ) 1) by simpa using hr).intervalIntegrable
  have hiz : IntervalIntegrable z volume 0 1 :=
    (show MonotoneOn z (uIcc (0 : ℝ) 1) by simpa using hz).intervalIntegrable
  have hiabs := (hir.sub hiz).abs
  have hrs : MonotoneOn (fun u => r u ^ 2) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact pow_le_pow_left₀ (hrb u hu).1 (hr hu hv huv) 2
  have hzs : MonotoneOn (fun u => z u ^ 2) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact pow_le_pow_left₀ (hzb u hu).1 (hz hu hv huv) 2
  have hirs : IntervalIntegrable (fun u => r u ^ 2) volume 0 1 :=
    (show MonotoneOn (fun u => r u ^ 2) (uIcc (0 : ℝ) 1) by simpa using hrs).intervalIntegrable
  have hizs : IntervalIntegrable (fun u => z u ^ 2) volume 0 1 :=
    (show MonotoneOn (fun u => z u ^ 2) (uIcc (0 : ℝ) 1) by simpa using hzs).intervalIntegrable
  have hp := realOrderedSKPathPressure_l1_comparison n hn (fun _ => 0)
    (fun u => T * r u) (fun _ => 0) (fun u => T * z u)
    (fun _ _ _ _ _ => le_rfl)
    (fun u hu v hv huv => mul_le_mul_of_nonneg_left (hr hu hv huv) hT)
    (fun _ _ _ _ _ => le_rfl)
    (fun u hu v hv huv => mul_le_mul_of_nonneg_left (hz hu hv huv) hT) le_rfl
    (mul_nonneg hT (hrb 0 (by norm_num)).1) le_rfl
    (mul_nonneg hT (hzb 0 (by norm_num)).1) 0
  have he : (∫ u in (0 : ℝ)..1, |T * r u - T * z u|) =
      T * (∫ u in (0 : ℝ)..1, |r u - z u|) := by
    simp_rw [← mul_sub, abs_mul, abs_of_nonneg hT]
    exact intervalIntegral.integral_const_mul _ _
  simp only [sub_self, abs_zero, intervalIntegral.integral_zero, mul_zero, zero_add] at hp
  rw [he] at hp
  have hs : |(∫ u in (0 : ℝ)..1, r u ^ 2) -
      (∫ u in (0 : ℝ)..1, z u ^ 2)| ≤
        2 * (∫ u in (0 : ℝ)..1, |r u - z u|) := by
    rw [← intervalIntegral.integral_sub hirs hizs]
    calc
      _ ≤ ∫ u in (0 : ℝ)..1, |r u ^ 2 - z u ^ 2| := by
        simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
          (f := fun u => r u ^ 2 - z u ^ 2) (by norm_num : (0 : ℝ) ≤ 1)
      _ ≤ ∫ u in (0 : ℝ)..1, 2 * |r u - z u| := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
          (hirs.sub hizs).abs (hiabs.const_mul 2)
        intro u hu
        exact unit_square_difference_le (hrb u ⟨hu.1.le, hu.2.le⟩)
          (hzb u ⟨hu.1.le, hu.2.le⟩)
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hs' := mul_le_mul_of_nonneg_left hs (div_nonneg hT (by norm_num : (0 : ℝ) ≤ 4))
  have hsum := abs_add_le
    (realOrderedSKPathPressure n (fun _ => 0) (fun u => T * r u) 0 -
      realOrderedSKPathPressure n (fun _ => 0) (fun u => T * z u) 0)
    (T / 4 * ((∫ u in (0 : ℝ)..1, r u ^ 2) - ∫ u in (0 : ℝ)..1, z u ^ 2))
  rw [abs_mul, abs_of_nonneg (div_nonneg hT (by norm_num))] at hsum
  unfold physicalScalarQuantileValue
  have hid : realOrderedSKPathPressure n (fun _ => 0) (fun u => T * r u) 0 +
      T / 4 * (∫ u in (0 : ℝ)..1, r u ^ 2) -
      (realOrderedSKPathPressure n (fun _ => 0) (fun u => T * z u) 0 +
        T / 4 * (∫ u in (0 : ℝ)..1, z u ^ 2)) =
      (realOrderedSKPathPressure n (fun _ => 0) (fun u => T * r u) 0 -
        realOrderedSKPathPressure n (fun _ => 0) (fun u => T * z u) 0) +
        T / 4 * ((∫ u in (0 : ℝ)..1, r u ^ 2) -
          ∫ u in (0 : ℝ)..1, z u ^ 2) := by ring
  rw [hid]
  linarith

theorem mixedQuantile_monotoneOn {T : ℝ} (hT : 0 ≤ T)
    (e r z : ℝ → ℝ)
    (her : MonotoneOn (fun u => e u * r u) (Icc (0 : ℝ) 1))
    (hb : MonotoneOn (fun u => T - e u) (Icc (0 : ℝ) 1))
    (hz : MonotoneOn z (Icc (0 : ℝ) 1))
    (hbn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ T - e u)
    (hzn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ z u) :
    MonotoneOn (mixedQuantile T e r z) (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  apply div_le_div_of_nonneg_right _ hT
  exact add_le_add (her hu hv huv)
    (mul_le_mul (hb hu hv huv) (hz hu hv huv) (hzn u hu) (hbn v hv))

theorem mixedQuantile_radius_distance_le {T e r z : ℝ} (hT : 0 < T)
    (he : e ∈ Icc (0 : ℝ) T) :
    |(e * r + (T - e) * z) / T - r| ≤ |z - r| := by
  have hid : (e * r + (T - e) * z) / T - r =
      ((T - e) / T) * (z - r) := by
    field_simp
    ring
  have hc : (T - e) / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr he.2) hT.le,
      (div_le_one hT).mpr (sub_le_self T he.1)⟩
  rw [hid, abs_mul, abs_of_nonneg hc.1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc.2 (abs_nonneg _)

end OAI.SKFluctuations.LaplaceWindowFormalization

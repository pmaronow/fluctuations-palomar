module

public import ConstantDensityMacroPotential
public import SKFluctuationsOAI.Probability.SKFluctuations.ComparisonCapTravel

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem potential_negative_scalar_lower {Q r : ℝ} {H J S α : ℝ → ℝ} {C : ℝ≥0}
    (hQ : 0 < Q) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀ t ∈ Icc (0 : ℝ) 1, 0 < J t)
    (hd : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → HasDerivAt H (J t * (t - S t)) t)
    (hcap : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → H t < 0 → deriv α t = Q)
    (hneg : H r < 0) (hS : MonotoneOn S (Ioc (0 : ℝ) 1))
    (hS0 : 0 ≤ S r)
    (hα : LipschitzOnWith C α (Icc (0 : ℝ) 1))
    (hm : StrictMonoOn α (Icc (0 : ℝ) 1))
    (hαr : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ Icc (0 : ℝ) 1) :
    r - 1 / Q ≤ S r := by
  by_cases hSr : r ≤ S r
  · linarith [one_div_pos.mpr hQ]
  have hrs : S r ≤ r := (lt_of_not_ge hSr).le
  have hsub : Icc (S r) r ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hS0 hr.2
  have hneg' (t : ℝ) (ht : t ∈ Icc (S r) r) : H t < 0 := by
    have htr : t ≤ r := ht.2
    have ht0 : 0 ≤ t := hS0.trans ht.1
    have hH' : AbsolutelyContinuousOnInterval H t r :=
      hH.mono (by simpa only [uIcc_of_le zero_le_one, uIcc_of_le htr] using
        (Icc_subset_Icc ht0 hr.2 : Icc t r ⊆ Icc (0 : ℝ) 1))
    have hD' := hd.mono (fun s hs (hsi : s ∈ Icc t r) => hs
      ⟨ht0.trans hsi.1, hsi.2.trans hr.2⟩)
    have hi : 0 ≤ ∫ s in t..r, J s * (s - S s) := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict htr
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      filter_upwards [volume.ae_ne t] with s hst hsi
      have hs0 : 0 < s := ht0.trans_lt (lt_of_le_of_ne hsi.1 hst.symm)
      have hs1 : s ≤ 1 := hsi.2.trans hr.2
      have hSs := hS ⟨hs0, hs1⟩ hr hsi.2
      exact mul_nonneg (hJ s ⟨hs0.le, hs1⟩).le
        (sub_nonneg.mpr (hSs.trans (ht.1.trans hsi.1)))
    rw [potential_integral_eq_sub htr hH' hD'] at hi
    linarith
  have ht := cap_travel_le_total (M := fun _ => Q) hrs (hα.mono hsub)
    (hm.mono hsub) (fun t ht => hαr t (hsub ht)) continuousOn_const
    (fun _ _ => hQ) (hcap.mono fun t ht hti => ht (hsub hti) (hneg' t hti))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at ht
  linarith

theorem potential_negative_scalar_mismatch {Q r : ℝ} {H J S α : ℝ → ℝ} {C : ℝ≥0}
    (hQ : 0 < Q) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀ t ∈ Icc (0 : ℝ) 1, 0 < J t)
    (hd : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → HasDerivAt H (J t * (t - S t)) t)
    (hcap : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → H t < 0 → deriv α t = Q)
    (hneg : H r < 0) (hS : MonotoneOn S (Ioc (0 : ℝ) 1))
    (hSb : ∀ t ∈ Ioc (0 : ℝ) 1, S t ∈ Icc (0 : ℝ) 1)
    (hα : LipschitzOnWith C α (Icc (0 : ℝ) 1))
    (hm : StrictMonoOn α (Icc (0 : ℝ) 1))
    (hαr : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ Icc (0 : ℝ) 1) :
    |S r - r| ≤ 1 / Q := by
  have hlow := potential_negative_scalar_lower hQ hr hH hJ hd hcap hneg hS
    (hSb r hr).1 hα hm hαr
  have hD : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → HasDerivAt H
      ((J t / 2) * comparisonBracket 0 t (S t) ((S t)^2)) t := by
    filter_upwards [hd] with t hdt hti
    convert hdt hti using 1
    simp only [comparisonBracket, zero_mul, sub_zero, one_mul, zero_div]
    ring
  have hupp := potential_negative_center_bound (M := fun _ => Q) (p := fun _ => 0)
    (B := fun t => (S t)^2) (J := fun t => J t / 2) le_rfl hr hH
    (fun t ht => div_pos (hJ t ht) (by norm_num)) hD hcap hneg
    (fun _ _ => le_rfl) hS (hSb r hr).2 (fun _ _ => le_rfl) hα hm hαr
    continuousOn_const (fun _ _ => hQ)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at hupp
  apply abs_le.mpr
  constructor <;> linarith

theorem potential_macro_radius_defect {η Q : ℝ} {H J S α : ℝ → ℝ} {C : ℝ≥0}
    (hη : 0 ≤ η) (hQ : 0 < Q)
    (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀ t ∈ Icc (0 : ℝ) 1, 0 < J t)
    (hd : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → HasDerivAt H (J t * (t - S t)) t)
    (hbang : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 →
      (H t < 0 → deriv α t = Q) ∧ (0 < H t → deriv α t = η))
    (hcontact : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → H t = 0 → S t = t)
    (hS : MonotoneOn S (Ioc (0 : ℝ) 1))
    (hSb : ∀ t ∈ Ioc (0 : ℝ) 1, S t ∈ Icc (0 : ℝ) 1)
    (hα : LipschitzOnWith C α (Icc (0 : ℝ) 1))
    (hm : StrictMonoOn α (Icc (0 : ℝ) 1))
    (hαr : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ Icc (0 : ℝ) 1)
    (hα0 : α 0 = 0) (hα1 : α 1 = 1)
    (hdensity : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → 0 ≤ deriv α t) :
    (∫ r in Icc (0 : ℝ) 1, deriv α r * (S r - r)^2) ≤ η + (1 / Q)^2 := by
  have hαac : AbsolutelyContinuousOnInterval α 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le zero_le_one] using hα
  have hir : IntervalIntegrable (fun r => η + deriv α r * (1 / Q)^2) volume 0 1 :=
    intervalIntegrable_const.add (hαac.intervalIntegrable_deriv.mul_const _)
  have hir' : IntegrableOn (fun r => η + deriv α r * (1 / Q)^2) (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hir
  have hcap := hbang.mono (fun t ht hti => (ht hti).1)
  have hnon : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (fun r => deriv α r * (S r - r)^2) := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hdensity] with r hdr hri
    exact mul_nonneg (hdr hri) (sq_nonneg _)
  have hle : (fun r => deriv α r * (S r - r)^2) ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (fun r => η + deriv α r * (1 / Q)^2) := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hbang, hcontact, hdensity, volume.ae_ne (0 : ℝ)] with r hrbang hrzero hdr hr0 hri
    have hri' : r ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hri.1 hr0.symm, hri.2⟩
    have hd0 := hdr hri
    have he1 : (S r - r)^2 ≤ 1 := by
      have hs := hSb r hri'
      have hab : |S r - r| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1, hri.2],
        by linarith [hs.2, hri.1]⟩
      have hsq := (sq_le_sq₀ (abs_nonneg (S r - r)) zero_le_one).mpr hab
      simpa only [sq_abs, one_pow] using hsq
    rcases lt_trichotomy (H r) 0 with hneg | hzero | hpos
    · have hab := potential_negative_scalar_mismatch hQ hri' hH hJ hd hcap hneg hS hSb hα hm hαr
      have hsq := (sq_le_sq₀ (abs_nonneg (S r - r)) (one_div_pos.mpr hQ).le).mpr hab
      simp only [sq_abs] at hsq
      exact (mul_le_mul_of_nonneg_left hsq hd0).trans (le_add_of_nonneg_left hη)
    · rw [hrzero hri hzero, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      positivity
    · rw [(hrbang hri).2 hpos]
      have hmul := mul_le_mul_of_nonneg_left he1 hη
      nlinarith [sq_nonneg (1 / Q)]
  have hi := integral_mono_of_nonneg hnon hir' hle
  have he : (∫ r in Icc (0 : ℝ) 1, η + deriv α r * (1 / Q)^2) = η + (1 / Q)^2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_add intervalIntegrable_const (hαac.intervalIntegrable_deriv.mul_const _),
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
      hαac.integral_deriv_eq_sub, hα0, hα1]
    simp
  exact hi.trans_eq he

theorem macro_mass_defect_substitution {α z S : ℝ → ℝ} {C : ℝ≥0}
    (hα : LipschitzOnWith C α (Icc (0 : ℝ) 1))
    (hm : StrictMonoOn α (Icc (0 : ℝ) 1))
    (himage : α '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
    (hz : ∀ r ∈ Icc (0 : ℝ) 1, z (α r) = r)
    (hdensity : ∀ᵐ r, r ∈ Icc (0 : ℝ) 1 → 0 ≤ deriv α r) :
    (∫ u in (0 : ℝ)..1, (S u - z u)^2) =
      ∫ r in Icc (0 : ℝ) 1, deriv α r * (S (α r) - r)^2 := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← himage, lipschitz_interval_integral_image zero_le_one hα hm.injOn]
  rw [himage]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards [hdensity] with r hdr hri
  rw [abs_of_nonneg (hdr hri), hz r hri]

end OAI.SKFluctuations.LaplaceWindowFormalization

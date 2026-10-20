module

public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.WallSweep

open MeasureTheory Filter Set
open scoped Topology NNReal

theorem minimum_lipschitzOn {α : Type*} {s : Set ℝ} {K : ℝ≥0}
    (J : ℝ → α → ℝ) (v : ℝ → ℝ)
    (hmin : ∀ t ∈ s, ∃ a, J t a = v t ∧ ∀ b, v t ≤ J t b)
    (hLip : ∀ a, LipschitzOnWith K (fun t => J t a) s) :
    LipschitzOnWith K v s := by
  have hupper {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
      v x - v y ≤ (K : ℝ) * dist x y := by
    obtain ⟨a, hva, hmina⟩ := hmin y hy
    obtain ⟨b, hvb, hminb⟩ := hmin x hx
    calc
      v x - v y ≤ J x a - J y a := by rw [hva]; exact sub_le_sub_right (hminb a) _
      _ ≤ |J x a - J y a| := le_abs_self _
      _ ≤ (K : ℝ) * dist x y := by
        simpa only [Real.dist_eq] using (hLip a).dist_le_mul x hx y hy
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := hupper hy hx
    rw [dist_comm] at h
    linarith
  · exact hupper hx hy

theorem minimum_derivative_eq {J v : ℝ → ℝ} {t dv dJ : ℝ}
    (hcontact : J t = v t) (hbound : ∀ᶠ x in 𝓝 t, v x ≤ J x)
    (hv : HasDerivAt v dv t) (hJ : HasDerivAt J dJ t) :
    dv = dJ := by
  have hlocal : IsLocalMin (fun x => J x - v x) t := by
    filter_upwards [hbound] with x hx
    change J t - v t ≤ J x - v x
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr hx
  have hz := hlocal.hasDerivAt_eq_zero (hJ.sub hv)
  linarith

theorem minimum_sub_le_integral {α : Type*} {a b : ℝ} (hab : a ≤ b)
    (J : ℝ → α → ℝ) (v g : ℝ → ℝ) {K : ℝ≥0}
    (hv : LipschitzOnWith K v (uIcc a b))
    (hmin : ∀ t ∈ Ioo a b,
      ∃ z, J t z = v t ∧ (∀ᶠ x in 𝓝 t, v x ≤ J x z) ∧
        ∃ d, HasDerivAt (fun x => J x z) d t ∧ d ≤ g t)
    (hg : IntervalIntegrable g volume a b) :
    v b - v a ≤ ∫ t in a..b, g t := by
  have hac := hv.absolutelyContinuousOnInterval
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_mono_ae_restrict hab hac.intervalIntegrable_deriv hg
  change ∀ᵐ t ∂volume.restrict (Icc a b), deriv v t ≤ g t
  rw [ae_restrict_iff' measurableSet_Icc]
  have hnea : ∀ᵐ t : ℝ, t ≠ a := by simp [ae_iff]
  have hneb : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff]
  filter_upwards [hac.ae_differentiableAt, hnea, hneb] with t ht hta htb
  intro hti
  have htcc : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hti
  have htoo : t ∈ Ioo a b :=
    ⟨lt_of_le_of_ne hti.1 (Ne.symm hta), lt_of_le_of_ne hti.2 htb⟩
  obtain ⟨z, hcontact, hbound, d, hd, hdg⟩ := hmin t htoo
  have heq := minimum_derivative_eq hcontact hbound (ht htcc).hasDerivAt hd
  exact heq.le.trans hdg

end OAI.SKFluctuations.WallSweep

module

public import SKConstants.ScalarProcessTail
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace SKConstants

noncomputable def scalarTailScale (t : ℝ≥0) : ℝ :=
  Real.exp (-(t : ℝ) / (((2 : ℕ) : ℝ))) *
    (Real.sqrt ((((2 : ℕ) : ℝ)) * Real.pi * (t : ℝ)))⁻¹

noncomputable def scalarCompactTailConstant (R : ℝ) : ℝ :=
  (((2 : ℕ) : ℝ)) * Real.exp (-((1 + R) ^ 2) / (((2 : ℕ) : ℝ))) /
    (Real.cosh R * (Real.cosh (((1 : ℕ) : ℝ))) ^ (((3 : ℕ) : ℕ)))

noncomputable def scalarSeedP (ν : Measure ℝ) (t : ℝ≥0) : ℝ := ∫ z, scalarP z t ∂ν

noncomputable def scalarSeedR (ν : Measure ℝ) (t : ℝ≥0) : ℝ := ∫ z, scalarR z t ∂ν

theorem scalarTailScale_nonneg (t : ℝ≥0) : 0 ≤ scalarTailScale t := by
  unfold scalarTailScale
  positivity

theorem scalarCompactTailConstant_pos (R : ℝ) : 0 < scalarCompactTailConstant R := by
  unfold scalarCompactTailConstant
  positivity

theorem scalarP_le_four_tailScale (z : ℝ) (t : ℝ≥0) :
    scalarP z t ≤ 4 * scalarTailScale t := by
  have hh := scalarP_le_sharp_tail z t
  have hd : Real.exp (-(t : ℝ) / 2) / Real.cosh z ≤ Real.exp (-(t : ℝ) / 2) :=
    div_le_self (Real.exp_pos _).le (Real.one_le_cosh z)
  have hm := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 4 * (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ by positivity)
  unfold scalarTailScale
  norm_num only [Nat.cast_ofNat]
  apply hh.trans
  convert hm using 1 <;> ring

theorem scalarR_ge_compact_tailScale (z R : ℝ) (t : ℝ≥0)
    (ht : 1 ≤ (t : ℝ)) (hR : 0 ≤ R) (hz : |z| ≤ R) :
    scalarCompactTailConstant R * scalarTailScale t ≤ scalarR z t := by
  have hs : (1 + |z|) ^ 2 ≤ (1 + R) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have he : Real.exp (-((1 + R) ^ 2) / 2) ≤ Real.exp (-((1 + |z|) ^ 2) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hc : Real.cosh z ≤ Real.cosh R :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg hR] using hz)
  have hratio : Real.exp (-((1 + R) ^ 2) / 2) / Real.cosh R ≤
      Real.exp (-((1 + |z|) ^ 2) / 2) / Real.cosh z := by
    calc
      _ ≤ Real.exp (-((1 + |z|) ^ 2) / 2) / Real.cosh R :=
        div_le_div_of_nonneg_right he (Real.cosh_pos R).le
      _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.cosh_pos z) hc
  have hm := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ 2 * scalarTailScale t / (Real.cosh 1) ^ 3 by
      exact div_nonneg (mul_nonneg (by norm_num) (scalarTailScale_nonneg t)) (by positivity))
  have hh := scalarR_ge_sharp_tail z t ht
  apply le_trans _ hh
  unfold scalarCompactTailConstant scalarTailScale at *
  norm_num only [Nat.cast_ofNat] at *
  convert hm using 1 <;> ring

theorem integrable_scalarP_seed (ν : Measure ℝ) [IsFiniteMeasure ν]
    (t : ℝ≥0) (ht : t ≠ 0) : Integrable (fun z ↦ scalarP z t) ν := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_scalarP t).aestronglyMeasurable ?_
  exact ae_of_all _ (fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (scalarP_nonneg z t)]
    exact scalarP_le_one z t ht)

theorem integrable_scalarR_seed (ν : Measure ℝ) [IsFiniteMeasure ν]
    (t : ℝ≥0) (ht : t ≠ 0) : Integrable (fun z ↦ scalarR z t) ν := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_scalarR t).aestronglyMeasurable ?_
  exact ae_of_all _ (fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (scalarR_nonneg z t)]
    exact scalarR_le_one z t ht)

theorem scalarSeedP_le_sharp_tail (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (t : ℝ≥0) (ht : t ≠ 0) : scalarSeedP ν t ≤ 4 * scalarTailScale t := by
  have hh := integral_mono (integrable_scalarP_seed ν t ht)
    (integrable_const (4 * scalarTailScale t)) (fun z ↦ scalarP_le_four_tailScale z t)
  simpa [scalarSeedP] using hh

theorem scalarSeedR_ge_sharp_tail (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (R : ℝ) (hR : 0 ≤ R) (t : ℝ≥0) (ht : 1 ≤ (t : ℝ)) :
    ν.real (Icc (-R) R) * scalarCompactTailConstant R * scalarTailScale t ≤
      scalarSeedR ν t := by
  have ht0 : t ≠ 0 := by
    intro h
    simp only [h, NNReal.coe_zero] at ht
    linarith
  have hi := integrable_scalarR_seed ν t ht0
  calc
    _ = ∫ z in Icc (-R) R, scalarCompactTailConstant R * scalarTailScale t ∂ν := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    _ ≤ ∫ z in Icc (-R) R, scalarR z t ∂ν := by
      apply setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn measurableSet_Icc
      intro z hz
      exact scalarR_ge_compact_tailScale z R t ht hR (abs_le.mpr hz)
    _ ≤ scalarSeedR ν t := by
      simpa [scalarSeedR] using (setIntegral_le_integral (s := Icc (-R) R) hi
        (ae_of_all _ (fun z ↦ scalarR_nonneg z t)))

end SKConstants

module
public import SKConstants.ScalarObservationPredictableSums

public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
noncomputable section
namespace SKConstants

lemma scalarObservationPredictableVariation_le_of_bounded {Ω : Type*}
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (C : ℝ)
    (hC : ∀ k w, ‖H k w‖ ≤ C) (n : ℕ) (u : Bool × Ω) :
    scalarObservationPredictableVariation z B t H n u ≤
      C ^ 2 * ((t n : ℝ) - (t 0 : ℝ)) := by
  unfold scalarObservationPredictableVariation
  induction n with
  | zero => simp [predictableGaussianVariation]
  | succ n ih =>
    have hsq : scalarObservationCoefficient z B t H n u ^ 2 ≤ C ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) (hC n (scalarActualObservationPast z B (t n) u)) 2
      simpa only [scalarObservationCoefficient, Real.norm_eq_abs, sq_abs] using h
    have ht' : (t n : ℝ) ≤ (t (n + 1) : ℝ) :=
      NNReal.coe_le_coe.mpr (ht (Nat.le_succ n))
    change predictableGaussianVariation (brownianMeshVariance t)
      (scalarObservationCoefficient z B t H) n u +
        scalarObservationCoefficient z B t H n u ^ 2 * (brownianMeshVariance t n : ℝ) ≤ _
    rw [brownianMeshVariance, NNReal.coe_sub (ht (Nat.le_succ n))]
    calc
      _ ≤ C ^ 2 * ((t n : ℝ) - (t 0 : ℝ)) +
          C ^ 2 * ((t (n + 1) : ℝ) - (t n : ℝ)) :=
        add_le_add ih (mul_le_mul_of_nonneg_right hsq (sub_nonneg.mpr ht'))
      _ = C ^ 2 * ((t (n + 1) : ℝ) - (t 0 : ℝ)) := by ring

lemma scalarObservationPredictableVariation_current_le_of_bounded {Ω : Type*}
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ℝ → ℝ) (C : ℝ) (hC : ∀ y, ‖H y‖ ≤ C) (n : ℕ) (u : Bool × Ω) :
    scalarObservationPredictableVariation z B t (scalarCurrentObservationCoefficient t H) n u ≤
      C ^ 2 * ((t n : ℝ) - (t 0 : ℝ)) := by
  exact scalarObservationPredictableVariation_le_of_bounded z B t ht
    (scalarCurrentObservationCoefficient t H) C (fun k w => hC _) n u

lemma scalarObservationPredictableVariation_current_uniform_le_of_bounded {Ω : Type*}
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (H : ℝ → ℝ) (C : ℝ)
    (hC : ∀ y, ‖H y‖ ≤ C) (n m : ℕ) (u : Bool × Ω) :
    scalarObservationPredictableVariation z B (scalarUniformTime n)
      (scalarCurrentObservationCoefficient (scalarUniformTime n) H) m u ≤
        C ^ 2 * (scalarUniformTime n m : ℝ) := by
  simpa only [scalarUniformTime_zero, NNReal.coe_zero, sub_zero] using
    scalarObservationPredictableVariation_current_le_of_bounded z B (scalarUniformTime n)
      (scalarUniformTime_monotone n) H C hC m u

lemma scalarUniformTime_floor_le (n : ℕ) (T : ℝ≥0) :
    scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ ≤ T := by
  apply NNReal.coe_le_coe.mp
  rw [scalarUniformTime_coe]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  exact (Nat.floor_le (by positivity)).trans_eq (mul_comm _ _)

lemma scalarObservationPredictableVariation_defect_uniform_le_time {Ω : Type*}
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (n m : ℕ) (u : Bool × Ω) :
    scalarObservationPredictableVariation z B (scalarUniformTime n)
      (scalarCurrentObservationCoefficient (scalarUniformTime n) scalarDefect) m u ≤
        (scalarUniformTime n m : ℝ) := by
  have hb : ∀ y, ‖scalarDefect y‖ ≤ 1 := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (scalarDefect_pos y).le]
    exact scalarDefect_le_one y
  simpa only [one_pow, one_mul] using
    scalarObservationPredictableVariation_current_uniform_le_of_bounded z B scalarDefect 1 hb n m u

lemma scalarObservationPredictableVariation_defect_uniform_floor_le {Ω : Type*}
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (T : ℝ≥0) (u : Bool × Ω) :
    scalarObservationPredictableVariation z B (scalarUniformTime n)
      (scalarCurrentObservationCoefficient (scalarUniformTime n) scalarDefect)
      ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u ≤ (T : ℝ) := by
  exact (scalarObservationPredictableVariation_defect_uniform_le_time z B n _ u).trans
    (NNReal.coe_le_coe.mpr (scalarUniformTime_floor_le n T))

end SKConstants

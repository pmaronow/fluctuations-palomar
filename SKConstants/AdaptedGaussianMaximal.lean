module

public import SKConstants.AdaptedGaussianMGF

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def adaptedGaussianRunningAbsMax (H : GaussianPredictableCoefficient) :
    (n : ℕ) → GaussianHistory n → ℝ :=
  Nat.rec (motive := fun n => GaussianHistory n → ℝ) (fun _ => 0)
    (fun n running z => max (running z.1) |adaptedGaussianSum H (n + 1) z|)

theorem measurable_adaptedGaussianRunningAbsMax (H : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (adaptedGaussianRunningAbsMax H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).max
      (continuous_abs.measurable.comp (measurable_adaptedGaussianSum H hH (n + 1)))

def gaussianFirstExitCoefficient (H : GaussianPredictableCoefficient) (u : ℝ) :
    GaussianPredictableCoefficient :=
  fun k z => if adaptedGaussianRunningAbsMax H k z < u then H k z else 0

theorem measurable_gaussianFirstExitCoefficient (H : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k)) (u : ℝ) (k : ℕ) :
    Measurable (gaussianFirstExitCoefficient H u k) :=
  Measurable.ite
    (measurableSet_lt (measurable_adaptedGaussianRunningAbsMax H hH k) measurable_const)
    (hH k) measurable_const

theorem gaussianFirstExit_sum_properties (H : GaussianPredictableCoefficient)
    (u : ℝ) (hu : 0 < u) (n : ℕ) (z : GaussianHistory n) :
    (adaptedGaussianRunningAbsMax H n z < u →
      adaptedGaussianSum (gaussianFirstExitCoefficient H u) n z = adaptedGaussianSum H n z) ∧
    (u ≤ adaptedGaussianRunningAbsMax H n z →
      u ≤ |adaptedGaussianSum (gaussianFirstExitCoefficient H u) n z|) := by
  induction n with
  | zero =>
    constructor
    · intro _
      rfl
    · intro hz
      exact False.elim ((not_le_of_gt hu) hz)
  | succ n ih =>
    have hprev := ih z.1
    by_cases hbefore : adaptedGaussianRunningAbsMax H n z.1 < u
    · have hsum : adaptedGaussianSum (gaussianFirstExitCoefficient H u) (n + 1) z =
          adaptedGaussianSum H (n + 1) z := by
        simp only [adaptedGaussianSum, gaussianFirstExitCoefficient, hbefore, ↓reduceIte]
        rw [hprev.1 hbefore]
      constructor
      · intro _
        exact hsum
      · intro hz
        rw [hsum]
        have hmax := (le_max_iff.mp hz)
        rcases hmax with hpast | hnow
        · exact False.elim ((not_le_of_gt hbefore) hpast)
        · exact hnow
    · have hcross : u ≤ adaptedGaussianRunningAbsMax H n z.1 := le_of_not_gt hbefore
      have hsum : adaptedGaussianSum (gaussianFirstExitCoefficient H u) (n + 1) z =
          adaptedGaussianSum (gaussianFirstExitCoefficient H u) n z.1 := by
        simp only [adaptedGaussianSum, gaussianFirstExitCoefficient, hbefore, ↓reduceIte,
          zero_mul, add_zero]
      constructor
      · intro hz
        have hmax : adaptedGaussianRunningAbsMax H n z.1 ≤
            adaptedGaussianRunningAbsMax H (n + 1) z := le_max_left _ _
        exact False.elim ((not_le_of_gt hz) (hcross.trans hmax))
      · intro _
        rw [hsum]
        exact hprev.2 hcross

theorem gaussianFirstExit_quadraticVariation_le (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (u : ℝ) (n : ℕ) (z : GaussianHistory n) :
    adaptedGaussianQuadraticVariation dt (gaussianFirstExitCoefficient H u) n z ≤
      adaptedGaussianQuadraticVariation dt H n z := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    apply add_le_add (ih z.1)
    unfold gaussianFirstExitCoefficient
    split_ifs
    · exact le_rfl
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact mul_nonneg (sq_nonneg _) (dt n).coe_nonneg

theorem adaptedGaussianSum_maximal_tail (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ z ∂gaussianHistoryLaw dt n,
      adaptedGaussianQuadraticVariation dt H n z ≤ V)
    (hVp : 0 < V) (u : ℝ) (hu : 0 < u) :
    (gaussianHistoryLaw dt n).real {z | u ≤ adaptedGaussianRunningAbsMax H n z} ≤
      2 * Real.exp (-(u ^ 2 / (2 * V))) := by
  have hstopV : ∀ᵐ z ∂gaussianHistoryLaw dt n,
      adaptedGaussianQuadraticVariation dt (gaussianFirstExitCoefficient H u) n z ≤ V := by
    filter_upwards [hV] with z hz
    exact (gaussianFirstExit_quadraticVariation_le dt H u n z).trans hz
  have htail := adaptedGaussianSum_two_sided_tail dt (gaussianFirstExitCoefficient H u)
    (measurable_gaussianFirstExitCoefficient H hH u) n V hstopV hVp u hu.le
  apply le_trans ?_ htail
  apply measureReal_mono ?_ (measure_ne_top (gaussianHistoryLaw dt n) _)
  intro z hz
  exact (gaussianFirstExit_sum_properties H u hu n z).2 hz

end SKConstants

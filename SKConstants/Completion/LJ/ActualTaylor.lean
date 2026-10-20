module

public import SKConstants.Completion.LJ.FiniteRow
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def actualTaylorRow (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (K : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  taylorRow (fun j : Fin K => gridPosteriorScale W β t j)
    (fun j => gridQueryMean W β t j)
    (fun j => actualParisiNormalizedPosteriorRow W β t K u.1.2 j)
    (fun j => gridQuery W Z β hβ t K j u) (scalarHiddenSign u.1.1)

theorem actualTaylorRow_eq_finite (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t) (ht0 : t 0 = 0)
    (K : ℕ) (H : ℝ≥0) :
    actualTaylorRow W Z β hβ t K =ᵐ[actualParisiFullQuerySpinLaw W Z β H]
      actualFiniteRow W Z β hβ t K := by
  have hz := ((actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).measurePreserving
    (measurable_snd.comp measurable_fst)).quasiMeasurePreserving.ae
      (actualParisiMagnetizationObservable_zero_ae W β hβ)
  filter_upwards [hz] with u hu
  let s : Fin K → ℝ := fun j => gridPosteriorScale W β t j
  let b : Fin K → ℝ := fun j => gridQueryMean W β t j
  let a : ℕ → ℝ := fun j => actualParisiFullPosteriorMean W β (t j) u.1.2
  let T : Fin K → ℝ := fun j => actualParisiNormalizedPosteriorRow W β t K u.1.2 j
  let g : Fin K → ℝ := fun j => gridQuery W Z β hβ t K j u
  let x := scalarHiddenSign u.1.1
  have hs (j : Fin K) : s j ≠ 0 :=
    (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ _ _ (ht (by omega)))).ne'
  have ha0 : a 0 = 0 := by
    change actualParisiFullPosteriorMean W β (t 0) u.1.2 = 0
    rw [ht0]
    exact hu
  have hT : T = fun j : Fin K => (a (j + 1) - a j) / s j := rfl
  have hprev (j : Fin K) : rowPrevious s T j = a j := by
    rw [hT, rowPrevious_increments s a hs j, ha0, sub_zero]
  have hcurr (j : Fin K) : rowCurrent s T j = a (j + 1) := by
    rw [hT, rowCurrent_increments s a hs j, ha0, sub_zero]
  change taylorRow s b T g x = _
  rw [taylorRow_eq s b T g x hs]
  simp only [hprev, hcurr]
  simp only [actualFiniteRow, actualRowPotential, gridEnergy, rowPair, s, b, a, g, x,
    mul_assoc]

theorem actualTaylorRow_mean (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t) (ht0 : t 0 = 0)
    (K : ℕ) (H : ℝ≥0) (hH : t (K + 1) ≤ H) :
    (∫ u, actualTaylorRow W Z β hβ t K u ∂actualParisiFullQuerySpinLaw W Z β H) =
      gridEnergy W β t K :=
  (integral_congr_ae (actualTaylorRow_eq_finite W Z β hβ t ht ht0 K H)).trans
    (actualFiniteRow_mean W Z β hβ t ht K H hH)

end SKConstants.Completion.LJ

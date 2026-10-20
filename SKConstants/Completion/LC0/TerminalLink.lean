module
public import SKConstants.ParisiFullTerminalSpinLaw

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SKConstants.M1

def spinPrior (N : ℕ) : Measure (Fin N → Bool) :=
  Measure.pi (fun _ : Fin N => scalarHiddenPriorBool 0)

instance spinPrior_isProbability (N : ℕ) : IsProbabilityMeasure (spinPrior N) := by
  unfold spinPrior
  infer_instance

def TerminalDensity {S : Type*} {N : ℕ}
    (β : ℝ) (H : ℝ≥0) (Y : S → Fin N → ℝ)
    (u : (Fin N → Bool) × S) : ℝ :=
  ∏ i : Fin N, actualParisiSpinLinkDensity β (u.1 i) H (Y u.2 i)

theorem terminalDensity_eq_product {S : Type*} {N : ℕ}
    (β : ℝ) (H : ℝ≥0) (Y : S → Fin N → ℝ)
    (u : (Fin N → Bool) × S) :
    TerminalDensity β H Y u =
      ∏ i : Fin N, (1 + scalarHiddenSign (u.1 i) *
        actualParisiFullMagnetization β H (Y u.2 i)) := rfl

def TerminalLinkedLaw {S : Type*} [MeasurableSpace S] {N : ℕ}
    (β : ℝ) (H : ℝ≥0) (μ : Measure S) (Y : S → Fin N → ℝ) :
    Measure ((Fin N → Bool) × S) :=
  ((spinPrior N).prod μ).withDensity
    (fun u => ENNReal.ofReal (TerminalDensity β H Y u))

theorem terminalDensity_pos {S : Type*} {N : ℕ}
    (β : ℝ) (H : ℝ≥0) (Y : S → Fin N → ℝ)
    (u : (Fin N → Bool) × S) : 0 < TerminalDensity β H Y u := by
  exact Finset.prod_pos fun i _ => actualParisiSpinLinkDensity_pos β (u.1 i) H (Y u.2 i)

theorem measurable_terminalDensity {S : Type*} [MeasurableSpace S] {N : ℕ}
    (β : ℝ) (H : ℝ≥0) (Y : S → Fin N → ℝ) (hY : Measurable Y) :
    Measurable (TerminalDensity β H Y) := by
  apply Finset.measurable_prod
  intro i _
  have hm : Measurable (fun y : ℝ => actualParisiFullMagnetization β H y) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  exact measurable_const.add
    (((measurable_of_finite scalarHiddenSign).comp
      ((measurable_pi_apply i).comp measurable_fst)).mul
      (hm.comp (((measurable_pi_apply i).comp hY).comp measurable_snd)))

end SKConstants.M1

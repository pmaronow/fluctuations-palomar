module

public import SKConstants.Completion.LM4.RowInformation
public import SKConstants.ParisiFullMixedRowCovariance

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.LM4

open Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def actualRowBaseLaw (W : BrownianSystem Ω) (Z : BrownianSystem A) : Measure ((Bool × Ω) × A) :=
  ((scalarHiddenPriorBool 0).prod W.law).prod Z.law

instance actualRowBaseLaw_isProbability (W : BrownianSystem Ω) (Z : BrownianSystem A) :
    IsProbabilityMeasure (actualRowBaseLaw W Z) := by
  have := W.isProbability
  have := Z.isProbability
  unfold actualRowBaseLaw
  infer_instance

def actualRowLink (β : ℝ) (W : BrownianSystem Ω) (V : ℝ≥0) (u : (Bool × Ω) × A) : ℝ :=
  actualParisiFullTerminalSpinDensity β W V u.1

theorem measurable_actualRowLink (β : ℝ) (W : BrownianSystem Ω) (V : ℝ≥0) :
    Measurable (actualRowLink (A := A) β W V) :=
  (measurable_actualParisiFullTerminalSpinDensity β W V).comp measurable_fst

omit [MeasurableSpace A] in
theorem actualRowLink_bounds (β : ℝ) (W : BrownianSystem Ω) (V : ℝ≥0)
    (u : (Bool × Ω) × A) : 0 < actualRowLink β W V u ∧ actualRowLink β W V u ≤ 2 := by
  refine ⟨actualParisiFullTerminalSpinDensity_pos β W V u.1, ?_⟩
  have hm := actualParisiFullMagnetization_strict_bounds β V (actualParisiFullTerminalField β W V u.1.2)
  change 1 + scalarHiddenSign u.1.1 *
    actualParisiFullMagnetization β V (actualParisiFullTerminalField β W V u.1.2) ≤ 2
  cases u.1.1 <;> simp only [scalarHiddenSign, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul] <;> linarith

theorem actual_linkedRowLaw_eq (β : ℝ) (W : BrownianSystem Ω) (Z : BrownianSystem A) (V : ℝ≥0) :
    linkedRowLaw (actualRowBaseLaw W Z) (actualRowLink β W V) =
      actualParisiFullQuerySpinLaw W Z β V := by
  have := Z.isProbability
  symm
  exact prod_withDensity_left (μ := (scalarHiddenPriorBool 0).prod W.law)
    (ν := Z.law) (measurable_actualParisiFullTerminalSpinDensity β W V).ennreal_ofReal

theorem actualRowLink_integral (β : ℝ) (W : BrownianSystem Ω) (Z : BrownianSystem A) (V : ℝ≥0) :
    (∫ u, actualRowLink β W V u ∂actualRowBaseLaw W Z) = 1 := by
  have he := integral_linkedRowLaw (μ := actualRowBaseLaw W Z) (f := fun _ => (1 : ℝ))
    (measurable_actualRowLink β W V)
    (ae_of_all _ (fun u => (actualRowLink_bounds β W V u).1.le))
  rw [actual_linkedRowLaw_eq] at he
  simpa using he.symm

def actualRowInformation (β : ℝ) (W : BrownianSystem Ω) (V : ℝ≥0)
    (J Q : (Bool × Ω) × A → ℝ) : (Bool × Ω) × A → ℝ :=
  rowInformation (actualRowLink β W V) J Q

theorem actualRowInformation_centered_moments
    (β : ℝ) (W : BrownianSystem Ω) (Z : BrownianSystem A) (V : ℝ≥0)
    (J Q : (Bool × Ω) × A → ℝ) (hJm : Measurable J) (hQm : Measurable Q)
    (hJ : HasSubgaussianMGF J (4 * V) (actualRowBaseLaw W Z))
    (hQ : ∀ᵐ u ∂actualRowBaseLaw W Z, 0 ≤ Q u ∧ Q u ≤ 4 * (V : ℝ)) :
    let ν := actualParisiFullQuerySpinLaw W Z β V
    let X := centeredObservable ν (actualRowInformation β W V J Q)
    (∀ p : ℕ, Integrable (fun u => X u ^ p) ν) ∧
    (∫ u, X u ∂ν = 0) ∧
    (∀ p : ℕ, 2 ≤ p → (∫ u, |X u| ^ p ∂ν) ≤
      (p.factorial : ℝ) * (16 * (1 + (V : ℝ))) ^ p) := by
  have h := rowInformation_centered_moments (measurable_actualRowLink β W V) hJm hQm
    (ae_of_all _ (fun u => ⟨(actualRowLink_bounds β W V u).1.le, (actualRowLink_bounds β W V u).2⟩))
    (actualRowLink_integral β W Z V) V hJ hQ
  simpa only [actual_linkedRowLaw_eq, actualRowInformation] using h

theorem actualRowInformation_iid_upper
    (β : ℝ) (W : BrownianSystem Ω) (Z : BrownianSystem A) (V : ℝ≥0)
    (J Q : (Bool × Ω) × A → ℝ) (hJm : Measurable J) (hQm : Measurable Q)
    (hJ : HasSubgaussianMGF J (4 * V) (actualRowBaseLaw W Z))
    (hQ : ∀ᵐ u ∂actualRowBaseLaw W Z, 0 ≤ Q u ∧ Q u ≤ 4 * (V : ℝ))
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let ν := actualParisiFullQuerySpinLaw W Z β V
    (actualParisiFullMixedRowsLaw W Z β V n).real
      {u | (n : ℝ) * η ≤ ∑ i : Fin n,
        centeredObservable ν (actualRowInformation β W V J Q) (u i)} ≤
      Real.exp (-(n : ℝ) * min
        (η ^ 2 / (2048 * (1 + (V : ℝ)) ^ 2)) (η / (64 * (1 + (V : ℝ))))) := by
  have h := iid_rowInformation_upper (measurable_actualRowLink β W V) hJm hQm
    (ae_of_all _ (fun u => ⟨(actualRowLink_bounds β W V u).1.le, (actualRowLink_bounds β W V u).2⟩))
    (actualRowLink_integral β W Z V) V hJ hQ hn hη
  simpa only [actual_linkedRowLaw_eq, actualRowInformation, actualParisiFullMixedRowsLaw] using h

theorem actualRowInformation_iid_abs
    (β : ℝ) (W : BrownianSystem Ω) (Z : BrownianSystem A) (V : ℝ≥0)
    (J Q : (Bool × Ω) × A → ℝ) (hJm : Measurable J) (hQm : Measurable Q)
    (hJ : HasSubgaussianMGF J (4 * V) (actualRowBaseLaw W Z))
    (hQ : ∀ᵐ u ∂actualRowBaseLaw W Z, 0 ≤ Q u ∧ Q u ≤ 4 * (V : ℝ))
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let ν := actualParisiFullQuerySpinLaw W Z β V
    (actualParisiFullMixedRowsLaw W Z β V n).real
      {u | (n : ℝ) * η ≤ |∑ i : Fin n,
        centeredObservable ν (actualRowInformation β W V J Q) (u i)|} ≤
      2 * Real.exp (-(n : ℝ) * min
        (η ^ 2 / (2048 * (1 + (V : ℝ)) ^ 2)) (η / (64 * (1 + (V : ℝ))))) := by
  have h := iid_rowInformation_abs (measurable_actualRowLink β W V) hJm hQm
    (ae_of_all _ (fun u => ⟨(actualRowLink_bounds β W V u).1.le, (actualRowLink_bounds β W V u).2⟩))
    (actualRowLink_integral β W Z V) V hJ hQ hn hη
  simpa only [actual_linkedRowLaw_eq, actualRowInformation, actualParisiFullMixedRowsLaw] using h

theorem actualRowInformation_iid_strict_upper
    (β : ℝ) (W : BrownianSystem Ω) (Z : BrownianSystem A) (V : ℝ≥0)
    (J Q : (Bool × Ω) × A → ℝ) (hJm : Measurable J) (hQm : Measurable Q)
    (hJ : HasSubgaussianMGF J (4 * V) (actualRowBaseLaw W Z))
    (hQ : ∀ᵐ u ∂actualRowBaseLaw W Z, 0 ≤ Q u ∧ Q u ≤ 4 * (V : ℝ))
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let ν := actualParisiFullQuerySpinLaw W Z β V
    (actualParisiFullMixedRowsLaw W Z β V n).real
      {u | (n : ℝ) * η < ∑ i : Fin n,
        centeredObservable ν (actualRowInformation β W V J Q) (u i)} ≤
      Real.exp (-((n : ℝ) / 2048) *
        min (η ^ 2 / (1 + (V : ℝ)) ^ 2) (η / (1 + (V : ℝ)))) := by
  have h := iid_rowInformation_strict_upper (measurable_actualRowLink β W V) hJm hQm
    (ae_of_all _ (fun u => ⟨(actualRowLink_bounds β W V u).1.le, (actualRowLink_bounds β W V u).2⟩))
    (actualRowLink_integral β W Z V) V hJ hQ hn hη
  simpa only [actual_linkedRowLaw_eq, actualRowInformation, actualParisiFullMixedRowsLaw] using h

end SKConstants.Completion.LM4

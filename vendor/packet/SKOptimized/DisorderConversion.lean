module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace SKOptimized.Disorder

theorem integrable_probability_mass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hprob : ∀ ω, f ω ∈ Icc (0 : ℝ) 1) :
    Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf
  apply Eventually.of_forall
  intro ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hprob ω).1] using (hprob ω).2

theorem annealed_bad_mass_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {A : Set Ω} {e : ℝ}
    (hf : AEStronglyMeasurable f μ) (hprob : ∀ ω, f ω ∈ Icc (0 : ℝ) 1)
    (hA : MeasurableSet A) (he : 0 ≤ e) (hgood : ∀ ω ∈ A, f ω ≤ e) :
    (∫ ω, f ω ∂μ) ≤ μ.real Aᶜ + e := by
  have hfi := integrable_probability_mass hf hprob
  calc
    (∫ ω, f ω ∂μ) ≤ ∫ ω, e + Aᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      apply integral_mono hfi
        ((integrable_const e).add ((integrable_const (1 : ℝ)).indicator hA.compl))
      intro ω
      by_cases hω : ω ∈ A
      · simp only [Pi.add_apply, Set.indicator_of_notMem (show ω ∉ Aᶜ by simpa)]
        simpa only [add_zero] using hgood ω hω
      · simp only [Pi.add_apply, Set.indicator_of_mem (show ω ∈ Aᶜ from hω)]
        linarith [(hprob ω).2]
    _ = μ.real Aᶜ + e := by
      rw [integral_add (integrable_const e)
        ((integrable_const (1 : ℝ)).indicator hA.compl),
        integral_const, integral_indicator_const _ hA.compl]
      simp only [probReal_univ, smul_eq_mul, one_mul, mul_one]
      ring

theorem annealed_bad_mass_le_multiplicity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {A : Set Ω}
    {M e : ℝ} (hf : AEStronglyMeasurable f μ)
    (hprob : ∀ ω, f ω ∈ Icc (0 : ℝ) 1) (hA : MeasurableSet A)
    (hM : 0 ≤ M) (he : 0 ≤ e) (hgood : ∀ ω ∈ A, f ω ≤ M * e) :
    (∫ ω, f ω ∂μ) ≤ μ.real Aᶜ + M * e :=
  annealed_bad_mass_le hf hprob hA (mul_nonneg hM he) hgood

theorem annealed_union_bad_mass_le {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {g : I → Ω → ℝ} {A : Set Ω} {e : ℝ}
    (hf : AEStronglyMeasurable f μ) (hprob : ∀ ω, f ω ∈ Icc (0 : ℝ) 1)
    (hA : MeasurableSet A) (he : 0 ≤ e)
    (hunion : ∀ ω ∈ A, f ω ≤ ∑ i, g i ω)
    (heach : ∀ i ω, ω ∈ A → g i ω ≤ e) :
    (∫ ω, f ω ∂μ) ≤ μ.real Aᶜ + (Fintype.card I : ℝ) * e := by
  apply annealed_bad_mass_le_multiplicity hf hprob hA (Nat.cast_nonneg _) he
  intro ω hω
  calc
    f ω ≤ ∑ i, g i ω := hunion ω hω
    _ ≤ ∑ _i : I, e := Finset.sum_le_sum (fun i _ => heach i ω hω)
    _ = (Fintype.card I : ℝ) * e := by simp

theorem annealed_bad_mass_tendsto_zero {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) {f : ∀ n, Ω n → ℝ}
    {A : ∀ n, Set (Ω n)} {e : ℕ → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (μ n))
    (hprob : ∀ n ω, f n ω ∈ Icc (0 : ℝ) 1)
    (hA : ∀ n, MeasurableSet (A n)) (he : ∀ n, 0 ≤ e n)
    (hgood : ∀ n ω, ω ∈ A n → f n ω ≤ e n)
    (hfailure : Tendsto (fun n => (μ n).real (A n)ᶜ) atTop (𝓝 0))
    (hconditional : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, f n ω ∂μ n) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => (μ n).real (A n)ᶜ + e n) atTop (𝓝 0) := by
    simpa only [add_zero] using hfailure.add hconditional
  apply squeeze_zero (fun n => integral_nonneg (fun ω => (hprob n ω).1))
    (fun n => ?_) hsum
  let := hμ n
  exact annealed_bad_mass_le (hf n) (hprob n) (hA n) (he n) (hgood n)

theorem annealed_bad_mass_tendsto_zero_of_failure_bound {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) {f : ∀ n, Ω n → ℝ}
    {A : ∀ n, Set (Ω n)} {d e : ℕ → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (μ n))
    (hprob : ∀ n ω, f n ω ∈ Icc (0 : ℝ) 1)
    (hA : ∀ n, MeasurableSet (A n)) (he : ∀ n, 0 ≤ e n)
    (hgood : ∀ n ω, ω ∈ A n → f n ω ≤ e n)
    (hfailure_bound : ∀ n, (μ n).real (A n)ᶜ ≤ d n)
    (hfailure : Tendsto d atTop (𝓝 0)) (hconditional : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, f n ω ∂μ n) atTop (𝓝 0) := by
  have hactual_failure : Tendsto (fun n => (μ n).real (A n)ᶜ) atTop (𝓝 0) :=
    squeeze_zero (fun _ => measureReal_nonneg) hfailure_bound hfailure
  exact annealed_bad_mass_tendsto_zero hμ hf hprob hA he hgood
    hactual_failure hconditional

theorem annealed_bad_mass_tendsto_zero_of_eventual_bounds {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
    (hμ : ∀ n, IsProbabilityMeasure (μ n)) {f : ∀ n, Ω n → ℝ}
    {A : ∀ n, Set (Ω n)} {d e : ℕ → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (μ n))
    (hprob : ∀ n ω, f n ω ∈ Icc (0 : ℝ) 1)
    (hA : ∀ n, MeasurableSet (A n))
    (he : ∀ᶠ n : ℕ in atTop, 0 ≤ e n)
    (hgood : ∀ᶠ n : ℕ in atTop, ∀ ω ∈ A n, f n ω ≤ e n)
    (hfailure_bound : ∀ᶠ n : ℕ in atTop, (μ n).real (A n)ᶜ ≤ d n)
    (hfailure : Tendsto d atTop (𝓝 0)) (hconditional : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, f n ω ∂μ n) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => d n + e n) atTop (𝓝 0) := by
    simpa only [add_zero] using hfailure.add hconditional
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    integral_nonneg (fun ω => (hprob n ω).1))) ?_ hsum
  filter_upwards [he, hgood, hfailure_bound] with n hen hgoodn hfailuren
  let := hμ n
  exact (annealed_bad_mass_le (hf n) (hprob n) (hA n) hen hgoodn).trans
    (add_le_add hfailuren le_rfl)

end SKOptimized.Disorder

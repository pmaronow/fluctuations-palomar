module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SKConstants.Completion.LM4

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def linkedRowLaw (μ : Measure Ω) (ell : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (ell ω))

theorem linkedRowLaw_absolutelyContinuous (ell : Ω → ℝ) :
    linkedRowLaw μ ell ≪ μ := withDensity_absolutelyContinuous _ _

theorem linkedRowLaw_le_two {ell : Ω → ℝ}
    (hbound : ∀ᵐ ω ∂μ, ell ω ≤ 2) :
    linkedRowLaw μ ell ≤ (2 : ℝ≥0∞) • μ := by
  calc
    _ ≤ μ.withDensity (fun _ => (2 : ℝ≥0∞)) :=
      withDensity_mono (hbound.mono (fun ω hω => by
        simpa using ENNReal.ofReal_le_ofReal hω))
    _ = _ := withDensity_const _

theorem linkedRowLaw_isProbability [IsProbabilityMeasure μ]
    {ell : Ω → ℝ} (hell : Measurable ell)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2)
    (hnorm : ∫ ω, ell ω ∂μ = 1) :
    IsProbabilityMeasure (linkedRowLaw μ ell) := by
  have hI : Integrable ell μ := Integrable.of_bound hell.aestronglyMeasurable 2
    (hbound.mono (fun ω hω => by simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2))
  constructor
  rw [linkedRowLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (hbound.mono (fun _ hω => hω.1)), hnorm]
  norm_num

theorem linkedRowLaw_integrable {ell : Ω → ℝ}
    (hbound : ∀ᵐ ω ∂μ, ell ω ≤ 2) {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable f (linkedRowLaw μ ell) :=
  (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono_measure
    (linkedRowLaw_le_two hbound)

theorem linkedRowLaw_lintegral_le_two {ell : Ω → ℝ}
    (hbound : ∀ᵐ ω ∂μ, ell ω ≤ 2) (f : Ω → ℝ≥0∞) :
    (∫⁻ ω, f ω ∂linkedRowLaw μ ell) ≤ 2 * ∫⁻ ω, f ω ∂μ := by
  simpa using lintegral_mono' (linkedRowLaw_le_two hbound) (fun _ => le_rfl (a := f _))

theorem linkedRowLaw_real_le_two [IsFiniteMeasure μ]
    {ell : Ω → ℝ} (hbound : ∀ᵐ ω ∂μ, ell ω ≤ 2) (s : Set Ω) :
    (linkedRowLaw μ ell).real s ≤ 2 * μ.real s := by
  have h := (linkedRowLaw_le_two hbound) s
  have hh : ((2 : ℝ≥0∞) • μ) s ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ s)
  have ht := ENNReal.toReal_mono hh h
  simpa only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat] using ht

theorem linkedRowLaw_log_lower_tail [IsProbabilityMeasure μ]
    {ell : Ω → ℝ} (hell : Measurable ell) (t : ℝ) :
    (linkedRowLaw μ ell).real {ω | Real.log (ell ω) ≤ -t} ≤ Real.exp (-t) := by
  let A := {ω | Real.log (ell ω) ≤ -t}
  have hA : MeasurableSet A := measurableSet_le (hell.log) measurable_const
  have hbound : linkedRowLaw μ ell A ≤ ENNReal.ofReal (Real.exp (-t)) := by
    rw [linkedRowLaw, withDensity_apply _ hA]
    calc
      _ ≤ ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-t)) ∂μ := by
        apply setLIntegral_mono' hA
        intro ω hω
        apply ENNReal.ofReal_le_ofReal
        by_cases hpos : 0 < ell ω
        · exact (Real.log_le_iff_le_exp hpos).mp hω
        · exact (le_of_not_gt hpos).trans (Real.exp_pos _).le
      _ ≤ ∫⁻ _ω, ENNReal.ofReal (Real.exp (-t)) ∂μ :=
        setLIntegral_le_lintegral _ _
      _ = _ := by simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (Real.exp_pos _).le)

theorem linkedRowLaw_log_le_log_two {ell : Ω → ℝ} (hell : Measurable ell)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2) :
    ∀ᵐ ω ∂linkedRowLaw μ ell, Real.log (ell ω) ≤ Real.log 2 := by
  apply (ae_withDensity_iff (hell.ennreal_ofReal)).mpr
  filter_upwards [hbound] with ω hω hne
  have hpos : 0 < ell ω := by simpa using hne
  exact Real.log_le_log hpos hω.2

theorem integral_linkedRowLaw {ell f : Ω → ℝ} (hell : Measurable ell)
    (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ ell ω) :
    (∫ ω, f ω ∂linkedRowLaw μ ell) = ∫ ω, ell ω * f ω ∂μ := by
  rw [linkedRowLaw, integral_withDensity_eq_integral_toReal_smul hell.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hnonneg] with ω hω
  simp only [ENNReal.toReal_ofReal hω, smul_eq_mul]

end SKConstants.Completion.LM4

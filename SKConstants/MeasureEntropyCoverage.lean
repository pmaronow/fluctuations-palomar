module

public import SKConstants.JointGibbs
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

public section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory InformationTheory

namespace SKConstants

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

theorem integrable_finiteWeightMeasure (p : V → ℝ) (f : V → ℝ) :
    Integrable f (finiteWeightMeasure p) := by
  unfold finiteWeightMeasure
  apply integrable_finsetSum_measure.mpr
  intro x _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem integral_finiteWeightMeasure (p : V → ℝ) (hp : ∀ x, 0 ≤ p x) (f : V → ℝ) :
    ∫ x, f x ∂finiteWeightMeasure p = ∑ x, p x * f x := by
  unfold finiteWeightMeasure
  rw [integral_finsetSum_measure]
  · simp [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp _)]
  · intro x _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem finiteWeightMeasure_withDensity_ratio (p q : V → ℝ)
    (_hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x) :
    (finiteWeightMeasure q).withDensity (fun x ↦ ENNReal.ofReal (p x / q x)) =
      finiteWeightMeasure p := by
  unfold finiteWeightMeasure
  rw [← Measure.sum_fintype, withDensity_sum, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [withDensity_smul_measure, dirac_withDensity, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (hq x).le]
  congr 1
  field_simp [(hq x).ne']

theorem klDiv_finiteWeightMeasure (p q : V → ℝ)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x, p x = 1) (hq_sum : ∑ x, q x = 1) :
    klDiv (finiteWeightMeasure p) (finiteWeightMeasure q) = ENNReal.ofReal (finiteKL p q) := by
  have : IsProbabilityMeasure (finiteWeightMeasure p) :=
    finiteWeightMeasure_probability p (fun x ↦ (hp x).le) hp_sum
  have : IsProbabilityMeasure (finiteWeightMeasure q) :=
    finiteWeightMeasure_probability q (fun x ↦ (hq x).le) hq_sum
  have hdensity := finiteWeightMeasure_withDensity_ratio p q (fun x ↦ (hp x).le) hq
  have hac : finiteWeightMeasure p ≪ finiteWeightMeasure q := by
    rw [← hdensity]
    exact withDensity_absolutelyContinuous _ _
  have hrn : (finiteWeightMeasure p).rnDeriv (finiteWeightMeasure q) =ᵐ[finiteWeightMeasure q]
      (fun x ↦ ENNReal.ofReal (p x / q x)) := by
    rw [← hdensity]
    exact Measure.rnDeriv_withDensity _ (measurable_of_countable _)
  have hllr : llr (finiteWeightMeasure p) (finiteWeightMeasure q) =ᵐ[finiteWeightMeasure p]
      (fun x ↦ Real.log (p x / q x)) := by
    filter_upwards [hrn.filter_mono hac.ae_le] with x hx
    simp only [llr, hx, ENNReal.toReal_ofReal (div_pos (hp x) (hq x)).le]
  have hint : Integrable (llr (finiteWeightMeasure p) (finiteWeightMeasure q))
      (finiteWeightMeasure p) := integrable_finiteWeightMeasure _ _
  rw [klDiv_of_ac_of_integrable hac hint]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae hllr, integral_finiteWeightMeasure p (fun x ↦ (hp x).le)]
  rfl

theorem map_finite_endpoint_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → V) (hX : Measurable X) :
    μ.map X = finiteWeightMeasure (fun v ↦ μ.real (X ⁻¹' {v})) := by
  rw [← Measure.sum_smul_dirac (μ.map X), Measure.sum_fintype]
  unfold finiteWeightMeasure
  apply Finset.sum_congr rfl
  intro v _
  rw [Measure.map_apply hX (measurableSet_singleton v)]
  change μ (X ⁻¹' {v}) • Measure.dirac v =
    ENNReal.ofReal ((μ (X ⁻¹' {v})).toReal) • Measure.dirac v
  rw [ENNReal.ofReal_toReal (measure_ne_top μ _)]

theorem finite_endpoint_probability_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → V) (hX : Measurable X) :
    ∑ v, μ.real (X ⁻¹' {v}) = 1 := by
  have h := sum_measureReal_preimage_singleton Finset.univ
    (fun v _ ↦ (measurableSet_singleton v).preimage hX) (μ := μ)
  simpa using h

theorem finite_endpoint_KL_le {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → V) (hX : Measurable X)
    (hp : ∀ v, 0 < μ.real (X ⁻¹' {v})) (hq : ∀ v, 0 < ν.real (X ⁻¹' {v}))
    (K : ℝ) (hK : 0 ≤ K) (hKL : klDiv μ ν ≤ ENNReal.ofReal K) :
    finiteKL (fun v ↦ μ.real (X ⁻¹' {v})) (fun v ↦ ν.real (X ⁻¹' {v})) ≤ K := by
  have h := (klDiv_map_le μ ν hX).trans hKL
  rw [map_finite_endpoint_eq μ X hX, map_finite_endpoint_eq ν X hX,
    klDiv_finiteWeightMeasure _ _ hp hq
      (finite_endpoint_probability_sum μ X hX) (finite_endpoint_probability_sum ν X hX)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp h

theorem measureKL_finite_endpoint_coverage {Ω : Type*} [MeasurableSpace Ω] [DecidableEq V]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → V) (hX : Measurable X)
    (hp : ∀ v, 0 < μ.real (X ⁻¹' {v})) (hq : ∀ v, 0 < ν.real (X ⁻¹' {v}))
    (A : Finset V) (K alpha : ℝ) (hK : 0 ≤ K)
    (hKL : klDiv μ ν ≤ ENNReal.ofReal K) (halpha : 0 < alpha)
    (hMass : alpha ≤ μ.real (X ⁻¹' (A : Set V))) :
    Real.exp (-(K + Real.log 2) / alpha) ≤ ν.real (X ⁻¹' (A : Set V)) := by
  have hμ := sum_measureReal_preimage_singleton A
    (fun v _ ↦ (measurableSet_singleton v).preimage hX) (μ := μ)
  have hν := sum_measureReal_preimage_singleton A
    (fun v _ ↦ (measurableSet_singleton v).preimage hX) (μ := ν)
  rw [← hν]
  exact finiteKL_uniform_coverage _ _ A K alpha hp hq
    (finite_endpoint_probability_sum μ X hX) (finite_endpoint_probability_sum ν X hX)
    (finite_endpoint_KL_le μ ν X hX hp hq K hK hKL) halpha (by rwa [hμ])

end SKConstants

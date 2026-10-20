module

public import ScalarFiniteParisiBridge
public import MacroSquareCompletion
public import SKFluctuationsOAI.Probability.ParisiFinite.Mix

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

attribute [local instance] Measure.Subtype.measureSpace

def uniformOrderMass : ProbabilityMeasure ParisiFinite.OrderPoint :=
  ⟨volume, ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    simp⟩⟩

def quantileOrderMap (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (u : ParisiFinite.OrderPoint) : ParisiFinite.OrderPoint :=
  ⟨q u, hqb u u.property⟩

theorem quantileOrderMap_measurable (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    Measurable (quantileOrderMap q hqb) := by
  have hm : Monotone (fun u : ParisiFinite.OrderPoint => q u) :=
    fun u v huv => hq u.property v.property huv
  exact hm.measurable.subtype_mk

def quantileLaw (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    ProbabilityMeasure ParisiFinite.OrderPoint :=
  uniformOrderMass.map (quantileOrderMap q hqb)

def quantileMassProfile (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    boundedMassProfiles :=
  scalarProfileOfParisiMeasure (quantileLaw q hqb)

theorem quantileMassProfile_mem (q : ℝ → ℝ)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    quantileMassProfile q hqb ∈ scalarProfiles :=
  scalarProfileOfParisiMeasure_mem _

theorem quantileMassProfile_cdf (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    (quantileMassProfile q hqb).val t =
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
        {u | q (u : ℝ) ≤ t} := by
  change (quantileLaw q hqb : Measure ParisiFinite.OrderPoint).real
    {x | (x : ℝ) ≤ t} = _
  unfold quantileLaw
  change ((uniformOrderMass.map (quantileOrderMap q hqb) :
    Measure ParisiFinite.OrderPoint) {x | (x : ℝ) ≤ t}).toReal = _
  rw [ProbabilityMeasure.map_apply' _ (quantileOrderMap_measurable q hq hqb).aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)]
  rfl

theorem quantileLaw_integral_square (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    (∫ x : ParisiFinite.OrderPoint, (x : ℝ) ^ 2
        ∂(quantileLaw q hqb : Measure ParisiFinite.OrderPoint)) =
      ∫ u in (0 : ℝ)..1, q u ^ 2 := by
  unfold quantileLaw
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map_of_stronglyMeasurable (quantileOrderMap_measurable q hq hqb)
      (by fun_prop : StronglyMeasurable (fun x : ParisiFinite.OrderPoint => (x : ℝ) ^ 2))]
  change (∫ u : ParisiFinite.OrderPoint, q u ^ 2) = _
  rw [integral_subtype measurableSet_Icc (fun u : ℝ => q u ^ 2),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

theorem quantileMassProfile_penalty (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    scalarPenalty (quantileMassProfile q hqb) =
      (1 - (∫ u in (0 : ℝ)..1, q u ^ 2)) / 2 := by
  let ρ := quantileLaw q hqb
  have hs : Integrable (fun x : ParisiFinite.OrderPoint => (x : ℝ) ^ 2)
      (ρ : Measure ParisiFinite.OrderPoint) := by
    apply Integrable.of_bound (by fun_prop) 1
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [x.property.1, x.property.2]
  have hc := ParisiFinite.integral_cdf_mul ρ continuous_id
    (by norm_num : (0 : ℝ) ≤ 1)
    (by intro t ht; simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2)
  simp only [id_eq, integral_id, one_pow] at hc
  rw [integral_div] at hc
  rw [integral_sub (integrable_const 1) hs, integral_const] at hc
  rw [scalarPenalty_eq]
  have he : (∫ u in (0 : ℝ)..1, u * (quantileMassProfile q hqb).val u) =
      ∫ u in (0 : ℝ)..1, (ρ : Measure ParisiFinite.OrderPoint).real
        {x | (x : ℝ) ≤ u} * u := by
    apply intervalIntegral.integral_congr
    intro u _
    change u * ((ρ : Measure ParisiFinite.OrderPoint).real {x | (x : ℝ) ≤ u}) = _
    ring
  rw [he, hc, quantileLaw_integral_square q hq hqb]
  simp [Measure.real]

end OAI.SKFluctuations.LaplaceWindowFormalization

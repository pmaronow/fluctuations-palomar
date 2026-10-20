module

public import WeakTraceCompactness
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem weak_integral_tendsto_of_uniform_domination
    {ι : Type*} {L : Filter ι} [L.NeBot]
    (μs : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs L (𝓝 μ)) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hdom : ∀ j : ι, (μs j : Measure ℝ) ≤ ρ) (f : ℝ → ℝ)
    (hf : Integrable f ρ) :
    Tendsto (fun j => ∫ r, f r ∂(μs j : Measure ℝ)) L
      (𝓝 (∫ r, f r ∂(μ : Measure ℝ))) := by
  have hμ := weak_limit_le_of_uniform_domination μs μ hweak ρ (Eventually.of_forall hdom)
  have hfμ := hf.mono_measure hμ
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g,hgerr,hg⟩ := hf.exists_boundedContinuous_integral_sub_le (by positivity : 0 < ε/4)
  have ht := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak g
  have hnear := (Metric.tendsto_nhds.mp ht) (ε/2) (by positivity)
  have hdiff (ν : Measure ℝ) (hν : ν ≤ ρ) :
      |(∫ r, f r ∂ν) - ∫ r, g r ∂ν| ≤ ε/4 := by
    have hfi := hf.mono_measure hν
    have hgi := hg.mono_measure hν
    calc
      |(∫ r, f r ∂ν) - ∫ r, g r ∂ν| = ‖∫ r, f r-g r ∂ν‖ := by
        rw [integral_sub hfi hgi,Real.norm_eq_abs]
      _ ≤ ∫ r, ‖f r-g r‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ r, ‖f r-g r‖ ∂ρ := integral_mono_measure hν
        (ae_of_all _ (fun _ => norm_nonneg _)) (hf.sub hg).norm
      _ ≤ ε/4 := hgerr
  filter_upwards [hnear] with j hj
  rw [Real.dist_eq] at hj ⊢
  have hjs := hdiff (μs j : Measure ℝ) (hdom j)
  have hms := hdiff (μ : Measure ℝ) hμ
  have htriangle : |(∫ r, f r ∂(μs j : Measure ℝ)) - ∫ r, f r ∂(μ : Measure ℝ)| ≤
      |(∫ r, f r ∂(μs j : Measure ℝ)) - ∫ r, g r ∂(μs j : Measure ℝ)| +
      |(∫ r, g r ∂(μs j : Measure ℝ)) - ∫ r, g r ∂(μ : Measure ℝ)| +
      |(∫ r, g r ∂(μ : Measure ℝ)) - ∫ r, f r ∂(μ : Measure ℝ)| := by
    have heq : (∫ r, f r ∂(μs j : Measure ℝ)) - ∫ r, f r ∂(μ : Measure ℝ) =
        ((∫ r, f r ∂(μs j : Measure ℝ)) - ∫ r, g r ∂(μs j : Measure ℝ)) +
        ((∫ r, g r ∂(μs j : Measure ℝ)) - ∫ r, g r ∂(μ : Measure ℝ)) +
        ((∫ r, g r ∂(μ : Measure ℝ)) - ∫ r, f r ∂(μ : Measure ℝ)) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_sub_comm (∫ r, g r ∂(μ : Measure ℝ)) (∫ r, f r ∂(μ : Measure ℝ))] at htriangle
  linarith

theorem weak_contact_weighted_integral_tendsto
    {ι : Type*} {L : Filter ι} [L.NeBot]
    (μs : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs L (𝓝 μ)) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hdom : ∀ j : ι, (μs j : Measure ℝ) ≤ ρ) (weight : ℝ → ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) (hw : IntegrableOn weight A ρ) :
    Tendsto (fun j => ∫ r in A, weight r ∂(μs j : Measure ℝ)) L
      (𝓝 (∫ r in A, weight r ∂(μ : Measure ℝ))) := by
  have hi : Integrable (A.indicator weight) ρ := (integrable_indicator_iff hA).mpr hw
  have ht := weak_integral_tendsto_of_uniform_domination μs μ hweak ρ hdom
    (A.indicator weight) hi
  simpa only [integral_indicator hA] using ht

end OAI.SKFluctuations.LaplaceWindowFormalization

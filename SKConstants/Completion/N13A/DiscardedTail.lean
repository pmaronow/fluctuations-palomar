module

public import SKConstants.Completion.N13A.EnergyMeasurable
public import SKConstants.Completion.N13A.ConditionalTail
public import SKConstants.Completion.N13A.VarianceRates

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SKConstants.Completion.N13A
open SKConstantsOAI.ZeroTemperatureSK Blueprint

theorem discarded_tail_from_conditional_variance {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) (hn : 1 ≤ n)
    (C B w : ℝ) (hC : 0<C) (hB : B ≤ (n:ℝ)^(-w))
    (hvar : ∀ y : SharpInput p n, sharpRows W β hβ p n y ∈ gramGood W β hβ p n →
      discardedVariance (sharpRows W β hβ p n y) ≤
        C/n*((n:ℝ)^(-p.a) + weightedSq W β hβ (sharpRows W β hβ p n y) + (n:ℝ)^(-p.b)))
    (hmgf : ∀ S : Set (RowArray p n), MeasurableSet S → S ⊆ gramGood W β hβ p n →
      ∀ θ : ℝ,
        (∫⁻ y in (sharpRows W β hβ p n) ⁻¹' S,
          ENNReal.ofReal (Real.exp (θ*sharpDiscarded W β hβ p n y)) ∂sharpLinkedLaw W β hβ p n) =
        ∫⁻ y in (sharpRows W β hβ p n) ⁻¹' S,
          ENNReal.ofReal (Real.exp (θ^2*discardedVariance (sharpRows W β hβ p n y)/2))
            ∂sharpLinkedLaw W β hβ p n) :
    (sharpLinkedLaw W β hβ p n).real
      {y | (sharpRows W β hβ p n y ∈ gramGood W β hβ p n ∧
        weightedSq W β hβ (sharpRows W β hβ p n y) ≤ B) ∧
          (n:ℝ)^(-p.z) < |sharpDiscarded W β hβ p n y|} ≤
      2*Real.exp (-((1/(6*C))*(n:ℝ)^(1+min p.a (min w p.b)-2*p.z))) := by
  let S : Set (RowArray p n) := gramGood W β hβ p n ∩ {z | weightedSq W β hβ z ≤ B}
  have hS : MeasurableSet S := (measurableSet_gramGood W β hβ p n).inter
    (measurableSet_le (measurable_weightedSq W β hβ p n) measurable_const)
  let V := 3*C*(n:ℝ)^(-1-min p.a (min w p.b))
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hV : 0<V := by dsimp [V]; positivity
  have hvc : ∀ y : SharpInput p n, sharpRows W β hβ p n y ∈ S →
      discardedVariance (sharpRows W β hβ p n y) ≤ V := by
    intro y hy
    exact (hvar y hy.1).trans (variance_scale_le _ C p.a p.b w _ hnR hC.le (hy.2.trans hB))
  have hM := conditional_mgf_bound_on_row_event (sharpLinkedLaw W β hβ p n)
    (sharpRows W β hβ p n) (measurable_sharpRows W β hβ p n) S hS
    (sharpDiscarded W β hβ p n) (fun z => discardedVariance z) V hvc
    (hmgf S hS inter_subset_left)
  have htail := restricted_gaussian_two_sided_tail (sharpLinkedLaw W β hβ p n)
    ((sharpRows W β hβ p n) ⁻¹' S) ((measurable_sharpRows W β hβ p n) hS)
    (sharpDiscarded W β hβ p n) (measurable_sharpDiscarded W β hβ p n).aemeasurable.restrict
    V ((n:ℝ)^(-p.z)) hV (Real.rpow_pos_of_pos hn0 _) hM
  have hreal := (ENNReal.toReal_mono ENNReal.ofReal_ne_top htail).trans_eq
    (ENNReal.toReal_ofReal (by positivity))
  change (sharpLinkedLaw W β hβ p n).real
    {y | (sharpRows W β hβ p n y ∈ gramGood W β hβ p n ∧
      weightedSq W β hβ (sharpRows W β hβ p n y) ≤ B) ∧
        (n:ℝ)^(-p.z) < |sharpDiscarded W β hβ p n y|} ≤ _ at hreal
  dsimp only [V] at hreal
  rw [neg_div, gaussian_chernoff_exponent _ C _ p.z hn0 hC] at hreal
  exact hreal

theorem identDistrib_real_gt {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {F : A → ℝ} {G : B → ℝ}
    (h : IdentDistrib F G μ ν) (t : ℝ) :
    μ.real {y | t < F y} = ν.real {y | t < G y} :=
  congrArg ENNReal.toReal (h.measure_mem_eq (s := Ioi t) measurableSet_Ioi)

end SKConstants.Completion.N13A

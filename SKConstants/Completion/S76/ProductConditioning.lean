module

public import SKConstants.Completion.S76.QueryTransforms

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.S76
open SKConstantsOAI.ZeroTemperatureSK LJ LJ3 LC1
variable {Ω A S T : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSpace S] [MeasurableSpace T]

theorem setIntegral_le_of_conditional_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (f : Ω → ℝ) (B : ℝ)
    (hbound : μ E ≠ 0 → (∫ w, f w ∂μ[|E]) ≤ B) :
    (∫ w in E, f w ∂μ) ≤ μ.real E * B := by
  by_cases h0 : μ E = 0
  · simp [Measure.restrict_eq_zero.mpr h0, measureReal_def, h0]
  · have hc := hbound h0
    rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv] at hc
    have hp : 0 < μ.real E := ENNReal.toReal_pos h0 (measure_ne_top _ _)
    calc
      _ = μ.real E * ((μ.real E)⁻¹ * ∫ w in E, f w ∂μ) := by
        rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hp.le

theorem conditional_integral_prod (μ : Measure Ω) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : Ω → S) (R : A → T) (hP : Measurable P) (hR : Measurable R)
    (f : Ω → ℝ) (hf : Integrable f μ) (B : ℝ)
    (hbound : ∀ D : Set S, MeasurableSet D → μ (P ⁻¹' D) ≠ 0 →
      (∫ w, f w ∂μ[|P ⁻¹' D]) ≤ B)
    (E : Set (S × T)) (hE : MeasurableSet E)
    (hE0 : (μ.prod ν) ((fun u : Ω × A => (P u.1, R u.2)) ⁻¹' E) ≠ 0) :
    (∫ u, f u.1 ∂(μ.prod ν)[|(fun u : Ω × A => (P u.1, R u.2)) ⁻¹' E]) ≤ B := by
  classical
  let D := (fun u : Ω × A => (P u.1, R u.2)) ⁻¹' E
  have hD : MeasurableSet D := hE.preimage (hP.prodMap hR)
  let F : Ω × A → ℝ := D.indicator (fun u => f u.1)
  let G : Ω × A → ℝ := D.indicator (fun _ => 1)
  have hiF : Integrable F (μ.prod ν) :=
    ((measurePreserving_fst (μ := μ) (ν := ν)).integrable_comp_of_integrable hf).indicator hD
  have hiG : Integrable G (μ.prod ν) := (integrable_const (1 : ℝ)).indicator hD
  have htest (a : A) : (∫ w, F (w, a) ∂μ) ≤ (∫ w, G (w, a) ∂μ) * B := by
    let Da := (fun s : S => (s, R a)) ⁻¹' E
    have hDa : MeasurableSet Da := hE.preimage (measurable_id.prodMk measurable_const)
    have heF : (fun w => F (w, a)) = (P ⁻¹' Da).indicator f := rfl
    have heG : (fun w => G (w, a)) = (P ⁻¹' Da).indicator (fun _ => (1 : ℝ)) := rfl
    rw [heF, heG, integral_indicator (hDa.preimage hP), integral_indicator_const 1 (hDa.preimage hP)]
    simp only [smul_eq_mul, mul_one]
    exact setIntegral_le_of_conditional_bound μ _ f B (hbound Da hDa)
  have htotal : (∫ u in D, f u.1 ∂μ.prod ν) ≤ (μ.prod ν).real D * B := by
    rw [← integral_indicator hD, show D.indicator (fun u => f u.1) = F from rfl,
      integral_prod_symm _ hiF]
    apply (integral_mono_ae hiF.integral_prod_right (hiG.integral_prod_right.mul_const B)
      (ae_of_all _ htest)).trans_eq
    rw [integral_mul_const, ← integral_prod_symm _ hiG, integral_indicator_const 1 hD]
    simp only [smul_eq_mul, mul_one]
  change (∫ u, f u.1 ∂(μ.prod ν)[|D]) ≤ B
  rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  apply (mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr measureReal_nonneg)).trans_eq
  have hp : (μ.prod ν).real D ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hE0, measure_ne_top _ _⟩
  field_simp

def fieldBrownianPath (β : ℝ) (s : ℝ≥0) : ScalarContinuousPath s → ScalarContinuousPath s :=
  fun p => scalarPathFromPast s (boundedDriftRecoverBrownianPast (actualParisiFullScalarDrift β) s p)

theorem measurable_fieldBrownianPath (β : ℝ) (s : ℝ≥0) : Measurable (fieldBrownianPath β s) :=
  (measurable_scalarPathFromPast s).comp
    (measurable_boundedDriftRecoverBrownianPast (actualParisiFullScalarDrift β) s)

theorem fieldBrownianPath_actual (W : BrownianSystem Ω) (β : ℝ) (s : ℝ≥0) :
    (fun w => fieldBrownianPath β s (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w))
      =ᵐ[W.law] brownianFinitePath W s := by
  filter_upwards [boundedDriftRecoverBrownianPast_actual W (actualParisiFullScalarDrift β) s,
    LM4b.brownianFinitePathFromPast_ae W s] with w hr hb
  exact (congrArg (scalarPathFromPast s) hr).trans hb

theorem posterior_conditional_brownian_prefix_tail (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (ScalarContinuousPath (t 0))) (hE : MeasurableSet E)
    (hE0 : W.law ((brownianFinitePath W (t 0)) ⁻¹' E) ≠ 0)
    (n : ℕ) (h : ℝ) (hh : (t n : ℝ) - t 0 ≤ h) (hh0 : 0 < h) (a : ℝ) (ha : 0 < a) :
    (W.law[|(brownianFinitePath W (t 0)) ⁻¹' E]).real
      {w | ∃ k : ℕ, k ≤ n ∧ a ≤ |actualParisiMagnetizationObservable W β (t k) w -
        actualParisiMagnetizationObservable W β (t 0) w|} ≤
          2 * Real.exp (-(a ^ 2 / (2 * h))) := by
  let F := (fieldBrownianPath β (t 0)) ⁻¹' E
  have hset : (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' F =ᵐ[W.law]
      (brownianFinitePath W (t 0)) ⁻¹' E := by
    filter_upwards [fieldBrownianPath_actual W β (t 0)] with w hw
    change (fieldBrownianPath β (t 0) _ ∈ E) = _
    rw [hw]
    rfl
  have hcond : W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' F] =
      W.law[|(brownianFinitePath W (t 0)) ⁻¹' E] := by
    unfold ProbabilityTheory.cond
    rw [measure_congr hset, Measure.restrict_congr_set hset]
  have h0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' F) ≠ 0 := by
    rwa [measure_congr hset]
  have hb := actualPosterior_conditional_any_prefix_tail W β hβ t ht F
    (hE.preimage (measurable_fieldBrownianPath β (t 0))) h0 n h hh hh0 a ha
  rwa [hcond] at hb

theorem posterior_conditional_pair_prefix_tail (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (hE : MeasurableSet E)
    (hE0 : (W.law.prod Z.law) ((pairPast W Z (t 0)) ⁻¹' E) ≠ 0)
    (n : ℕ) (h : ℝ) (hh : (t n : ℝ) - t 0 ≤ h) (hh0 : 0 < h) (a : ℝ) (ha : 0 < a) :
    ((W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E]).real
      {u | ∃ k : ℕ, k ≤ n ∧ a ≤ |actualParisiMagnetizationObservable W β (t k) u.1 -
        actualParisiMagnetizationObservable W β (t 0) u.1|} ≤
          2 * Real.exp (-(a ^ 2 / (2 * h))) := by
  classical
  let := W.isProbability
  let := Z.isProbability
  let F : Set Ω := {w | ∃ k : ℕ, k ≤ n ∧ a ≤ |actualParisiMagnetizationObservable W β (t k) w -
    actualParisiMagnetizationObservable W β (t 0) w|}
  have hF : MeasurableSet F := by
    unfold F
    simp only [ofPred_exists, ofPred_and]
    exact MeasurableSet.iUnion (fun k =>
      (MeasurableSet.const (k ≤ n)).inter (measurableSet_le measurable_const
        ((measurable_actualParisiMagnetizationObservable W β (t k)).sub
          (measurable_actualParisiMagnetizationObservable W β (t 0))).abs))
  have hb := conditional_integral_prod W.law Z.law (brownianFinitePath W (t 0))
    (brownianFinitePath Z (t 0)) (measurable_brownianFinitePath W (t 0))
    (measurable_brownianFinitePath Z (t 0)) (F.indicator (fun _ => (1 : ℝ)))
    ((integrable_const (1 : ℝ)).indicator hF) (2 * Real.exp (-(a ^ 2 / (2 * h))))
    (fun D hD hD0 => by
      rw [integral_indicator_const 1 hF]
      simpa only [smul_eq_mul, mul_one] using
        posterior_conditional_brownian_prefix_tail W β hβ t ht D hD hD0 n h hh hh0 a ha) E hE hE0
  have he : (fun u : Ω × A => F.indicator (fun _ => (1 : ℝ)) u.1) =
      (Prod.fst ⁻¹' F).indicator (fun _ => (1 : ℝ)) := rfl
  rw [he, integral_indicator_const 1 (hF.preimage measurable_fst)] at hb
  simp only [smul_eq_mul, mul_one] at hb
  change ((W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E]).real
    (Prod.fst ⁻¹' F) ≤ 2 * Real.exp (-(a ^ 2 / (2 * h))) at hb
  exact hb

end SKConstants.Completion.S76

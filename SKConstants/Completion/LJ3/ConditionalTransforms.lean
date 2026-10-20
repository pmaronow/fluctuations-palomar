module

public import SKConstants.Completion.LJ.LJ2
public import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable

namespace SKConstants.Completion.LJ3
open SKConstantsOAI.ZeroTemperatureSK LJ
variable {Ω : Type*} [MeasurableSpace Ω]

def gateFieldCoefficient (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (ScalarContinuousPath (t 0))) (H : OriginalFieldCoefficient t) :
    OriginalFieldCoefficient t :=
  fun k p => if scalarContinuousPathRestrict (t 0) (t k) (ht (Nat.zero_le k)) p ∈ E
    then H k p else 0

theorem measurable_gateFieldCoefficient (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (ScalarContinuousPath (t 0))) (hE : MeasurableSet E)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (k : ℕ) :
    Measurable (gateFieldCoefficient t ht E H k) :=
  Measurable.ite (hE.preimage (measurable_scalarContinuousPathRestrict _ _ _))
    (hH k) measurable_const

theorem gateFieldCoefficient_actual (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (H : OriginalFieldCoefficient t) :
    ∀ᵐ w ∂W.law, ∀ k, originalFieldCoefficient W b t (gateFieldCoefficient t ht E H) k w =
      if boundedDriftPastPath W b (t 0) w ∈ E then originalFieldCoefficient W b t H k w else 0 := by
  have hr := ae_all_iff.mpr (fun k => boundedDriftPastPath_restrict W b
    (t 0) (t k) (ht (Nat.zero_le k)))
  filter_upwards [hr] with w hw
  intro k
  simp only [originalFieldCoefficient, gateFieldCoefficient, hw k]

theorem predictableGaussianSum_gate {Ξ : Type*} (X H : ℕ → Ξ → ℝ)
    (E : Set Ξ) (n : ℕ) (w : Ξ) :
    predictableGaussianSum X (fun k w => if w ∈ E then H k w else 0) n w =
      if w ∈ E then predictableGaussianSum X H n w else 0 := by
  induction n with
  | zero => simp [predictableGaussianSum]
  | succ n ih =>
    simp only [predictableGaussianSum, ih]
    split_ifs <;> simp

theorem predictableGaussianVariation_gate {Ξ : Type*} (v : ℕ → ℝ≥0)
    (H : ℕ → Ξ → ℝ) (E : Set Ξ) (n : ℕ) (w : Ξ) :
    predictableGaussianVariation v (fun k w => if w ∈ E then H k w else 0) n w =
      if w ∈ E then predictableGaussianVariation v H n w else 0 := by
  induction n with
  | zero => simp [predictableGaussianVariation]
  | succ n ih =>
    simp only [predictableGaussianVariation, ih]
    split_ifs <;> simp

theorem originalFieldSum_gate (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (H : OriginalFieldCoefficient t) (n : ℕ) :
    originalFieldSum W b t (gateFieldCoefficient t ht E H) n =ᵐ[W.law]
      (fun w => if boundedDriftPastPath W b (t 0) w ∈ E then originalFieldSum W b t H n w else 0) := by
  filter_upwards [gateFieldCoefficient_actual W b t ht E H] with w hw
  change predictableGaussianSum _ _ _ _ = _
  rw [predictableGaussianSum_congr _ _
    (fun k w => if boundedDriftPastPath W b (t 0) w ∈ E then
      originalFieldCoefficient W b t H k w else 0) w hw n]
  exact predictableGaussianSum_gate _ _ ((boundedDriftPastPath W b (t 0)) ⁻¹' E) n w

theorem originalFieldVariation_gate (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (H : OriginalFieldCoefficient t) (n : ℕ) :
    originalFieldVariation W b t (gateFieldCoefficient t ht E H) n =ᵐ[W.law]
      (fun w => if boundedDriftPastPath W b (t 0) w ∈ E then originalFieldVariation W b t H n w else 0) := by
  filter_upwards [gateFieldCoefficient_actual W b t ht E H] with w hw
  change predictableGaussianVariation _ _ _ _ = _
  rw [predictableGaussianVariation_congr _ _
    (fun k w => if boundedDriftPastPath W b (t 0) w ∈ E then
      originalFieldCoefficient W b t H k w else 0) w hw n]
  exact predictableGaussianVariation_gate _ _ ((boundedDriftPastPath W b (t 0)) ⁻¹' E) n w

theorem posteriorFieldSum_gate (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (H : OriginalFieldCoefficient t) (n : ℕ) :
    posteriorFieldSum W β t (gateFieldCoefficient t ht E H) n =ᵐ[W.law]
      (fun w => if boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0) w ∈ E
        then posteriorFieldSum W β t H n w else 0) := by
  filter_upwards [gateFieldCoefficient_actual W (actualParisiFullScalarDrift β) t ht E H] with w hw
  change predictableGaussianSum _ _ _ _ = _
  rw [predictableGaussianSum_congr _ _
    (fun k w => if boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0) w ∈ E then
      originalFieldCoefficient W (actualParisiFullScalarDrift β) t H k w else 0) w hw n]
  exact predictableGaussianSum_gate _ _
    ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) n w

theorem conditional_mgf_of_gated_compensation
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (hE0 : μ E ≠ 0) (S V : Ω → ℝ) (hS : Measurable S) (θ v : ℝ)
    (hv : ∀ᵐ w ∂μ, V w ≤ v)
    (hcomp : Integrable (fun w => Real.exp (θ * (if w ∈ E then S w else 0) -
      θ ^ 2 * (if w ∈ E then V w else 0) / 2)) μ)
    (hcomp_le : (∫ w, Real.exp (θ * (if w ∈ E then S w else 0) -
      θ ^ 2 * (if w ∈ E then V w else 0) / 2) ∂μ) ≤ 1) :
    Integrable (fun w => Real.exp (θ * S w)) μ[|E] ∧
      mgf S μ[|E] θ ≤ Real.exp (θ ^ 2 * v / 2) := by
  let C := fun w => Real.exp (θ * (if w ∈ E then S w else 0) -
    θ ^ 2 * (if w ∈ E then V w else 0) / 2)
  have hsplit := integral_add_compl hE hcomp
  have hccompl : (∫ w in Eᶜ, C w ∂μ) = μ.real Eᶜ := by
    calc
      _ = ∫ _ in Eᶜ, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hE.compl] with w hw
        have hn : w ∉ E := hw
        simp [C, hn]
      _ = _ := by simp
  have hmass : μ.real E + μ.real Eᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl hE (μ := μ)
  have hcE : (∫ w in E, C w ∂μ) ≤ μ.real E := by
    change (∫ w in E, C w ∂μ) + (∫ w in Eᶜ, C w ∂μ) = _ at hsplit
    rw [hccompl] at hsplit
    linarith
  have hbound : ∀ᵐ w ∂μ.restrict E,
      Real.exp (θ * S w) ≤ Real.exp (θ ^ 2 * v / 2) * C w := by
    filter_upwards [ae_restrict_of_ae hv, ae_restrict_mem hE] with w hw he
    simp only [C, ite_eq_left he]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg θ)]
  have hi : Integrable (fun w => Real.exp (θ * S w)) (μ.restrict E) := by
    refine (hcomp.restrict.const_mul (Real.exp (θ ^ 2 * v / 2))).mono'
      ((hS.const_mul θ).exp.aestronglyMeasurable) ?_
    filter_upwards [hbound] with w hw
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hw
  have htest : (∫ w in E, Real.exp (θ * S w) ∂μ) ≤
      μ.real E * Real.exp (θ ^ 2 * v / 2) := by
    apply (integral_mono_ae hi (hcomp.restrict.const_mul _) hbound).trans
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hcE (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  constructor
  · exact hi.smul_measure (ENNReal.inv_ne_top.mpr hE0)
  · change (∫ w, Real.exp (θ * S w) ∂μ[|E]) ≤ _
    rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
    apply (mul_le_mul_of_nonneg_left htest (inv_nonneg.mpr (measureReal_nonneg))).trans_eq
    have hp : μ.real E ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hE0, measure_ne_top _ _⟩
    field_simp

theorem measurable_originalFieldSum (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (originalFieldSum W b t H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.add ((measurable_originalFieldCoefficient W b t H hH n).mul
      ((W.measurable (t (n + 1))).sub (W.measurable (t n))))

theorem originalFieldSum_conditional_mgf (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E) (hE0 : W.law ((boundedDriftPastPath W b (t 0)) ⁻¹' E) ≠ 0)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) (v : ℝ)
    (hv : ∀ᵐ w ∂W.law, originalFieldVariation W b t H n w ≤ v) :
    Integrable (fun w => Real.exp (θ * originalFieldSum W b t H n w))
      W.law[|(boundedDriftPastPath W b (t 0)) ⁻¹' E] ∧
      mgf (originalFieldSum W b t H n) W.law[|(boundedDriftPastPath W b (t 0)) ⁻¹' E] θ ≤
        Real.exp (θ ^ 2 * v / 2) := by
  let := W.isProbability
  let G := gateFieldCoefficient t ht E H
  have hG := measurable_gateFieldCoefficient t ht E hE H hH
  have hc := predictableGaussianExponential_integral W.law (brownianMeshIncrement W.B t)
    (originalFieldCoefficient W b t G) (brownianMeshVariance t)
    (brownianMeshIncrement_hasLaw W.brownian.toIsPreBrownianReal t ht)
    (fun k => (measurable_originalFieldCoefficient W b t G hG k).aemeasurable)
    (originalField_state_indep_increment W b t ht G hG) θ n
  have he : predictableGaussianExponential (brownianMeshIncrement W.B t)
      (originalFieldCoefficient W b t G) (brownianMeshVariance t) θ n =ᵐ[W.law]
      (fun w => Real.exp (θ * (if boundedDriftPastPath W b (t 0) w ∈ E
        then originalFieldSum W b t H n w else 0) - θ ^ 2 *
          (if boundedDriftPastPath W b (t 0) w ∈ E
            then originalFieldVariation W b t H n w else 0) / 2)) := by
    filter_upwards [originalFieldSum_gate W b t ht E H n,
      originalFieldVariation_gate W b t ht E H n] with w hs hv
    change Real.exp (θ * originalFieldSum W b t G n w -
      θ ^ 2 * originalFieldVariation W b t G n w / 2) = _
    rw [hs, hv]
  exact conditional_mgf_of_gated_compensation W.law _
    (hE.preimage (measurable_boundedDriftPastPath W b (t 0))) hE0 _ _
    (measurable_originalFieldSum W b t H hH n)
    θ v hv (hc.1.congr he) ((integral_congr_ae he).symm.trans_le hc.2.le)

theorem posteriorFieldSum_conditional_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k))
    (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k) (hHD : ∀ k p, |H k p| ≤ D k)
    (n : ℕ) (v : ℝ)
    (hv : ∀ᵐ w ∂W.law, originalFieldVariation W (actualParisiFullScalarDrift β) t H n w ≤ v)
    (θ : ℝ) :
    Integrable (fun w => Real.exp (θ * posteriorFieldSum W β t H n w))
      W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E] ∧
      mgf (posteriorFieldSum W β t H n)
        W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E] θ ≤
          Real.exp (θ ^ 2 * v / 2) := by
  let := W.isProbability
  let b := actualParisiFullScalarDrift β
  let G := gateFieldCoefficient t ht E H
  have hG := measurable_gateFieldCoefficient t ht E hE H hH
  have hGD (k : ℕ) (p : ScalarContinuousPath (t k)) : |G k p| ≤ D k := by
    dsimp only [G, gateFieldCoefficient]
    split_ifs
    · exact hHD k p
    · simpa using hD k
  let X := fun w => actualParisiPredictableExponential β t ht G θ n (boundedDriftPastPath W b (t n) w)
  have hbound := actualParisiPredictableExponential_bounds β t ht G D hD hGD θ n
  have hXm : Measurable X :=
    (measurable_actualParisiPredictableExponential β t ht G hG θ n).comp
      (measurable_boundedDriftPastPath W b (t n))
  have hXi : Integrable X W.law := Integrable.of_bound hXm.aestronglyMeasurable _
    (ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound.2 _).1]
      exact (hbound.2 _).2))
  have hXle : (∫ w, X w ∂W.law) ≤ 1 :=
    actualParisiPredictableExponential_integral_le_one W β hβ t ht G hG D hD hGD θ n
  have he : X =ᵐ[W.law]
      (fun w => Real.exp (θ * (if boundedDriftPastPath W b (t 0) w ∈ E
        then posteriorFieldSum W β t H n w else 0) - θ ^ 2 *
          (if boundedDriftPastPath W b (t 0) w ∈ E
            then originalFieldVariation W b t H n w else 0) / 2)) := by
    filter_upwards [posteriorFieldSum_exponential W β t ht G θ n,
      posteriorFieldSum_gate W β t ht E H n,
      originalFieldVariation_gate W b t ht E H n] with w hx hs hv
    exact hx.trans (by rw [hs, hv])
  exact conditional_mgf_of_gated_compensation W.law _
    (hE.preimage (measurable_boundedDriftPastPath W b (t 0))) hE0 _ _
    (measurable_posteriorFieldSum W β t H hH n) θ v hv (hXi.congr he)
    ((integral_congr_ae he).symm.trans_le hXle)

end SKConstants.Completion.LJ3

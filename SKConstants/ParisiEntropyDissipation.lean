module

public import SKConstants.ParisiEntropyPolynomialExpectation

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {T : ℝ}
variable (F : TimeField T) (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)
  (hm : ∀ v x, |F.f v x|<1)
  (ha : ∀ v x, |deriv (F.f v) x|≤1-(F.f v x)^2)

def entropyDissipationRate (F : TimeField T) (v x : ℝ) : ℝ :=
  (deriv (F.f v) x)^2/(1-(F.f v x)^2)

include hm in
lemma entropyPolynomial_expected_tendsto (v : ℝ) :
    Tendsto (fun N => (entropyPolynomialTimeField F N).expected b W v) atTop
      (𝓝 (∫ w, binarySpinEntropy (F.f v (b.solution W.driver (Real.toNNReal v) w)) ∂W.law)) := by
  let := W.isProbability
  unfold TimeField.expected
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => |Real.log 2|+1)
    (fun N => (integrable_family_comp (P:=W.law) (entropyPolynomialTimeField F N).smooth v
      (b.solution_measurable W (Real.toNNReal v))).aestronglyMeasurable) (integrable_const _) _ _
  · intro N
    filter_upwards [] with w
    simp only [Real.norm_eq_abs,entropyPolynomialTimeField_f]
    exact binaryEntropyPolynomial_abs_bound N (hm _ _).le
  · filter_upwards [] with w
    simp only [entropyPolynomialTimeField_f]
    exact binaryEntropyPolynomial_tendsto (hm _ _)

include hm ha in
lemma entropyPolynomialRate_expected_tendsto (v : ℝ) :
    Tendsto (fun N => ∫ w, entropyPolynomialRate F N v
      (b.solution W.driver (Real.toNNReal v) w) ∂W.law) atTop
      (𝓝 (∫ w, entropyDissipationRate F v
        (b.solution W.driver (Real.toNNReal v) w) ∂W.law)) := by
  let := W.isProbability
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
    (fun N => (integrable_family_comp (P:=W.law) (entropyPolynomialRate_family F N) v
      (b.solution_measurable W (Real.toNNReal v))).aestronglyMeasurable) (integrable_const _) _ _
  · intro N
    filter_upwards [] with w
    simp only [Real.norm_eq_abs,abs_of_nonneg (entropyPolynomialRate_nonneg F N v _)]
    exact entropyPolynomialRate_le_one F N v _ (hm _ _) (ha _ _)
  · filter_upwards [] with w
    simpa only [entropyDissipationRate] using
      (entropyPolynomialRate_tendsto F v (b.solution W.driver (Real.toNNReal v) w) (hm _ _))

include hm ha in
lemma entropyPolynomialRate_integral_tendsto_between (A V : ℝ) (hAV : A≤V) :
    Tendsto (fun N => ∫ v in A..V, ∫ w, entropyPolynomialRate F N v
      (b.solution W.driver (Real.toNNReal v) w) ∂W.law) atTop
      (𝓝 (∫ v in A..V, ∫ w, entropyDissipationRate F v
        (b.solution W.driver (Real.toNNReal v) w) ∂W.law)) := by
  let := W.isProbability
  simp only [intervalIntegral.integral_of_le hAV]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    (fun N => (bounded_family_expected_stronglyMeasurable W b (entropyPolynomialRate_family F N)).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self) (integrable_const _) _ _
  · intro N
    filter_upwards [] with v
    have H := norm_integral_le_of_norm_le_const (μ:=W.law) (C:=(1:ℝ))
      (f:=fun w => entropyPolynomialRate F N v (b.solution W.driver (Real.toNNReal v) w))
      (Eventually.of_forall (fun w => by
        simp only [Real.norm_eq_abs,abs_of_nonneg (entropyPolynomialRate_nonneg F N v _)]
        exact entropyPolynomialRate_le_one F N v _ (hm _ _) (ha _ _)))
    simpa only [probReal_univ,mul_one] using H
  · exact Eventually.of_forall (fun v => entropyPolynomialRate_expected_tendsto F b W hm ha v)

include hm ha in
theorem actualBrownian_entropy_dissipation_between (A V : ℝ) (hA0 : 0≤A)
    (hAV : A≤V) (hVT : V<T)
    (hgen : ∀ v∈Icc A V, ∀ x, F.generator b.f v x=0)
    (hbr : ∀ v : ℝ≥0, ∀ᵐ w ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r w) (Ioi (v:ℝ)) v) :
    (∫ w, binarySpinEntropy (F.f V (b.solution W.driver (Real.toNNReal V) w)) ∂W.law)=
      (∫ w, binarySpinEntropy (F.f A (b.solution W.driver (Real.toNNReal A) w)) ∂W.law)-
        (1/2:ℝ)*(∫ v in A..V, ∫ w, entropyDissipationRate F v
          (b.solution W.driver (Real.toNNReal v) w) ∂W.law) := by
  have H := entropyPolynomial_expected_tendsto F b W hm V
  simp only [entropyPolynomial_expected_integral_between F b W A V hA0 hAV hVT hgen hbr] at H
  have HR := (entropyPolynomial_expected_tendsto F b W hm A).sub
    ((entropyPolynomialRate_integral_tendsto_between F b W hm ha A V hAV).const_mul (1/2:ℝ))
  exact tendsto_nhds_unique H HR

include hm ha in
lemma entropyPolynomialRate_integral_tendsto (V : ℝ) (hV0 : 0≤V) :
    Tendsto (fun N => ∫ v in 0..V, ∫ w, entropyPolynomialRate F N v
      (b.solution W.driver (Real.toNNReal v) w) ∂W.law) atTop
      (𝓝 (∫ v in 0..V, ∫ w, entropyDissipationRate F v
        (b.solution W.driver (Real.toNNReal v) w) ∂W.law)) := by
  let := W.isProbability
  simp only [intervalIntegral.integral_of_le hV0]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
    (fun N => (bounded_family_expected_stronglyMeasurable W b (entropyPolynomialRate_family F N)).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self) (integrable_const _) _ _
  · intro N
    filter_upwards [] with v
    have H := norm_integral_le_of_norm_le_const (μ:=W.law) (C:=(1:ℝ))
      (f:=fun w => entropyPolynomialRate F N v (b.solution W.driver (Real.toNNReal v) w))
      (Eventually.of_forall (fun w => by
        simp only [Real.norm_eq_abs,abs_of_nonneg (entropyPolynomialRate_nonneg F N v _)]
        exact entropyPolynomialRate_le_one F N v _ (hm _ _) (ha _ _)))
    simpa only [probReal_univ,mul_one] using H
  · exact Eventually.of_forall (fun v => entropyPolynomialRate_expected_tendsto F b W hm ha v)

lemma entropyPolynomial_expected_zero (hF0 : F.f 0 0=0) (N : ℕ) :
    (entropyPolynomialTimeField F N).expected b W 0=Real.log 2 := by
  let := W.isProbability
  unfold TimeField.expected
  simp only [Real.toNNReal_zero,BoundedLipschitzDrift.solution_zero,entropyPolynomialTimeField_f,hF0,
    binaryEntropyPolynomial_zero,
    integral_const,probReal_univ,smul_eq_mul,one_mul]

include hm ha in
theorem actualBrownian_entropy_dissipation_from_initial (V : ℝ) (hV0 : 0≤V) (hVT : V<T)
    (hgen : ∀ v∈Icc 0 V, ∀ x, F.generator b.f v x=0)
    (hbr : ∀ v : ℝ≥0, ∀ᵐ w ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r w) (Ioi (v:ℝ)) v) :
    (∫ w, binarySpinEntropy (F.f V (b.solution W.driver (Real.toNNReal V) w)) ∂W.law)=
      binarySpinEntropy (F.f 0 0)-(1/2:ℝ)*(∫ v in 0..V, ∫ w, entropyDissipationRate F v
        (b.solution W.driver (Real.toNNReal v) w) ∂W.law) := by
  let := W.isProbability
  have H := entropyPolynomial_expected_tendsto F b W hm V
  simp only [entropyPolynomial_expected_integral F b W V hV0 hVT hgen hbr] at H
  have H0 := entropyPolynomial_expected_tendsto F b W hm 0
  simp only [Real.toNNReal_zero,BoundedLipschitzDrift.solution_zero,integral_const,
    probReal_univ,smul_eq_mul,one_mul] at H0
  have HR := H0.sub ((entropyPolynomialRate_integral_tendsto F b W hm ha V hV0).const_mul (1/2:ℝ))
  exact tendsto_nhds_unique H HR

include hm ha in
theorem actualBrownian_entropy_dissipation (V : ℝ) (hV0 : 0≤V) (hVT : V<T)
    (hF0 : F.f 0 0=0)
    (hgen : ∀ v∈Icc 0 V, ∀ x, F.generator b.f v x=0)
    (hbr : ∀ v : ℝ≥0, ∀ᵐ w ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r w) (Ioi (v:ℝ)) v) :
    (∫ w, binarySpinEntropy (F.f V (b.solution W.driver (Real.toNNReal V) w)) ∂W.law)=
      Real.log 2-(1/2:ℝ)*(∫ v in 0..V, ∫ w, entropyDissipationRate F v
        (b.solution W.driver (Real.toNNReal v) w) ∂W.law) := by
  have H := entropyPolynomial_expected_tendsto F b W hm V
  simp only [entropyPolynomial_expected_integral F b W V hV0 hVT hgen hbr,
    entropyPolynomial_expected_zero F b W hF0] at H
  have HR := (tendsto_const_nhds (x:=Real.log 2)).sub
    ((entropyPolynomialRate_integral_tendsto F b W hm ha V hV0).const_mul (1/2:ℝ))
  exact tendsto_nhds_unique H HR

end SKConstants.ParisiFullSupport

module

public import SKConstants.ParisiEntropyDissipation
public import SKConstants.ParisiFullPosteriorProfile

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

lemma boundedSmooth_tanh : BoundedSmooth Real.tanh := by
  simpa only [one_mul] using boundedSmooth_tanh_mul 1

lemma staticTanh_generator_zero (T : ℝ) (b : BoundedLipschitzDrift) (v x : ℝ)
    (hb : b.f v x=Real.tanh x) :
    (staticTimeField T Real.tanh boundedSmooth_tanh).generator b.f v x=0 := by
  have HD : deriv Real.tanh=scalarDefect := funext (fun y => (hasDerivAt_tanh_scalar y).deriv)
  unfold TimeField.generator staticTimeField
  rw [HD,deriv_scalarDefect,hb]
  ring

lemma staticTanh_entropyRate (T v x : ℝ) :
    entropyDissipationRate (staticTimeField T Real.tanh boundedSmooth_tanh) v x=scalarDefect x := by
  unfold entropyDissipationRate staticTimeField
  rw [(hasDerivAt_tanh_scalar x).deriv]
  change (scalarDefect x)^2/scalarDefect x=scalarDefect x
  field_simp

theorem actualParisi_post_entropy_dissipation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (V : ℝ) (hV : (parisiEquilibriumPhysicalEndpoint β:ℝ)≤V) :
    (∫ w, binarySpinEntropy (Real.tanh (actualParisiFullScalarProcess W β (Real.toNNReal V) w)) ∂W.law)=
      (∫ w, binarySpinEntropy (Real.tanh
        (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) w)) ∂W.law)-
        (1/2:ℝ)*(∫ v in (parisiEquilibriumPhysicalEndpoint β:ℝ)..V,
          actualParisiFullDefectMoment W β v) := by
  let F := staticTimeField (V+1) Real.tanh boundedSmooth_tanh
  let b := actualParisiFullScalarDrift β
  have hm (v x : ℝ) : |F.f v x|<1 := Real.abs_tanh_lt_one x
  have ha (v x : ℝ) : |deriv (F.f v) x|≤1-(F.f v x)^2 := by
    change |deriv Real.tanh x| ≤ scalarDefect x
    rw [(hasDerivAt_tanh_scalar x).deriv,abs_of_pos (scalarDefect_pos x)]
  have H := actualBrownian_entropy_dissipation_between F b W hm ha
    (parisiEquilibriumPhysicalEndpoint β) V (parisiEquilibriumPhysicalEndpoint β).coe_nonneg hV
    (by linarith : V<V+1) (fun v hv x => ?_)
    (fun v => (finiteTemperatureCDFDrift_path_right_continuous W β _ _ _).mono (fun w hw => hw v))
  · simp only [F,b,staticTanh_entropyRate] at H
    simpa only [staticTimeField,actualParisiFullScalarProcess,
      actualParisiFullDefectMoment,Real.toNNReal_coe] using H
  · apply staticTanh_generator_zero
    apply congrFun (actualParisiFullScalarDrift_eq_tanh_after_support β hβ v _)
    rw [←parisiEquilibriumPhysicalEndpoint_coe β hβ]
    exact hv.1

end SKConstants

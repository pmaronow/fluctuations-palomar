module

public import SKConstants.ParisiSmoothCutoffs

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

attribute [local irreducible] BoundedLipschitzDrift.solution

set_option backward.isDefEq.respectTransparency true in
lemma brownian_solution_joint_measurable (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) :
    Measurable (fun p : ℝ×Ω => b.solution W.driver (Real.toNNReal p.1) p.2) := by
  let ℱ := Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)
  have hB : IsProgressive ℱ W.driver := W.driver_progressive
  have hX : IsProgressive ℱ (b.solution W.driver) := b.solution_progressive ℱ hB
  have hx : Measurable (fun p : ℝ≥0×Ω => b.solution W.driver p.1 p.2) :=
    progressive_joint_measurable ℱ hX
  exact hx.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

lemma bounded_family_expected_stronglyMeasurable (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) :
    StronglyMeasurable (fun v => ∫ w, F v (b.solution W.driver (Real.toNNReal v) w) ∂W.law) := by
  let := W.isProbability
  have HM : Measurable (fun p : ℝ×Ω => F p.1 (b.solution W.driver (Real.toNNReal p.1) p.2)) :=
    hF.measurable.comp (measurable_fst.prodMk (brownian_solution_joint_measurable W b))
  exact HM.stronglyMeasurable.integral_prod_right

lemma bounded_family_expected_intervalIntegrable (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) (a c : ℝ) :
    IntervalIntegrable (fun v => ∫ w, F v (b.solution W.driver (Real.toNNReal v) w) ∂W.law) volume a c := by
  let := W.isProbability
  obtain ⟨C,hC⟩ := hF.bound
  apply (intervalIntegrable_const (c:=(C:ℝ))).mono_fun
    (bounded_family_expected_stronglyMeasurable W b hF).aestronglyMeasurable
  filter_upwards [] with v
  have H := norm_integral_le_of_norm_le_const (μ:=W.law) (C:=(C:ℝ))
    (f:=fun w => F v (b.solution W.driver (Real.toNNReal v) w))
    (Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs] using hC v _))
  simpa only [probReal_univ,mul_one,Real.norm_eq_abs,abs_of_nonneg C.coe_nonneg] using H

end SKConstants.ParisiFullSupport

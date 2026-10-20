module

public import SKConstants.Completion.LC0.PrimitivePathVersions
public import SKConstants.GaussianRotation

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.N16

variable {Ω : Type*} [MeasurableSpace Ω]

theorem stieltjesWeightedPath_const (c : ℝ) (T : ℝ≥0) (b : ScalarContinuousPath T) :
    scalarStieltjesWeightedPath (StieltjesFunction.const ℝ c) continuous_const T b = c • b := by
  ext t
  simp [scalarStieltjesWeightedPath, StieltjesFunction.measure_const,
    intervalIntegral, Measure.restrict_zero]

theorem brownianPath_rotation (W : BrownianSystem Ω) (T : ℝ≥0) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    ((scalarPrimitiveBrownianPathLaw W T).prod (scalarPrimitiveBrownianPathLaw W T)).map
      (fun p => c • p.1 + s • p.2) = scalarPrimitiveBrownianPathLaw W T := by
  have h := congrArg (fun μ : Measure (ScalarContinuousPath T × ScalarContinuousPath T) =>
      μ.map Prod.fst)
    (M1.weightedPair_preserves_brownian_law W W
      (StieltjesFunction.const ℝ (-c)) (StieltjesFunction.const ℝ s)
      continuous_const continuous_const T (fun _ _ => by simpa using hcs))
  rw [Measure.map_map measurable_fst (M1.measurable_WeightedPair _ _ _ _ T),
    Measure.map_fst_prod] at h
  simp only [measure_univ, one_smul] at h
  convert h using 1
  congr 1
  funext p
  simp [M1.WeightedPair, scalarTwoDriverWeightedPath, stieltjesWeightedPath_const]

theorem bridgePath_linear (T : ℝ≥0) (c s : ℝ)
    (b d : ScalarContinuousPath T) :
    scalarBrownianBridgePath T (c • b + s • d) =
      c • scalarBrownianBridgePath T b + s • scalarBrownianBridgePath T d := by
  ext t
  simp only [scalarBrownianBridgePath, ContinuousMap.coe_mk, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem bridgePath_rotation (W : BrownianSystem Ω) (T : ℝ≥0) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    ((scalarPrimitiveBridgePathLaw W T).prod (scalarPrimitiveBridgePathLaw W T)).map
      (fun p => c • p.1 + s • p.2) = scalarPrimitiveBridgePathLaw W T := by
  unfold scalarPrimitiveBridgePathLaw
  rw [Measure.map_prod_map _ _ (measurable_scalarBrownianBridgePath T)
      (measurable_scalarBrownianBridgePath T),
    Measure.map_map (by fun_prop)
      ((measurable_scalarBrownianBridgePath T).prodMap
        (measurable_scalarBrownianBridgePath T))]
  have h := congrArg (fun μ : Measure (ScalarContinuousPath T) =>
    μ.map (scalarBrownianBridgePath T)) (brownianPath_rotation W T c s hcs)
  rw [Measure.map_map (measurable_scalarBrownianBridgePath T) (by fun_prop)] at h
  convert h using 1
  congr 1
  funext p
  exact (bridgePath_linear T c s p.1 p.2).symm

end SKConstants.N16

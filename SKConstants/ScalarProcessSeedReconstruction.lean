module

public import SKConstants.ScalarProcessCausalReconstruction
import Mathlib.Tactic

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace SKConstants

@[expose] def scalarSeedInnovationPath (T : ℝ≥0)
    (p : ℝ × ScalarContinuousPath T) : ℝ × ScalarContinuousPath T :=
  (p.1, scalarInnovationPath T p.1 p.2)

theorem measurable_scalarSeedInnovationPath (T : ℝ≥0) :
    Measurable (scalarSeedInnovationPath T) := by
  apply Measurable.prodMk measurable_fst
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  have hi : Measurable (fun p : ℝ × ScalarContinuousPath T =>
      scalarInnovationPath T 0 p.2 t) := (ContinuousMap.measurable_eval t).comp
    ((measurable_scalarInnovationPath T 0).comp measurable_snd)
  convert hi.sub measurable_fst using 1
  funext p
  simp only [scalarInnovationPath, ContinuousMap.coe_mk, sub_zero, Pi.sub_apply]
  ring

theorem scalarSeedInnovationPath_injective (T : ℝ≥0) :
    Function.Injective (scalarSeedInnovationPath T) := by
  rintro ⟨z, f⟩ ⟨w, g⟩ h
  have hz := congrArg Prod.fst h
  change z = w at hz
  subst w
  have hf := congrArg Prod.snd h
  change scalarInnovationPath T z f = scalarInnovationPath T z g at hf
  exact Prod.ext rfl (scalarInnovationPath_injective T z hf)

theorem scalarSeedInnovationPath_measurableEmbedding (T : ℝ≥0) :
    MeasurableEmbedding (scalarSeedInnovationPath T) :=
  (measurable_scalarSeedInnovationPath T).measurableEmbedding
    (scalarSeedInnovationPath_injective T)

@[expose] def scalarSeedObservationPathFromInnovation (T : ℝ≥0) :
    ℝ × ScalarContinuousPath T → ScalarContinuousPath T :=
  fun p => (scalarSeedInnovationPath_measurableEmbedding T).invFun p |>.2

theorem measurable_scalarSeedObservationPathFromInnovation (T : ℝ≥0) :
    Measurable (scalarSeedObservationPathFromInnovation T) :=
  measurable_snd.comp (scalarSeedInnovationPath_measurableEmbedding T).measurable_invFun

theorem scalarSeedObservationPathFromInnovation_leftInverse (T : ℝ≥0)
    (z : ℝ) (f : ScalarContinuousPath T) :
    scalarSeedObservationPathFromInnovation T (z, scalarInnovationPath T z f) = f := by
  have h := (scalarSeedInnovationPath_measurableEmbedding T).leftInverse_invFun (z, f)
  exact congrArg Prod.snd h

theorem scalarSeedObservationPath_reconstruction (T : ℝ≥0) (z : ℝ)
    (Y : ℝ → ℝ) (hY : Continuous Y) (t : Icc (0 : ℝ) (T : ℝ)) :
    scalarSeedObservationPathFromInnovation T
      (z, scalarInnovationPath T z (scalarContinuousPathRestriction T Y hY)) t = Y t := by
  rw [scalarSeedObservationPathFromInnovation_leftInverse]
  rfl

@[expose] def scalarSeedEndpointFromInnovation (T : ℝ≥0) :
    ℝ × ScalarContinuousPath T → ℝ :=
  fun p => scalarSeedObservationPathFromInnovation T p ⟨T, ⟨T.coe_nonneg, le_rfl⟩⟩

theorem measurable_scalarSeedEndpointFromInnovation (T : ℝ≥0) :
    Measurable (scalarSeedEndpointFromInnovation T) :=
  (ContinuousMap.measurable_eval _).comp
    (measurable_scalarSeedObservationPathFromInnovation T)

theorem scalarSeedEndpointFromInnovation_reconstruction (T : ℝ≥0) (z : ℝ)
    (f : ScalarContinuousPath T) :
    scalarSeedEndpointFromInnovation T (z, scalarInnovationPath T z f) =
      f ⟨T, ⟨T.coe_nonneg, le_rfl⟩⟩ := by
  unfold scalarSeedEndpointFromInnovation
  rw [scalarSeedObservationPathFromInnovation_leftInverse]

end SKConstants

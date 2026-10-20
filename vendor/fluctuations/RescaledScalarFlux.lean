module

public import JointProfileResponse
public import NonnegativeThirdEnvelope

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarPlantedCurvatureCube_joint_smallClock_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 0)) :
    Tendsto (fun n => scalarPlantedJetPower hT (α n) 1 3 (q n)) atTop
      (𝓝 ((scalarTailSpatialJet hT β 2 0 0)^3)) := by
  simpa only [scalarPlantedJetPower_zero] using
    scalarPlantedJetPower_joint_parameter_window_tendsto hT hα hq 1 3

theorem scalarCurvatureFlux_rescaled_tendsto {T t U : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {x : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ᶠ n in atTop, 0 < x n) (ht : 0 < t)
    (hc : ∀ n q, ContinuousWithinAt (α n).val (Ici q) q)
    (hmass : Tendsto (fun n => (α n).val (x n*t)/x n) atTop (𝓝 U)) :
    Tendsto (fun n => T^2*scalarCurvatureFlux hT (α n) (x n*t)/x n) atTop
      (𝓝 (T^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
        2*T^2*(scalarTailSpatialJet hT β 2 0 0)^3*U)) := by
  have hq : Tendsto (fun n => x n*t) atTop (𝓝 0) := by
    simpa only [zero_mul] using hx.mul_const t
  have hqp : ∀ᶠ n in atTop, 0 < x n*t := hxp.mono (fun _ hn => mul_pos hn ht)
  have hthird := (scalarPlantedThirdSquare_joint_smallClock_tendsto hT hα hq hqp hc).mul_const t
  have hthird' : Tendsto (fun n => scalarPlantedJetPower hT (α n) 2 2 (x n*t)/x n) atTop
      (𝓝 (T*(scalarTailSpatialJet hT β 4 0 0)^2*t)) := by
    apply hthird.congr'
    filter_upwards [hxp] with n hn
    field_simp
  have hcube := scalarPlantedCurvatureCube_joint_smallClock_tendsto hT hα hq
  have hflux := (hthird'.sub ((hmass.const_mul 2).mul hcube)).const_mul (T^2)
  have he : T^2*(T*(scalarTailSpatialJet hT β 4 0 0)^2*t-
      2*U*(scalarTailSpatialJet hT β 2 0 0)^3)=
      T^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
        2*T^2*(scalarTailSpatialJet hT β 2 0 0)^3*U := by ring
  rw [he] at hflux
  apply hflux.congr'
  filter_upwards [hxp] with n hn
  dsimp only [scalarCurvatureFlux]
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization

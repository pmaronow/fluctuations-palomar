module

public import ComparisonCriticalPositiveWallGradientCore
public import ComparisonActualHighWallScalarLimitData
public import ComparisonHighStrengthUniformClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem actual_positive_wall_scaled_radius_scalar_integrable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (alpha : boundedMassProfiles) (a b : ℝ) :
    let S := fun t=>M.radiusS (M.xs*t)
    let K := fun t=>actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val (M.xs*t))
    let Gamma := scalarCovarianceResponse hT alpha
    IntegrableOn (fun t=>(S t-Gamma (K t))/M.xs^3) (Icc a b) := by
  intro S K Gamma
  have hu t : M.alpha.val.val (M.xs*t)∈Icc (0:ℝ) 1 :=
    M.alpha.val.property.1 _
  have hmono : Monotone (fun t=>M.alpha.val.val (M.xs*t)) :=
    fun _ _ h=>M.alpha.val.property.2
      (mul_le_mul_of_nonneg_left h M.hxs.le)
  have hS : Monotone S := fun s t h=>M.full_radius_moments.1
    (mul_le_mul_of_nonneg_left h M.hxs.le)
  have hS0 t : 0 ≤ S t := (M.full_radius_moments.2.2 _).1.1
  have hK : Monotone K := by
    intro s t h
    exact add_le_add (M.data.hf_monotone M.alpha (hu s) (hu t) (hmono h))
      (mul_le_mul (M.data.bf_monotone M.alpha (hu s) (hu t) (hmono h))
        (hS h) (hS0 s) (NNReal.coe_nonneg _))
  have hSi : IntegrableOn S (Icc a b) :=
    (hS.monotoneOn (Icc a b)).integrableOn_isCompact (μ:=volume) isCompact_Icc
  have hKi : IntegrableOn K (Icc a b) :=
    (hK.monotoneOn (Icc a b)).integrableOn_isCompact (μ:=volume) isCompact_Icc
  have hGi : IntegrableOn (fun t=>Gamma (K t)) (Icc a b) := by
    apply Integrable.of_bound
      ((scalarPlantedEnergy_continuous hT alpha).comp_aestronglyMeasurable
        (hKi.div_const T).aestronglyMeasurable) 1
    filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_of_nonneg (scalarPlantedEnergy_bounds hT alpha _).1]
    exact (scalarPlantedEnergy_bounds hT alpha _).2
  exact (hSi.sub hGi).div_const _

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

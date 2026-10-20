module

public import ComparisonActualHighWallRadiusSequence
public import ComparisonActualHighWallScalarLimitData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal
namespace ActualHighWallOverlapMinimum
set_option maxHeartbeats 8000000

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

def wallRadiusPointDefect
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) : ℝ := M.radiusB r-(M.radiusS r)^2

theorem wall_radius_point_defect_nonneg
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc M.data.rmin 1) : 0≤M.wallRadiusPointDefect r := by
  exact sub_nonneg.mpr (M.radius_moments.2.2 r hr).2.1

theorem wall_radius_point_defect_integrableOn
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntegrableOn M.wallRadiusPointDefect (Icc M.data.rmin 1) := by
  have H:=M.radius_moments
  have hS2 : MonotoneOn (fun r=>(M.radiusS r)^2) (Icc M.data.rmin 1) := by
    intro r hr s hs hrs
    exact pow_le_pow_left₀ ((H.2.2 r hr).1.1) (H.1 hr hs hrs) 2
  exact (H.2.1.integrableOn_isCompact (μ:=volume) isCompact_Icc).sub
    (hS2.integrableOn_isCompact (μ:=volume) isCompact_Icc)

theorem original_scalar_radius_gap_integrableOn
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (alpha : boundedMassProfiles) :
    IntegrableOn (fun r=>M.radiusS r-
      scalarCovarianceResponse hT alpha
        (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)))
      (Icc M.data.rmin 1) := by
  have H:=M.radius_moments
  have hS:=H.1.integrableOn_isCompact (μ:=volume) isCompact_Icc
  have hK : MonotoneOn
      (fun r=>actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r))
      (Icc M.data.rmin 1) := by
    intro r hr s hs hrs
    have har: M.alpha.val.val r∈Icc (0:ℝ) 1:=M.alpha.val.property.1 r
    have has: M.alpha.val.val s∈Icc (0:ℝ) 1:=M.alpha.val.property.1 s
    have ham:=M.alpha.val.property.2 hrs
    exact add_le_add (M.data.hf_monotone M.alpha har has ham)
      (mul_le_mul (M.data.bf_monotone M.alpha har has ham) (H.1 hr hs hrs)
        ((H.2.2 r hr).1.1) (NNReal.coe_nonneg _))
  have hKi:IntegrableOn
      (fun r=>actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)/T)
      (Icc M.data.rmin 1):=
    (hK.integrableOn_isCompact (μ:=volume) isCompact_Icc).div_const T
  have hG:IntegrableOn (fun r=>scalarPlantedEnergy hT alpha
      (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)/T))
      (Icc M.data.rmin 1):=by
    apply Integrable.of_bound
      ((scalarPlantedEnergy_continuous hT alpha).comp_aestronglyMeasurable
        hKi.aestronglyMeasurable) 1
    filter_upwards [] with r
    rw [Real.norm_eq_abs,abs_of_nonneg (scalarPlantedEnergy_bounds hT alpha _).1]
    exact (scalarPlantedEnergy_bounds hT alpha _).2
  exact hS.sub hG

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

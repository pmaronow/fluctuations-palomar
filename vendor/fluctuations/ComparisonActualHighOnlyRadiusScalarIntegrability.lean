module

public import ComparisonActualHighOnlyRadiusSingleCutIntegral
public import ComparisonActualHighOnlyClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal
namespace ActualHighOnlyOverlapMinimum
set_option maxHeartbeats 8000000

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem original_scalar_radius_gap_integrableOn
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (alpha : boundedMassProfiles) :
    IntegrableOn (fun r=>orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r)-
      scalarCovarianceResponse hT alpha
        (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r))) (Icc (0:ℝ) 1) := by
  have H:=M.radius_moments
  have hS:=H.1.integrableOn_isCompact (μ:=volume) isCompact_Icc
  have hK : MonotoneOn (fun r=>actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r))
      (Icc (0:ℝ) 1) := by
    intro r hr s hs hrs
    have har: M.alpha.val.val r∈Icc (0:ℝ) 1:=M.alpha.val.property.1 r
    have has: M.alpha.val.val s∈Icc (0:ℝ) 1:=M.alpha.val.property.1 s
    have ham:=M.alpha.val.property.2 hrs
    exact add_le_add (M.inherited_hf_monotone har has ham)
      (mul_le_mul (M.inherited_bf_monotone har has ham) (H.1 hr hs hrs)
        ((H.2.2 r hr).1.1) (NNReal.coe_nonneg _))
  have hKi:IntegrableOn (fun r=>actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)/T)
      (Icc (0:ℝ) 1):=
    (hK.integrableOn_isCompact (μ:=volume) isCompact_Icc).div_const T
  have hG:IntegrableOn (fun r=>scalarPlantedEnergy hT alpha
      (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)/T)) (Icc (0:ℝ) 1):=by
    apply Integrable.of_bound
      ((scalarPlantedEnergy_continuous hT alpha).comp_aestronglyMeasurable
        hKi.aestronglyMeasurable) 1
    filter_upwards [] with r
    rw [Real.norm_eq_abs,abs_of_nonneg (scalarPlantedEnergy_bounds hT alpha _).1]
    exact (scalarPlantedEnergy_bounds hT alpha _).2
  exact hS.sub hG

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import SKProof.Port.ComparisonActualOriginalQRadiusSingleCutIntegral
public import SKProof.Port.ComparisonActualOriginalQClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal
namespace ActualThetaZeroOverlapMinimum
set_option maxHeartbeats 8000000

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

private theorem radiusS_unit_domain
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn M.radiusS (Icc (0:ℝ) 1) ∧
      ∀ r ∈ Icc (0:ℝ) 1, 0 ≤ M.radiusS r := by
  have hnonneg (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      0 ≤ orderedPathS (n+1) M.sweepBf M.sweepHf u := by
    by_cases hz : u = 0
    · subst u
      simp only [orderedPathS, orderedPathPair_zero]
      norm_num
    · exact (orderedPath_SK_bounds (n+1) M.data.hn M.sweepBf M.sweepHf
        M.sweep_bf_monotone M.sweep_hf_monotone
        ⟨lt_of_le_of_ne hu.1 (Ne.symm hz), hu.2⟩).1
  refine ⟨?_, fun r _ => hnonneg _ (M.alpha.val.property.1 r)⟩
  intro r _ t _ hrt
  have hr := M.alpha.val.property.1 r
  have ht := M.alpha.val.property.1 t
  have hmono := M.alpha.val.property.2 hrt
  by_cases hz : M.alpha.val.val r = 0
  · change orderedPathS (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r) ≤
      orderedPathS (n+1) M.sweepBf M.sweepHf (M.alpha.val.val t)
    rw [hz]
    simpa only [orderedPathS, orderedPathPair_zero] using
      hnonneg _ ht
  · have hp : 0 < M.alpha.val.val r := lt_of_le_of_ne hr.1 (Ne.symm hz)
    exact (orderedPath_SK_monotone (n+1) M.data.hn M.sweepBf M.sweepHf
      M.sweep_bf_monotone M.sweep_hf_monotone).1
      ⟨hp, hr.2⟩ ⟨hp.trans_le hmono, ht.2⟩ hmono

theorem original_scalar_radius_gap_integrableOn
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (alpha : boundedMassProfiles) :
    IntegrableOn (fun r=>orderedPathS (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)-
      scalarCovarianceResponse hT alpha
        (actualMixedClock (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r))) (Icc (0:ℝ) 1) := by
  have H:=radiusS_unit_domain M
  have hS:=H.1.integrableOn_isCompact (μ:=volume) isCompact_Icc
  have hK : MonotoneOn (fun r=>actualMixedClock (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r))
      (Icc (0:ℝ) 1) := by
    intro r hr s hs hrs
    have har: M.alpha.val.val r∈Icc (0:ℝ) 1:=M.alpha.val.property.1 r
    have has: M.alpha.val.val s∈Icc (0:ℝ) 1:=M.alpha.val.property.1 s
    have ham:=M.alpha.val.property.2 hrs
    exact add_le_add (M.inherited_hf_monotone har has ham)
      (mul_le_mul (M.inherited_bf_monotone har has ham) (H.1 hr hs hrs)
        (H.2 r hr) (NNReal.coe_nonneg _))
  have hKi:IntegrableOn (fun r=>actualMixedClock (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)/T)
      (Icc (0:ℝ) 1):=
    (hK.integrableOn_isCompact (μ:=volume) isCompact_Icc).div_const T
  have hG:IntegrableOn (fun r=>scalarPlantedEnergy hT alpha
      (actualMixedClock (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)/T)) (Icc (0:ℝ) 1):=by
    apply Integrable.of_bound
      ((scalarPlantedEnergy_continuous hT alpha).comp_aestronglyMeasurable
        hKi.aestronglyMeasurable) 1
    filter_upwards [] with r
    rw [Real.norm_eq_abs,abs_of_nonneg (scalarPlantedEnergy_bounds hT alpha _).1]
    exact (scalarPlantedEnergy_bounds hT alpha _).2
  exact hS.sub hG

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonLinearCubicCoordinateClosure
public import SKProof.Port.ComparisonActualOriginalQRadiusScalarIntegrability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal
namespace ActualThetaZeroOverlapMinimum
set_option maxHeartbeats 8000000

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem cavity_radius_point_defect_unit_integrable
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntegrableOn M.cavityRadiusPointDefect (Icc (0:ℝ) 1) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact M.cavityRadiusPointDefect_integrableOn le_rfl le_rfl

theorem actual_original_radius_scalar_modulus_integral_le
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (alpha : boundedMassProfiles)
    (F : Set ℝ) [IsFiniteMeasure (volume.restrict F)]
    (hFm : MeasurableSet F) (hF : F ⊆ Icc (0:ℝ) 1)
    {C L eta : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (heta : 0 ≤ eta)
    (hmass : (volume.restrict F).real univ ≤ L*M.xs)
    (hpoint : ∀r∈F,
      |orderedPathS (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)-
        scalarCovarianceResponse hT alpha
          (actualMixedClock (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r))| ≤
      C*M.xs^2*(Real.sqrt (M.cavityRadiusPointDefect r)+1/M.data.N)+eta*M.xs^3) :
    (∫r in F, |orderedPathS (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)-
      scalarCovarianceResponse hT alpha
        (actualMixedClock (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r))|)/M.xs^4 ≤
      C*Real.sqrt (L*((∫r in F,M.cavityRadiusPointDefect r)/M.xs^3))+
        C*L/(M.data.N*M.xs)+L*eta := by
  have hi := M.cavity_radius_point_defect_unit_integrable.mono_set hF
  have hnonneg : ∀ᵐr∂volume.restrict F,0 ≤ M.cavityRadiusPointDefect r := by
    filter_upwards [ae_restrict_mem hFm] with r hr
    exact M.cavityRadiusPointDefect_nonneg (hF hr)
  obtain ⟨hroot,hroot2⟩:=coordinate_sqrt_integrable (volume.restrict F)
    M.cavityRadiusPointDefect hi hnonneg
  have hscalar:=(M.original_scalar_radius_gap_integrableOn hT alpha).mono_set hF
  have H:=linear_cubic_modulus_normalized_integral_le (volume.restrict F)
    (fun r=>Real.sqrt (M.cavityRadiusPointDefect r))
    (fun r=>orderedPathS (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)-
      scalarCovarianceResponse hT alpha
        (actualMixedClock (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)))
    hroot hscalar M.hxs hC hL (one_div_nonneg.mpr M.data.hN.le) heta hmass (by
      filter_upwards [ae_restrict_mem hFm] with r hr
      simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using hpoint r hr)
  have HC:=comparison_original_mass_normalized_L1_le_sqrt (volume.restrict F)
    (fun r=>Real.sqrt (M.cavityRadiusPointDefect r)) hroot hroot2 M.hxs hL hmass
  have heq : (∫r in F,(Real.sqrt (M.cavityRadiusPointDefect r))^2)=
      ∫r in F,M.cavityRadiusPointDefect r := by
    exact integral_congr_ae (hnonneg.mono fun r hr=>Real.sq_sqrt hr)
  rw [heq] at HC
  have Hmul:=mul_le_mul_of_nonneg_left HC hC
  have hid : C*L*((1/M.data.N)/M.xs)=C*L/(M.data.N*M.xs) := by ring
  rw [hid] at H
  linarith only [H,Hmul]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

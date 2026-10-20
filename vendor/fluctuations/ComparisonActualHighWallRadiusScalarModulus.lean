module

public import ComparisonLinearCubicCoordinateClosure
public import ComparisonActualHighWallRadiusScalarIntegrability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal
namespace ActualHighWallOverlapMinimum
set_option maxHeartbeats 8000000

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem actual_original_radius_scalar_modulus_integral_le
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (alpha : boundedMassProfiles)
    (F : Set ℝ) [IsFiniteMeasure (volume.restrict F)]
    (hFm : MeasurableSet F) (hF : F ⊆ Icc M.data.rmin 1)
    {C L eta : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (heta : 0 ≤ eta)
    (hmass : (volume.restrict F).real univ ≤ L*M.xs)
    (hpoint : ∀r∈F,
      |M.radiusS r-
        scalarCovarianceResponse hT alpha
          (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r))| ≤
      C*M.xs^2*(Real.sqrt (M.wallRadiusPointDefect r)+1/M.data.N)+eta*M.xs^3) :
    (∫r in F, |M.radiusS r-
      scalarCovarianceResponse hT alpha
        (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r))|)/M.xs^4 ≤
      C*Real.sqrt (L*((∫r in F,M.wallRadiusPointDefect r)/M.xs^3))+
        C*L/(M.data.N*M.xs)+L*eta := by
  have hi := M.wall_radius_point_defect_integrableOn.mono_set hF
  have hnonneg : ∀ᵐr∂volume.restrict F,0 ≤ M.wallRadiusPointDefect r := by
    filter_upwards [ae_restrict_mem hFm] with r hr
    exact M.wall_radius_point_defect_nonneg (hF hr)
  obtain ⟨hroot,hroot2⟩:=coordinate_sqrt_integrable (volume.restrict F)
    M.wallRadiusPointDefect hi hnonneg
  have hscalar:=(M.original_scalar_radius_gap_integrableOn hT alpha).mono_set hF
  have H:=linear_cubic_modulus_normalized_integral_le (volume.restrict F)
    (fun r=>Real.sqrt (M.wallRadiusPointDefect r))
    (fun r=>M.radiusS r-
      scalarCovarianceResponse hT alpha
        (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r)))
    hroot hscalar M.hxs hC hL (one_div_nonneg.mpr M.data.hN.le) heta hmass (by
      filter_upwards [ae_restrict_mem hFm] with r hr
      simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using hpoint r hr)
  have HC:=comparison_original_mass_normalized_L1_le_sqrt (volume.restrict F)
    (fun r=>Real.sqrt (M.wallRadiusPointDefect r)) hroot hroot2 M.hxs hL hmass
  have heq : (∫r in F,(Real.sqrt (M.wallRadiusPointDefect r))^2)=
      ∫r in F,M.wallRadiusPointDefect r := by
    exact integral_congr_ae (hnonneg.mono fun r hr=>Real.sq_sqrt hr)
  rw [heq] at HC
  have Hmul:=mul_le_mul_of_nonneg_left HC hC
  have hid : C*L*((1/M.data.N)/M.xs)=C*L/(M.data.N*M.xs) := by ring
  rw [hid] at H
  linarith only [H,Hmul]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

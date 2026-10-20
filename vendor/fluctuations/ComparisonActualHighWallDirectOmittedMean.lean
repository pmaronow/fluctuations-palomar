module

public import ComparisonActualGeneralLowMeanDefectCalibration
public import ComparisonActualHighWallScalarFeedbackAlong
public import ComparisonActualGeneralTargetMeanBounds
public import WallMeanSuppressionAlgebra

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

 theorem actual_high_wall_omitted_mean_suppression_of_finite_original_prices
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Cd Cgap Cr : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i star U : ℕ)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hhigh : M.data.s ≤ partitionPoint 0 as star)
    (hlow : partitionPoint 0 as i < M.data.s) (hCd : 0 ≤ Cd)
    (Hsmall : (Cd+1)*M.data.d^2 ≤ 1/2)
    (Hroom : 4*Bclock*(Cd+1)*M.data.d^2 ≤ M.data.epsilon)
    (Hdefect :
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| ≤ Cd*M.data.d^2)
    (Hmean : |nativePhysicalResourceCenter n M.bf M.hf as i-
      nativeOriginalScalarPairMean as (nativeContinuumMixedClock n M.bf M.hf as) i| ≤ Cgap*M.data.d^3)
    (Hscalar :
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeOriginalScalarPairMean as K i-chi^2*K i| ≤ Cr*M.data.d^3) :
    orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as i) ≤
      wallMeanScale (4*Bclock*(Cgap+Cr+1/16)) M.data.d M.data.epsilon := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let bstar:=(M.bf (partitionPoint 0 as star):ℝ)
  let blow:=(M.bf (partitionPoint 0 as i):ℝ)
  let S:=nativePhysicalResourceCenter n M.bf M.hf as i
  let h:=(M.hf (partitionPoint 0 as i):ℝ)
  have hu:=partitionPoint_mem as ho i
  have hstar:=partitionPoint_mem as ho star
  have hHstar : partitionPoint 0 as star∈Icc M.data.s 1:=⟨hhigh,hstar.2⟩
  have hB : 0 < Bclock:=M.data.hTpos.trans_le M.hT
  have hchi : chi∈Icc (0:ℝ) 1:=actual_general_continuum_chi_mem_unit_on_any_grid
    (n:=n) M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho U (by omega) hU
  have hbstar : 0 ≤ M.data.T-bstar:=by
    have HT:=M.data.total_clock_le M.alpha _ hstar
    dsimp only [bstar]
    linarith [NNReal.coe_nonneg (M.hf (partitionPoint 0 as star))]
  have Hgap : M.data.T-bstar ≤ M.data.d^2:=by
    dsimp only [bstar]
    rw [(M.data.clock_coe M.alpha hstar).1]
    dsimp only [ActualHighWallData.b]
    rw [wallChangedMatrix_on M.data.hr M.data.hs1 M.data.hc M.data.hk M.data.hkc
      M.data.hm M.data.hM M.data.g M.data.hg.continuous M.data.T M.data.epsilon
      M.data.theta M.alpha hHstar]
    have Hg:=laplaceComparisonStrength_le M.data.d (sq_nonneg M.data.d)
      (constrainedQuantile M.data.hr M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha ⟨_,hHstar⟩)
    change M.data.g _ ≤ M.data.d^2 at Hg
    linarith only [Hg]
  have Hlow : blow ≤ M.data.T-M.data.epsilon:=by
    dsimp only [blow]
    rw [(M.data.clock_coe M.alpha hu).1]
    dsimp only [ActualHighWallData.b]
    rw [wallChangedMatrix_below M.data.hr M.data.hs1 M.data.hc M.data.hk M.data.hkc
      M.data.hm M.data.hM M.data.g M.data.hg.continuous M.data.T M.data.epsilon
      M.data.theta M.alpha hlow]
    have Htheta:=mul_nonneg M.data.htheta.1 (wallLowStrength_bounds M.data.hepsilon).1
    linarith only [Htheta]
  have Hfactor:=scalar_low_factor_lower_of_high_defect hB M.hT M.data.hepsilon.1 hCd hchi
    hbstar Hgap Hlow Hdefect Hsmall Hroom
  have HS : S=orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as i):=by
    unfold S nativePhysicalResourceCenter
    exact (native_ordered_source_center_eq_completed n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hu).symm
  have HS0 : 0 ≤ S:=by
    rw [HS]
    exact (physicalOrderedPathS_mem_unit n M.bf M.hf (M.data.bf_monotone M.alpha)
      (M.data.hf_monotone M.alpha) hu).1
  have HK : K i=h+blow*S:=native_continuum_mixed_clock_eq_original_center n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho i
  have Hfield : h ≤ (1/16)*M.data.d^3:=by
    have HF:=M.data.low_field_cubic M.alpha hu hlow
    dsimp only [h]
    nlinarith only [HF]
  have H:=original_low_mean_suppression_of_same_scalar_errors hB M.data.hepsilon.1 HS0
    (NNReal.coe_nonneg _) hchi HK Hfactor Hfield
    (nativeOriginalScalarPairMean as K i) Hmean Hscalar
  rw [HS] at H
  exact H

end OAI.SKFluctuations.Cavity

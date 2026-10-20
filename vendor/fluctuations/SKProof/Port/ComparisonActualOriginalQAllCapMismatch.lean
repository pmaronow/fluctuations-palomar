module

public import SKProof.Port.ComparisonActualOriginalQSquaredMismatch
public import ComparisonActualHighWallThetaZeroInitialCapPoint
public import ComparisonActualHighWallThetaZeroBroadBudgets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem radiusThermal_nonneg
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (_hr : r∈Icc (0:ℝ) 1) : 0 ≤ M.radiusThermal r := by
  have hu : M.alpha.val.val r ∈ Icc (0:ℝ) 1 := M.alpha.val.property.1 r
  by_cases hu0 : M.alpha.val.val r = 0
  · simp only [radiusThermal,radiusB,radiusS,hu0,orderedPathB,orderedPathS,orderedPathPair_zero]
    norm_num
  · exact sub_nonneg.mpr (orderedPath_SK_bounds (n+1) M.data.hn M.sweepBf M.sweepHf
      M.sweep_bf_monotone M.sweep_hf_monotone
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩).2.2.1

theorem controlFactor_pos
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (r : ℝ) :
    0 < M.controlFactor r:=inverseControlFactor_pos _ _ _

theorem Potential.component_endpoint_alternatives
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {r : ℝ} (hr : r∈p.negativeSet) :
    (p.H (sInf (ordConnectedComponent p.negativeSet r))=0 ∨
      sInf (ordConnectedComponent p.negativeSet r)=M.data.rmin) ∧
    (p.H (sSup (ordConnectedComponent p.negativeSet r))=0 ∨
      sSup (ordConnectedComponent p.negativeSet r)=1) := by
  obtain ⟨c,hcl,hcr,_,hcLeft,hcRight⟩:=p.negative_component_endpoints hr
  simpa only [hcl,hcr] using And.intro hcLeft hcRight

private theorem rmin_le_cap_travel
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    M.data.rmin ≤ M.cavityCapTravel := by
  have hU : 0 < M.data.U := M.data.hU
  have hL : 0 < M.data.L := M.data.hL
  have hpow : 0 < M.data.N^delta := Real.rpow_pos_of_pos M.data.hN _
  have hs0 : 0 ≤ M.data.s := M.data.hs.1.le
  have hrecip := (comparisonCap_first_term (δ:=delta) M.data.hN M.data.hU
    M.data.hL M.data.hE M.data.hd.le M.data.hs.1.le).2
  change 1/M.data.M M.data.s ≤
    (M.data.L/M.data.N^delta)*(1/(M.data.s+M.data.U)) at hrecip
  have hratio : M.data.U/(M.data.s+M.data.U) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith [M.data.hs.1])
  have hhalf : M.data.rmin ≤ (M.data.L/M.data.N^delta)/2 := by
    calc
      M.data.rmin = (M.data.U/2)*(1/M.data.M M.data.s) := by
        change M.data.U/(2*M.data.M M.data.s) = _
        ring
      _ ≤ (M.data.U/2)*((M.data.L/M.data.N^delta)*(1/(M.data.s+M.data.U))) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = ((M.data.L/M.data.N^delta)/2)*(M.data.U/(M.data.s+M.data.U)) := by ring
      _ ≤ ((M.data.L/M.data.N^delta)/2)*1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (M.data.L/M.data.N^delta)/2 := mul_one _
  have hU1 : M.data.U ≤ 1 := M.data.hsmall.trans M.data.hd1
  have hlog : (1:ℝ)/2 ≤ Real.log ((1+M.data.U)/M.data.U) := by
    have htwo : (2:ℝ) ≤ (1+M.data.U)/M.data.U :=
      (le_div_iff₀ M.data.hU).mpr (by linarith only [hU1])
    have H := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at H
    exact H.trans (Real.log_le_log (by norm_num) htwo)
  exact hhalf.trans (by
    change (M.data.L/M.data.N^delta)/2 ≤
      (M.data.L/M.data.N^delta)*Real.log ((1+M.data.U)/M.data.U)
    simpa only [div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ M.data.L/M.data.N^delta))

theorem Potential.all_negative_point_squared_mismatch
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {r : ℝ} (hr : r∈Ioo M.data.rmin 1) (hneg : p.H r<0) :
    (M.radiusS r-r)^2≤16*M.cavityCapTravel^2+2*M.radiusThermal r := by
  have hrneg : r∈p.negativeSet := ⟨hr,hneg⟩
  obtain ⟨hl,hlr,hrz,hz,heq,_,_⟩:=wholeCap_component_endpoints p.negativeSet_open
    p.negativeSet_subset hrneg
  have hinterval : ∀t∈Ioo (sInf (ordConnectedComponent p.negativeSet r))
      (sSup (ordConnectedComponent p.negativeSet r)),p.H t<0 := by
    intro t ht
    exact (ordConnectedComponent_subset (heq.symm ▸ ht)).2
  have hwidth:=(p.cap_interval_travel M hl (hlr.trans hrz).le hz hinterval).2.1
  have hend:=p.component_endpoint_alternatives hrneg
  rcases hend.1 with hleft|hwall
  · have H:=p.cap_point_squared_mismatch hl hz ⟨hlr,hrz⟩ hleft hend.2 hneg
    have hs:=pow_le_pow_left₀ (sub_nonneg.mpr (hlr.trans hrz).le) hwidth 2
    dsimp only [radiusThermal]
    nlinarith only [H,hs]
  · have hmom:=M.radius_moments
    have hS0 : 0≤M.radiusS r := (hmom.2.2 r (Ioo_subset_Icc_self hr)).1.1
    have hSz : M.radiusS r ≤ sSup (ordConnectedComponent p.negativeSet r) := by
      rcases hend.2 with hc|ht
      · exact p.cap_point_mean_le_right hl hz ⟨hlr,hrz⟩ hc hneg
      · rw [ht]
        exact (hmom.2.2 r (Ioo_subset_Icc_self hr)).1.2
    rw [hwall] at hwidth
    have ht0 := M.cavityCapTravel_nonneg
    have hwallTravel := rmin_le_cap_travel M
    have hSbound : M.radiusS r ≤ M.data.rmin+M.cavityCapTravel := by
      linarith only [hSz,hwidth]
    have hrbound : r ≤ M.data.rmin+M.cavityCapTravel := by
      linarith only [hrz,hwidth]
    have hr0 : 0 ≤ r := M.data.rmin_nonneg.trans hr.1.le
    have habs : |M.radiusS r-r| ≤ M.data.rmin+M.cavityCapTravel :=
      abs_le.mpr ⟨by linarith only [hS0,hrbound],by linarith only [hSbound,hr0]⟩
    have Hsq := pow_le_pow_left₀ (abs_nonneg (M.radiusS r-r)) habs 2
    rw [sq_abs] at Hsq
    have hcharge : (M.data.rmin+M.cavityCapTravel)^2 ≤ (2*M.cavityCapTravel)^2 :=
      pow_le_pow_left₀ (add_nonneg M.data.rmin_nonneg ht0)
        (by linarith only [hwallTravel]) 2
    have hdef := M.radiusThermal_nonneg ⟨M.data.rmin_nonneg.trans hr.1.le,hr.2.le⟩
    nlinarith only [Hsq,hcharge,hdef,sq_nonneg M.cavityCapTravel]

theorem Potential.all_nonpositive_squared_mismatch_ae
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    ∀ᵐr,r∈Icc M.data.rmin 1→p.H r≤0→
      (M.radiusS r-r)^2≤16*M.cavityCapTravel^2+2*M.radiusThermal r := by
  have hmom:=M.radius_moments
  filter_upwards [p.hzero,volume.ae_ne M.data.rmin,volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri hnonpos
  have hro : r∈Ioo M.data.rmin 1 := ⟨lt_of_le_of_ne hri.1 hr0.symm,lt_of_le_of_ne hri.2 hr1⟩
  rcases hnonpos.eq_or_lt with hz|hneg
  · have Hp:=laplaceComparisonStrength_logSlope_mem M.data.hd.ne' M.hlam.ne' r
    have H:=(comparison_gradient_contact_mismatch (M.data.hrbounds.1.trans hro.1) (laplaceComparisonStrength_pos _ M.hlam r)
      ⟨Hp.1,Hp.2.le⟩ (hmom.2.2 r hri).1.1 (hmom.2.2 r hri).2.1 (hrzero hri hz).1).2
    change (M.radiusS r-r)^2≤M.radiusThermal r at H
    have hdef := M.radiusThermal_nonneg ⟨M.data.rmin_nonneg.trans hri.1,hri.2⟩
    nlinarith [sq_nonneg M.cavityCapTravel]
  · exact p.all_negative_point_squared_mismatch hro hneg

theorem Potential.all_nonpositive_squared_mismatch_ae_high_mass
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    ∀ᵐu,u∈Icc M.data.s 1 → p.H (M.sweepRadius u) ≤ 0 →
      (orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)^2 ≤ 16*M.cavityCapTravel^2+
        2*(orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2) := by
  have H:=ae_inverse_pullback
    (inverseIntegralConstraints_lipschitz M.data.hm M.data.hM M.alpha.property)
    (fun u (_ : u∈Icc M.data.s 1)=>M.sweepRadius_bounds u)

    (fun u hu=>M.sweepRadius_spec hu)

    p.all_nonpositive_squared_mismatch_ae
  filter_upwards [H] with u hu hui hnonpos
  have HH:=hu hui hnonpos
  simpa only [radiusS,radiusB,radiusThermal,M.sweepRadius_spec hui] using HH

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

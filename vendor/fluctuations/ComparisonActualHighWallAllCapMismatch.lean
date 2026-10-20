module

public import ComparisonActualHighWallStarSelectionDistinct
public import ComparisonActualHighWallInitialMismatchAmplitude

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def full_radius_thermal (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) : ℝ→ℝ :=
  fun r=>M.radiusB r-(M.radiusS r)^2

theorem full_radius_thermal_nonneg
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc M.data.rmin 1) : 0 ≤ M.full_radius_thermal r :=
  sub_nonneg.mpr (M.radius_moments.2.2 r hr).2.1

theorem Potential.full_component_endpoint_alternatives
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {r : ℝ} (hr : r∈p.negativeSet) :
    (p.H (sInf (ordConnectedComponent p.negativeSet r))=0 ∨
      sInf (ordConnectedComponent p.negativeSet r)=M.data.rmin) ∧
    (p.H (sSup (ordConnectedComponent p.negativeSet r))=0 ∨
      sSup (ordConnectedComponent p.negativeSet r)=1) := by
  obtain ⟨c,hcl,hcr,_,hcLeft,hcRight⟩ := p.negative_component_endpoints hr
  simpa only [hcl,hcr] using And.intro hcLeft hcRight

theorem Potential.full_cap_point_mean_le_right
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {l z r : ℝ} (hl : M.data.rmin≤l) (hz : z≤1) (hr : r∈Ioo l z)
    (hright : p.H z=0) (hneg : p.H r<0) : M.radiusS r≤z := by
  let g:=laplaceComparisonStrength M.data.d (M.data.d^2)
  let slope:=comparisonLogSlope g
  let S:=M.radiusS
  let B:=fun t=>orderedPathB (n+1) M.bf M.hf (M.alpha.val.val t)
  let J:=fun t=>M.controlFactor t*g t
  have hmom:=M.radius_moments
  have hsub : Icc l z⊆Icc M.data.rmin 1 := Icc_subset_Icc hl hz
  have hsubo : Ioo l z⊆Ioc M.data.rmin 1 := fun t ht=>⟨hl.trans_lt ht.1,ht.2.le.trans hz⟩
  have hJ t (_ht : t∈Icc M.data.rmin 1) : 0<J t :=
    mul_pos (inverseControlFactor_pos _ _ t) (laplaceComparisonStrength_pos _ (sq_pos_of_pos M.data.hd) _)
  have hDp : ∀ᵐt,t∈Icc M.data.rmin 1→HasDerivAt p.H
      (J t*comparisonBracket (slope t) t (S t) (B t)) t := by
    filter_upwards [p.hD,volume.ae_ne M.data.rmin] with t ht ht0 hti
    have hp : 0<t := M.data.hrbounds.1.trans_le hti.1
    have H:=ht hti
    rw [comparison_gradient_slope hp.ne' (laplaceComparisonStrength_pos _ (sq_pos_of_pos M.data.hd) _).ne'] at H
    convert H using 1
    dsimp [J,S,B,slope,g,radiusS,comparisonBracket]
    ring
  have hpm : MonotoneOn slope (Ioc M.data.rmin 1) := by
    intro s hs t ht hst
    dsimp [slope,g]
    rw [laplaceComparisonStrength_logSlope M.data.hd.ne' (sq_pos_of_pos M.data.hd).ne',
      laplaceComparisonStrength_logSlope M.data.hd.ne' (sq_pos_of_pos M.data.hd).ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hst (sq_pos_of_pos M.data.hd).le) (pow_nonneg M.data.hd.le _))
  have hpb t (_ht : t∈Ioc M.data.rmin 1) : slope t∈Icc (0:ℝ) 1 := by
    have H:=laplaceComparisonStrength_logSlope_mem M.data.hd.ne' (sq_pos_of_pos M.data.hd).ne' t
    exact ⟨H.1,H.2.le⟩
  have hSr : MonotoneOn S (Ioc M.data.rmin 1) := hmom.1.mono Ioc_subset_Icc_self
  have hBr : MonotoneOn B (Ioc M.data.rmin 1) := hmom.2.1.mono Ioc_subset_Icc_self
  have hS0 t (ht : t∈Ioc M.data.rmin 1) : 0≤S t := (hmom.2.2 t (Ioc_subset_Icc_self ht)).1.1
  have hB2 t (ht : t∈Ioc M.data.rmin 1) : (S t)^2≤B t := (hmom.2.2 t (Ioc_subset_Icc_self ht)).2.1
  have hac : AbsolutelyContinuousOnInterval p.H l z := p.hH.mono (by
    simpa only [uIcc_of_le M.data.hr,uIcc_of_le (hr.1.trans hr.2).le] using hsub)
  have hDsub := hDp.mono (fun t ht hti=>ht (hsub hti))
  exact cap_S_le_right (S:=S) (B:=B) (M.data.hrbounds.1.le.trans hl) hr hac
    (fun t ht=>hJ t (hsub ht)) hDsub hright hneg
    (fun t ht=>hpb t (hsubo ht)) (hSr.mono hsubo)
    (fun t ht=>hS0 t (hsubo ht)) (fun t ht=>hB2 t (hsubo ht))

theorem Potential.full_all_negative_point_squared_mismatch
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {r : ℝ} (hr : r∈Ioo M.data.rmin 1) (hneg : p.H r<0) :
    (M.radiusS r-r)^2≤16*(M.data.rmin+M.cavityCapTravel)^2+2*M.full_radius_thermal r := by
  have hrneg : r∈p.negativeSet := ⟨hr,hneg⟩
  obtain ⟨hl,hlr,hrz,hz,heq,_,_⟩:=wholeCap_component_endpoints p.negativeSet_open
    (inter_subset_left.trans Ioo_subset_Icc_self) hrneg
  have hinterval : ∀t∈Ioo (sInf (ordConnectedComponent p.negativeSet r))
      (sSup (ordConnectedComponent p.negativeSet r)),p.H t<0 := by
    intro t ht
    exact (ordConnectedComponent_subset (heq.symm ▸ ht)).2
  have hwidth:=(p.cap_interval_travel hl (hlr.trans hrz).le hz hinterval).2.1
  have hend:=p.full_component_endpoint_alternatives hrneg
  rcases hend.1 with hleft|hwall
  · have H:=p.cap_point_squared_mismatch hl hz ⟨hlr,hrz⟩ hleft hend.2 hneg
    have hs:=pow_le_pow_left₀ (sub_nonneg.mpr (hlr.trans hrz).le) hwidth 2
    have HG := pow_le_pow_left₀ M.cavityCapTravel_nonneg
      (by linarith [M.data.hrbounds.1] : M.cavityCapTravel ≤ M.data.rmin+M.cavityCapTravel) 2
    dsimp only [full_radius_thermal]
    nlinarith only [H,hs,HG]
  · have hmom:=M.radius_moments
    have hS0 : 0≤M.radiusS r := (hmom.2.2 r (Ioo_subset_Icc_self hr)).1.1
    have hSz : M.radiusS r ≤ sSup (ordConnectedComponent p.negativeSet r) := by
      rcases hend.2 with hc|ht
      · exact p.full_cap_point_mean_le_right hl hz ⟨hlr,hrz⟩ hc hneg
      · rw [ht]
        exact (hmom.2.2 r (Ioo_subset_Icc_self hr)).1.2
    rw [hwall] at hwidth
    have ht0:=M.cavityCapTravel_nonneg
    have hSbound : M.radiusS r ≤ M.data.rmin+M.cavityCapTravel := by linarith [hSz,hwidth]
    have hrbound : r ≤ M.data.rmin+M.cavityCapTravel := by linarith [hrz,hwidth]
    have habs : |M.radiusS r-r|≤M.data.rmin+M.cavityCapTravel :=
      abs_le.mpr ⟨by linarith only [hS0,hrbound],by linarith only [hSbound,hr.1,M.data.hrbounds.1.le]⟩
    have Hsq := pow_le_pow_left₀ (abs_nonneg (M.radiusS r-r)) habs 2
    rw [sq_abs] at Hsq
    have hdef := M.full_radius_thermal_nonneg (Ioo_subset_Icc_self hr)
    nlinarith only [Hsq,hdef,sq_nonneg (M.data.rmin+M.cavityCapTravel)]

theorem Potential.full_all_nonpositive_squared_mismatch_ae
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    ∀ᵐr,r∈Icc M.data.rmin 1→p.H r≤0→
      (M.radiusS r-r)^2≤16*(M.data.rmin+M.cavityCapTravel)^2+2*M.full_radius_thermal r := by
  have hmom:=M.radius_moments
  filter_upwards [p.hzero,volume.ae_ne M.data.rmin,volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri hnonpos
  have hro : r∈Ioo M.data.rmin 1 := ⟨lt_of_le_of_ne hri.1 hr0.symm,lt_of_le_of_ne hri.2 hr1⟩
  rcases hnonpos.eq_or_lt with hz|hneg
  · have Hp:=laplaceComparisonStrength_logSlope_mem M.data.hd.ne' (sq_pos_of_pos M.data.hd).ne' r
    have H:=(comparison_gradient_contact_mismatch (M.data.hrbounds.1.trans hro.1) (laplaceComparisonStrength_pos _ (sq_pos_of_pos M.data.hd) r)
      ⟨Hp.1,Hp.2.le⟩ (hmom.2.2 r hri).1.1 (hmom.2.2 r hri).2.1 (hrzero hri hz).1).2
    change (M.radiusS r-r)^2≤M.full_radius_thermal r at H
    have hdef := M.full_radius_thermal_nonneg hri
    nlinarith [sq_nonneg (M.data.rmin+M.cavityCapTravel)]
  · exact p.full_all_negative_point_squared_mismatch hro hneg

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

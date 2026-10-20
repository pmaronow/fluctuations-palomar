module

public import ComparisonActualHighOnlyCapComponents
public import ComparisonNativeCapMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 12000000

namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.cap_point_squared_mismatch
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {l z r : ℝ} (hl : (0:ℝ)≤l) (hz : z≤1) (hr : r∈Ioo l z)
    (hleft : p.H l=0) (hright : p.H z=0 ∨ z=1) (hneg : p.H r<0) :
    (M.radiusS r-r)^2≤16*(z-l)^2+2*(fun t=>M.radiusB t-(M.radiusS t)^2) r := by
  let g:=(laplaceComparisonStrength M.data.d M.lam)
  let slope:=comparisonLogSlope g
  let S:=M.radiusS
  let B:=fun t=>orderedPathB (n+1) M.bf M.hf (M.alpha.val.val t)
  let J:=fun t=>M.controlFactor t*g t
  have hmom:=M.radius_moments
  have hsub : Icc l z⊆Icc (0:ℝ) 1 := Icc_subset_Icc hl hz
  have hsubo : Ioo l z⊆Ioc (0:ℝ) 1 := fun t ht=>⟨hl.trans_lt ht.1,ht.2.le.trans hz⟩
  have hJ t (_ht : t∈Icc (0:ℝ) 1) : 0<J t :=
    mul_pos (inverseControlFactor_pos _ _ t) (laplaceComparisonStrength_pos _ (M.hlam) _)
  have hDp : ∀ᵐt,t∈Icc (0:ℝ) 1→HasDerivAt p.H
      (J t*comparisonBracket (slope t) t (S t) (B t)) t := by
    filter_upwards [p.hD,volume.ae_ne (0:ℝ)] with t ht ht0 hti
    have hp : 0<t := lt_of_le_of_ne hti.1 ht0.symm
    have H:=ht hti
    rw [comparison_gradient_slope hp.ne' (laplaceComparisonStrength_pos _ (M.hlam) _).ne'] at H
    convert H using 1
    dsimp [J,S,B,slope,g,radiusS,comparisonBracket]
    ring
  have hpm : MonotoneOn slope (Ioc (0:ℝ) 1) := by
    intro s hs t ht hst
    dsimp [slope,g]
    rw [laplaceComparisonStrength_logSlope M.data.hd.ne' (M.hlam).ne',
      laplaceComparisonStrength_logSlope M.data.hd.ne' (M.hlam).ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hst (M.hlam).le) (pow_nonneg M.data.hd.le _))
  have hpb t (_ht : t∈Ioc (0:ℝ) 1) : slope t∈Icc (0:ℝ) 1 := by
    have H:=laplaceComparisonStrength_logSlope_mem M.data.hd.ne' (M.hlam).ne' t
    exact ⟨H.1,H.2.le⟩
  have hSr : MonotoneOn S (Ioc (0:ℝ) 1) := hmom.1.mono Ioc_subset_Icc_self
  have hBr : MonotoneOn B (Ioc (0:ℝ) 1) := hmom.2.1.mono Ioc_subset_Icc_self
  have hS0 t (ht : t∈Ioc (0:ℝ) 1) : 0≤S t := (hmom.2.2 t (Ioc_subset_Icc_self ht)).1.1
  have hB2 t (ht : t∈Ioc (0:ℝ) 1) : (S t)^2≤B t := (hmom.2.2 t (Ioc_subset_Icc_self ht)).2.1
  have hac : AbsolutelyContinuousOnInterval p.H l z := p.hH.mono (by
    simpa only [uIcc_of_le zero_le_one,uIcc_of_le (hr.1.trans hr.2).le] using hsub)
  have hDsub := hDp.mono (fun t ht hti=>ht (hsub hti))
  rcases hright with hc|hterminal
  · exact cap_interior_mismatch (hl) hr hac (fun t ht=>hJ t (hsub ht)) hDsub hleft hc hneg
      (hpm.mono hsubo) (fun t ht=>hpb t (hsubo ht)) (hSr.mono hsubo) (hBr.mono hsubo)
      (fun t ht=>hS0 t (hsubo ht)) (fun t ht=>hB2 t (hsubo ht))
  · have hri : r∈Ioc (0:ℝ) 1 := hsubo hr
    have hSr1 : S r≤z := by
      rw [hterminal]
      exact (hmom.2.2 r (Ioc_subset_Icc_self hri)).1.2
    exact potential_left_contact_cap_mismatch hl hz hr p.hH hJ hDp hleft hneg hpm hpb
      hSr hBr (hS0 r hri) hSr1 hB2

theorem Potential.negative_point_squared_mismatch
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hneg : p.H r<0)
    (haway : (0:ℝ)+M.cavityCapTravel<r) :
    (M.radiusS r-r)^2≤16*M.cavityCapTravel^2+2*(fun t=>M.radiusB t-(M.radiusS t)^2) r := by
  have hrneg : r∈p.negativeSet := ⟨hr,hneg⟩
  obtain ⟨hl,hlr,hrz,hz,heq,_,_⟩:=wholeCap_component_endpoints p.negativeSet_open
    p.negativeSet_subset hrneg
  have hinterval : ∀t∈Ioo (sInf (ordConnectedComponent p.negativeSet r))
      (sSup (ordConnectedComponent p.negativeSet r)),p.H t<0 := by
    intro t ht
    exact (ordConnectedComponent_subset (heq.symm ▸ ht)).2
  have hwidth:=(p.cap_interval_travel hl (hlr.trans hrz).le hz hinterval).2.1
  obtain ⟨c,hcl,hcr,_,hcLeft,hcRight⟩:=p.negative_component_endpoints hrneg
  have hend : (p.H (sInf (ordConnectedComponent p.negativeSet r))=0 ∨
      sInf (ordConnectedComponent p.negativeSet r)=(0:ℝ)) ∧
    (p.H (sSup (ordConnectedComponent p.negativeSet r))=0 ∨
      sSup (ordConnectedComponent p.negativeSet r)=1) := by
    simpa only [hcl,hcr] using And.intro hcLeft hcRight
  have hleft : p.H (sInf (ordConnectedComponent p.negativeSet r))=0 := by
    rcases hend.1 with H|H
    · exact H
    · rw [H] at hwidth
      exfalso
      linarith only [hwidth,hrz,haway]
  have H:=p.cap_point_squared_mismatch hl hz ⟨hlr,hrz⟩ hleft hend.2 hneg
  have hs:=pow_le_pow_left₀ (sub_nonneg.mpr (hlr.trans hrz).le) hwidth 2
  nlinarith

theorem Potential.nonpositive_squared_mismatch_ae
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    ∀ᵐr,r∈Icc (0:ℝ) 1→(0:ℝ)+M.cavityCapTravel<r→p.H r≤0→
      (M.radiusS r-r)^2≤16*M.cavityCapTravel^2+2*(fun t=>M.radiusB t-(M.radiusS t)^2) r := by
  have hmom:=M.radius_moments
  filter_upwards [p.hzero,volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri haway hnonpos
  have hro : r∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hri.1 hr0.symm,lt_of_le_of_ne hri.2 hr1⟩
  rcases hnonpos.eq_or_lt with hz|hneg
  · have H:=(hrzero hri hz).2.2
    change (M.radiusS r-r)^2≤M.radiusB r-(M.radiusS r)^2 at H
    have hdef := sub_nonneg.mpr (hmom.2.2 r hri).2.1
    nlinarith [sq_nonneg M.cavityCapTravel]
  · exact p.negative_point_squared_mismatch hro hneg haway

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

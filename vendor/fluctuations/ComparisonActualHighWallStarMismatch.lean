module

public import ComparisonActualHighWallCapCoverGeometry
public import ComparisonNativeCapMismatch
public import ComparisonActualHighWallInnovation

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy WholeUnitSideKernel
set_option maxHeartbeats 6500000

private theorem shifted_potential_left_contact_cap_mismatch
    {H J p S B : ℝ→ℝ} {origin a z r : ℝ}
    (horigin : origin≤1) (horigin0 : 0≤origin) (ha : origin≤a) (hz : z≤1) (hr : r∈Ioo a z)
    (hH : AbsolutelyContinuousOnInterval H origin 1)
    (hJ : ∀t∈Icc origin 1,0<J t)
    (hD : ∀ᵐ t,t∈Icc origin 1→HasDerivAt H (J t*comparisonBracket (p t) t (S t) (B t)) t)
    (haH : H a=0) (hrH : H r<0)
    (hp : MonotoneOn p (Ioc origin 1))
    (hpb : ∀t∈Ioc origin 1,p t∈Icc (0:ℝ) 1)
    (hS : MonotoneOn S (Ioc origin 1))
    (hBm : MonotoneOn B (Ioc origin 1))
    (hSr : 0≤S r) (hSz : S r≤z)
    (hBb : ∀t∈Ioc origin 1,(S t)^2≤B t) :
    (S r-r)^2≤16*(z-a)^2+2*(B r-(S r)^2) := by
  have hr01 : r∈Ioc origin 1 := ⟨ha.trans_lt hr.1,hr.2.le.trans hz⟩
  have hthermal := sub_nonneg.mpr (hBb r hr01)
  have hell : 0≤z-a := sub_nonneg.mpr (hr.1.trans hr.2).le
  by_cases hSr' : S r≤r
  · have hsub : Icc a r⊆Icc origin 1 := Icc_subset_Icc ha hr01.2
    obtain ⟨l,hli,hgl⟩ := potential_negative_left_witness hr.1
      (hH.mono (by simpa only [uIcc_of_le horigin,uIcc_of_le hr.1.le] using hsub))
      (fun t ht=>hJ t (hsub ht)) (hD.mono (fun t ht hti=>ht (hsub hti)))
      (by simpa only [haH] using hrH)
    have hl : l∈Ioc origin 1 := ⟨ha.trans_lt hli.1,hli.2.le.trans hr01.2⟩
    have hleft : comparisonBracket (p r) l (S r) (B r)≤0 :=
      (comparisonBracket_mono_moments (horigin0.trans_lt hl.1) (hpb r hr01)
        (hS hl hr01 hli.2.le) (hBm hl hr01 hli.2.le)).trans
        ((comparisonBracket_antitone (horigin0.trans_lt hl.1) (hBb l hl) (hp hl hr01 hli.2.le)).trans hgl.le)
    have hb := comparisonBracket_left_mismatch (horigin0.trans_lt hl.1) hli.2.le
      (hpb r hr01) hSr hSr' (hBb r hr01) hleft
    have hlen : 0≤r-l := sub_nonneg.mpr hli.2.le
    have hlen' : r-l≤z-a := by linarith [hli.1,hr.2]
    have hs := pow_le_pow_left₀ hlen hlen' 2
    nlinarith
  · have hdiff : 0≤S r-r := by linarith
    have hbound : S r-r≤z-a := by linarith [hr.1]
    have hs := pow_le_pow_left₀ hdiff hbound 2
    nlinarith [sq_nonneg (z-a)]

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.cap_point_squared_mismatch
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {l z r : ℝ} (hl : M.data.rmin≤l) (hz : z≤1) (hr : r∈Ioo l z)
    (hleft : p.H l=0) (hright : p.H z=0 ∨ z=1) (hneg : p.H r<0) :
    (M.radiusS r-r)^2≤16*(z-l)^2+2*(fun t=>M.radiusB t-(M.radiusS t)^2) r := by
  let g:=M.data.g
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
  rcases hright with hc|hterminal
  · exact cap_interior_mismatch (M.data.hrbounds.1.le.trans hl) hr hac (fun t ht=>hJ t (hsub ht)) hDsub hleft hc hneg
      (hpm.mono hsubo) (fun t ht=>hpb t (hsubo ht)) (hSr.mono hsubo) (hBr.mono hsubo)
      (fun t ht=>hS0 t (hsubo ht)) (fun t ht=>hB2 t (hsubo ht))
  · have hri : r∈Ioc M.data.rmin 1 := hsubo hr
    have hSr1 : S r≤z := by
      rw [hterminal]
      exact (hmom.2.2 r (Ioc_subset_Icc_self hri)).1.2
    exact shifted_potential_left_contact_cap_mismatch M.data.hr M.data.hrbounds.1.le hl hz hr p.hH hJ hDp hleft hneg hpm hpb
      hSr hBr (hS0 r hri) hSr1 hB2

theorem Potential.negative_point_squared_mismatch
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {r : ℝ} (hr : r∈Ioo M.data.rmin 1) (hneg : p.H r<0)
    (haway : M.data.rmin+M.cavityCapTravel<r) :
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
      sInf (ordConnectedComponent p.negativeSet r)=M.data.rmin) ∧
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
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    ∀ᵐr,r∈Icc M.data.rmin 1→M.data.rmin+M.cavityCapTravel<r→p.H r≤0→
      (M.radiusS r-r)^2≤16*M.cavityCapTravel^2+2*(fun t=>M.radiusB t-(M.radiusS t)^2) r := by
  have hmom:=M.radius_moments
  filter_upwards [p.hzero,volume.ae_ne M.data.rmin,volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri haway hnonpos
  have hro : r∈Ioo M.data.rmin 1 := ⟨lt_of_le_of_ne hri.1 hr0.symm,lt_of_le_of_ne hri.2 hr1⟩
  rcases hnonpos.eq_or_lt with hz|hneg
  · have H:=(hrzero hri hz).2.2
    change (M.radiusS r-r)^2≤M.radiusB r-(M.radiusS r)^2 at H
    have hdef := sub_nonneg.mpr (hmom.2.2 r hri).2.1
    nlinarith [sq_nonneg M.cavityCapTravel]
  · exact p.negative_point_squared_mismatch hro hneg haway

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

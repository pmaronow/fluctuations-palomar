module

public import ComparisonNativeBandAssembly
public import ComparisonCapSideTraceWall
public import ComparisonCapSideTraceTerminal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 4800000

theorem potential_left_contact_cap_mismatch
    {H J p S B : ℝ→ℝ} {a z r : ℝ}
    (ha : 0≤a) (hz : z≤1) (hr : r∈Ioo a z)
    (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀t∈Icc (0:ℝ) 1,0<J t)
    (hD : ∀ᵐ t,t∈Icc (0:ℝ) 1→HasDerivAt H (J t*comparisonBracket (p t) t (S t) (B t)) t)
    (haH : H a=0) (hrH : H r<0)
    (hp : MonotoneOn p (Ioc (0:ℝ) 1))
    (hpb : ∀t∈Ioc (0:ℝ) 1,p t∈Icc (0:ℝ) 1)
    (hS : MonotoneOn S (Ioc (0:ℝ) 1))
    (hBm : MonotoneOn B (Ioc (0:ℝ) 1))
    (hSr : 0≤S r) (hSz : S r≤z)
    (hBb : ∀t∈Ioc (0:ℝ) 1,(S t)^2≤B t) :
    (S r-r)^2≤16*(z-a)^2+2*(B r-(S r)^2) := by
  have hr01 : r∈Ioc (0:ℝ) 1 := ⟨ha.trans_lt hr.1,hr.2.le.trans hz⟩
  have hthermal := sub_nonneg.mpr (hBb r hr01)
  have hell : 0≤z-a := sub_nonneg.mpr (hr.1.trans hr.2).le
  by_cases hSr' : S r≤r
  · have hsub : Icc a r⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hr01.2
    obtain ⟨l,hli,hgl⟩ := potential_negative_left_witness hr.1
      (hH.mono (by simpa only [uIcc_of_le zero_le_one,uIcc_of_le hr.1.le] using hsub))
      (fun t ht=>hJ t (hsub ht)) (hD.mono (fun t ht hti=>ht (hsub hti)))
      (by simpa only [haH] using hrH)
    have hl : l∈Ioc (0:ℝ) 1 := ⟨ha.trans_lt hli.1,hli.2.le.trans hr01.2⟩
    have hleft : comparisonBracket (p r) l (S r) (B r)≤0 :=
      (comparisonBracket_mono_moments hl.1 (hpb r hr01)
        (hS hl hr01 hli.2.le) (hBm hl hr01 hli.2.le)).trans
        ((comparisonBracket_antitone hl.1 (hBb l hl) (hp hl hr01 hli.2.le)).trans hgl.le)
    have hb := comparisonBracket_left_mismatch hl.1 hli.2.le
      (hpb r hr01) hSr hSr' (hBb r hr01) hleft
    have hlen : 0≤r-l := sub_nonneg.mpr hli.2.le
    have hlen' : r-l≤z-a := by linarith [hli.1,hr.2]
    have hs := pow_le_pow_left₀ hlen hlen' 2
    nlinarith
  · have hdiff : 0≤S r-r := by linarith
    have hbound : S r-r≤z-a := by linarith [hr.1]
    have hs := pow_le_pow_left₀ hdiff hbound 2
    nlinarith [sq_nonneg (z-a)]

theorem native_actual_cap_mismatch_endpoint_cases
    (m : NativeBandModel) {a z r : ℝ} (ha : 0≤a) (hz : z≤1) (hr : r∈Ioo a z)
    (hboundary : (m.H a=0 ∧ m.H z=0) ∨ (a=0 ∧ m.H z=0) ∨ (m.H a=0 ∧ z=1))
    (hrH : m.H r<0) :
    (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)^2≤
      16*(z-a)^2+2*m.thermal (m.alpha.val.val r) := by
  have hmom := comparisonVariableEndpoint_radius_moments m.hc m.hk m.hkc m.hm m.hM
    (m.n+1) (by omega) m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hr01 : r∈Icc (0:ℝ) 1 := ⟨ha.trans hr.1.le,hr.2.le.trans hz⟩
  rcases hboundary with ho|hi|ht
  · exact (actual_variableEndpoint_comparison_cap_interior_geometry m.hc m.hk m.hkc m.hm m.hM
      m.hN m.hlog m.hd m.hnd m.hlam m.hld (m.n+1) (by omega) m.b m.h m.hb m.hlb m.hh m.hh0
      m.alpha m.H m.multiplier m.hH m.hJ m.hD ha hz hr hr le_rfl ho.1 ho.2 hrH hrH).2.2
  · have hs := actual_variableEndpoint_comparison_cap_right_bound m.hc m.hk m.hkc m.hm m.hM
      m.hN m.hlog m.hd m.hnd m.hlam m.hld (m.n+1) (by omega) m.b m.h m.hb m.hlb m.hh m.hh0
      m.alpha m.H m.multiplier m.hH m.hJ m.hD ha hz hr hi.2 hrH
    have hb := hmom.2.2 r hr01
    have hS0 : 0≤orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r) := hb.1.1
    have hSmax : orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)≤z := hs
    have hB : (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r))^2≤orderedPathB (m.n+1) m.bf m.hf (m.alpha.val.val r) := hb.2.1
    dsimp [NativeBandModel.thermal]
    rw [hi.1,sub_zero]
    have hnon : 0≤z := hr01.1.trans hr.2.le
    have hdiff : |orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r|≤z :=
      abs_le.mpr ⟨by linarith [hr.2],by linarith [hr01.1]⟩
    have hsq := (sq_le_sq₀ (abs_nonneg _) hnon).mpr hdiff
    simp only [sq_abs] at hsq
    nlinarith [sq_nonneg z]
  · let p := comparisonLogSlope (laplaceComparisonStrength m.d m.lam)
    let S := fun t=>orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val t)
    let B := fun t=>orderedPathB (m.n+1) m.bf m.hf (m.alpha.val.val t)
    have hDp : ∀ᵐ t,t∈Icc (0:ℝ) 1→HasDerivAt m.H
        ((m.multiplier t*laplaceComparisonStrength m.d m.lam t)*comparisonBracket (p t) t (S t) (B t)) t := by
      filter_upwards [m.hD,volume.ae_ne (0:ℝ)] with t hdt ht0 ht01
      have htp : 0<t := lt_of_le_of_ne ht01.1 ht0.symm
      have hh := hdt ht01
      rw [comparison_gradient_slope htp.ne' (laplaceComparisonStrength_pos m.d m.hlam t).ne'] at hh
      convert hh using 1
      dsimp [p,S,B,comparisonBracket,NativeBandModel.bf,NativeBandModel.hf,NativeBandModel.R]
      ring
    have hpm : MonotoneOn p (Ioc (0:ℝ) 1) := by
      intro s hs t ht hst
      dsimp [p]
      rw [laplaceComparisonStrength_logSlope m.hd.ne' m.hlam.ne',laplaceComparisonStrength_logSlope m.hd.ne' m.hlam.ne']
      exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hst m.hlam.le) (pow_nonneg m.hd.le _))
    have hpb t (ht : t∈Ioc (0:ℝ) 1) : p t∈Icc (0:ℝ) 1 :=
      ⟨(laplaceComparisonStrength_logSlope_mem m.hd.ne' m.hlam.ne' t).1,
        (laplaceComparisonStrength_logSlope_mem m.hd.ne' m.hlam.ne' t).2.le⟩
    apply potential_left_contact_cap_mismatch ha hz hr m.hH
      (fun t ht=>mul_pos (m.hJ t ht) (laplaceComparisonStrength_pos m.d m.hlam t)) hDp ht.1 hrH hpm hpb
      (hmom.1.mono Ioc_subset_Icc_self) (hmom.2.1.mono Ioc_subset_Icc_self)
      (hmom.2.2 r hr01).1.1
      (by simpa only [ht.2] using (hmom.2.2 r hr01).1.2)
      (fun t ht=>(hmom.2.2 t (Ioc_subset_Icc_self ht)).2.1)

end OAI.SKFluctuations.LaplaceWindowFormalization

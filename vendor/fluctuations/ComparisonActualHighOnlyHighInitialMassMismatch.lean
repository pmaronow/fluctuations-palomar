module

public import ComparisonActualHighOnlyHighCalibratedMassBand
public import ComparisonNativeActualRegularInitialMassMismatchAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.flat_initial_mass_squared_mismatch_le
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {v A Rcut : ℝ} (hv : v∈Icc (0:ℝ) 1) (hs : M.data.s≤v) (hA : 0≤A)
    (hamp : ∀u∈Ioc (0:ℝ) v,(orderedPathS (n+1) M.bf M.hf u-M.R u)^2≤A)
    (hflat : ∀r∈Icc (0:ℝ) Rcut,comparisonLogSlope (laplaceComparisonStrength M.context.d M.lam) r=0)
    (hR : ∀u∈Icc M.data.s v,M.R u≤Rcut) :
    (∫u in 0..v,(orderedPathS (n+1) M.bf M.hf u-M.R u)^2)≤
      M.cavityCapTravel^2*v+A*(2*M.data.s+M.context.N^(-delta)*M.context.U) := by
  let f:=fun u=>(orderedPathS (n+1) M.bf M.hf u-M.R u)^2
  have hi:=M.mass_squared_mismatch_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl hv.2)
  have hilo:IntervalIntegrable f volume 0 M.data.s:=hi.mono_set (by
    rw [uIcc_of_le M.data.hs.1,uIcc_of_le hv.1];exact Icc_subset_Icc le_rfl hs)
  have hihi:IntervalIntegrable f volume M.data.s v:=hi.mono_set (by
    rw [uIcc_of_le hs,uIcc_of_le hv.1];exact Icc_subset_Icc M.data.hs.1 le_rfl)
  have hlow:(∫u in 0..M.data.s,f u)≤A*M.data.s:=by
    have H:=intervalIntegral.integral_mono_ae_restrict M.data.hs.1 hilo intervalIntegrable_const
      (by filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with u hu hu0
          exact hamp u ⟨lt_of_le_of_ne hu.1 hu0.symm,hu.2.trans hs⟩)
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using H
  have himask:IntervalIntegrable p.positiveMassMask volume M.data.s v:=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hs).mpr
      (p.positiveMassMask_integrable.mono_set (Icc_subset_Icc M.data.hs.1 hv.2))
  have hpoint:∀ᵐu∂volume.restrict (Icc M.data.s v),f u≤M.cavityCapTravel^2+A*p.positiveMassMask u:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (p.flat_nonpositive_abs_mismatch_ae_high_mass hflat),
      ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with u hu hpoint hu0
    have hui:u∈Icc M.data.s 1:=⟨hu.1,hu.2.trans hv.2⟩
    by_cases hp:p.H (M.R u)≤0
    · have hm:=(p.positiveMassMask_zero_iff u).mpr hp
      rw [hm,mul_zero,add_zero]
      have H:=pow_le_pow_left₀ (abs_nonneg _) (hpoint hui (hR u hu) hp) 2
      simpa only [f,sq_abs] using H
    · have hm:p.positiveMassMask u=1:=by
        have HR:=omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
          M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha u
        simp only [Potential.positiveMassMask,indicator_of_mem (show M.R u∈p.positiveRadiusSet from ⟨HR,lt_of_not_ge hp⟩)]
      rw [hm,mul_one]
      have H:=hamp u ⟨lt_of_le_of_ne (M.data.hs.1.trans hu.1) hu0.symm,hu.2⟩
      dsimp only [f]
      nlinarith only [H,sq_nonneg M.cavityCapTravel]
  have hhigh:=intervalIntegral.integral_mono_ae_restrict hs hihi
    (intervalIntegrable_const.add (himask.const_mul A)) hpoint
  rw [intervalIntegral.integral_add intervalIntegrable_const (himask.const_mul A),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul] at hhigh
  simp only [smul_eq_mul] at hhigh
  have hmask:(∫u in M.data.s..v,p.positiveMassMask u)≤M.data.s+M.context.N^(-delta)*M.context.U:=by
    rw [intervalIntegral.integral_of_le hs,←integral_Icc_eq_integral_Ioc]
    apply le_trans _ p.positiveMassMask_mass_le
    apply setIntegral_mono_set p.positiveMassMask_integrable
      (ae_of_all _ (fun u=>by dsimp only [Potential.positiveMassMask];exact indicator_nonneg (fun _ _=>zero_le_one) _))
      (Eventually.of_forall (Icc_subset_Icc M.data.hs.1 hv.2))
  have HM:=mul_le_mul_of_nonneg_left hmask hA
  rw [←intervalIntegral.integral_add_adjacent_intervals hilo hihi]
  nlinarith only [hlow,hhigh,HM,mul_nonneg (sq_nonneg M.cavityCapTravel) M.data.hs.1]

theorem actual_HIGH_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2) atTop atTop)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*(M n).xs,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/((M n).xs)^3)
      atTop (𝓝 0) := by
  obtain ⟨B,hB,Hmean⟩:=eventually_actual_high_only_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let K:=(B+Az+1/cl)*(1+C)
  have hK : 0 < K := by dsimp only [K];positivity
  have hroom' : 0 < 3*m+delta := by linarith only [hm,hdelta]
  have Htravel:=actual_cap_travel_ratio_tendsto_zero_along hC0 hroom' dim hdim M (fun n=>(M n).xs) (fun _=>le_rfl)
  have Hfloor:Tendsto (fun n=>(2*(M n).data.s+(M n).context.N^(-delta)*(M n).context.U)/(M n).xs) atTop (𝓝 0):=by
    simpa only [add_div,mul_div_assoc,mul_zero,zero_add] using
      (G.omission_over_test_zero.const_mul 2).add
        (actual_floor_mass_ratio_tendsto_zero_along hC0 hroom' dim hdim M (fun n=>(M n).xs) (fun _=>le_rfl))
  have Htotal:=((Htravel.pow 2).const_mul C).add (Hfloor.const_mul (K^2))
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero] at Htotal
  have HW:=(G.xs_zero.const_mul C).eventually (eventually_le_nhds (by simp : C*(0:ℝ)<1))
  let Kr:=(Az+1/cl)*(1+C)
  have hKr:0 < Kr:=by dsimp only [Kr];positivity
  have Hflat:=comparison_strength_eventually_flat_of_divergence
    (fun n=>(M n).context.d) (fun n=>(M n).lam) (fun n=>(M n).xs)
    (Eventually.of_forall fun n=>⟨(M n).context.hd,(M n).hlam,(M n).hxs,(M n).hld⟩) hlarge hKr
  apply squeeze_zero' _ _ Htotal
  · filter_upwards [] with n
    have hw:=(M n).hxs
    exact div_nonneg (intervalIntegral.integral_nonneg (by positivity)
      (fun u _=>sq_nonneg _)) (pow_pos hw 3).le
  · filter_upwards [hdim.eventually Hmean,HW,Hflat,G.eventually_geometric_gates,G.positive_bands_high C hC] with n hnmean hnW hnflat hngate hnhigh
    have hw:=(M n).hxs
    obtain ⟨p⟩:=(M n).exists_potential_high_only hngate.2
    have hamp : ∀u∈Ioc (0:ℝ) (C*(M n).xs),
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2 ≤ K^2*((M n).xs)^2 := by
      intro u hu
      have hui : u∈Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2.trans hnW⟩
      have HS:=hnmean (M n) hngate.2 hngate.1 u ⟨hu.1,hu.2.trans hnW⟩
      have HR:=(M n).inverse_radius_le_source_mass hcl hAz hui
      have Hsmall : (M n).xs+u ≤ (1+C)*(M n).xs := by nlinarith only [hu.2]
      have Hmul:=mul_le_mul_of_nonneg_left Hsmall
        (show 0 ≤ B+Az+1/cl by positivity)
      have HS0:=(M n).mass_mean_nonneg hui
      have HR0:=(omittedSweepQuantile_bounds zero_le_one ⟨(M n).data.hs.1,(M n).data.hs1⟩ (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u).1
      have Habs : |orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u| ≤ K*(M n).xs := by
        apply abs_le.mpr
        dsimp only [K]
        constructor  <;> nlinarith only [HS,HR,HS0,HR0,Hmul]
      have Hsq:=pow_le_pow_left₀ (abs_nonneg _) Habs 2
      simpa only [sq_abs,mul_pow] using Hsq
    have hflat:∀r∈Icc (0:ℝ) (Kr*(M n).xs),comparisonLogSlope
        (laplaceComparisonStrength (M n).context.d (M n).lam) r=0:=by
      intro r hr
      have H:=(hnflat (r/(M n).xs) ⟨div_nonneg hr.1 hw.le,(div_le_iff₀ hw).mpr hr.2⟩).2.1
      simpa only [mul_div_cancel₀ r hw.ne'] using H
    have hR:∀u∈Icc (M n).data.s (C*(M n).xs),(M n).R u≤Kr*(M n).xs:=by
      intro u hu
      have HR:=(M n).inverse_radius_le_source_mass hcl hAz ⟨(M n).data.hs.1.trans hu.1,hu.2.trans hnW⟩
      have HH:=mul_le_mul_of_nonneg_left
        (show (M n).xs+u≤(1+C)*(M n).xs by linarith only [hu.2]) (show 0≤Az+1/cl by positivity)
      exact HR.trans (by convert HH using 1;dsimp only [Kr];ring)
    have Hint:=p.flat_initial_mass_squared_mismatch_le ⟨by positivity,hnW⟩ hnhigh
      (show 0≤K^2*(M n).xs^2 by positivity) hamp hflat hR
    have HD:=div_le_div_of_nonneg_right Hint (pow_pos hw 3).le
    apply HD.trans_eq
    field_simp

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

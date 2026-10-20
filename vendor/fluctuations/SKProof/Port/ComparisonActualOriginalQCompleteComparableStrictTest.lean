module

public import SKProof.Port.ComparisonActualOriginalQCompleteComparableProfile

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 24000000
theorem eventually_actual_comparable_test_point_strict_profile_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (hWupper : ∀ᶠn in atTop,(M n).directTestWorkingScale ≤ 1)
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∀ᶠn in atTop,cl*(M n).xs < (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs < cu*(M n).xs := by
  classical
  by_contra Hbad
  have Hfreq : ∃ᶠn in atTop,¬(cl*(M n).xs < (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs < cu*(M n).xs) := by
    simpa only [Filter.Frequently,not_not] using Hbad
  obtain ⟨theta,htheta,Htheta⟩:=extraction_of_frequently_atTop Hfreq
  obtain ⟨phi,hphi,htotal,d,HU,HV,hklo,hkup,Hrest⟩:=
    exists_actual_comparable_complete_direct_profile_original_q
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
      (fun n=>M (theta n)) (G.comp_original_q theta htheta)
      (htheta.tendsto_atTop.eventually hWupper) (fun n=>hcompare (theta n))
  let kappa:=(T/T)*scalarInitialDensityConstant G.hT d.beta
  have Hkappa : cl < kappa ∧ kappa < cu := by
    have H:=comparison_local_scalar_initial_density_strict_margins
      G.hT (epsilon:=0) (by norm_num) (by linarith [G.hT]) hclmargin hcumargin d.beta
    simpa only [sub_zero,kappa] using H
  have Hlimit : Tendsto (fun n=>(M (theta (phi n))).alpha.val.val (M (theta (phi n))).xs/
      (M (theta (phi n))).xs) atTop (𝓝 kappa) := by
    simpa only [mul_one,HV 1 zero_lt_one] using d.radius_inverse_cdf_limit 1
  have Hgood:=Hlimit.eventually (Ioo_mem_nhds Hkappa.1 Hkappa.2)
  obtain ⟨n,hn⟩:=Hgood.exists
  apply Htheta (phi n)
  exact ⟨(lt_div_iff₀ (M (theta (phi n))).hxs).mp hn.1,
    (div_lt_iff₀ (M (theta (phi n))).hxs).mp hn.2⟩

theorem actual_comparable_bad_test_strength_tendsto_zero_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (hWupper : ∀ᶠn in atTop,(M n).directTestWorkingScale ≤ 1)
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (Hbad : ∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) :
    Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop (𝓝 0) := by
  classical
  let f:=fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/(M n).xs^2
  have hf : ∀n,0 ≤ f n:=fun n=>div_nonneg
    (laplaceComparisonStrength_pos (M n).data.d (M n).hlam (M n).xs).le (sq_nonneg _)
  have Hsmall : ∀eta : ℝ,0 < eta → ∀ᶠn in atTop,f n < eta := by
    intro eta heta
    by_contra Hnone
    have Hfreq : ∃ᶠn in atTop,eta ≤ f n := by
      simpa only [Filter.Frequently,not_le] using Hnone
    obtain ⟨theta,htheta,Htheta⟩:=extraction_of_frequently_atTop Hfreq
    let Ccal:=max 1 (1/eta)
    have hCcal : 1 ≤ Ccal:=le_max_left _ _
    have hCeta : 1 ≤ Ccal*eta := by
      have H:=mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (1/eta)) heta.le
      simpa only [div_mul_cancel₀ 1 heta.ne'] using H
    have hCsq : 1 ≤ Ccal^2*eta:=hCeta.trans
      (mul_le_mul_of_nonneg_right (by nlinarith : Ccal ≤ Ccal^2) heta.le)
    have Hcompare : ∀n,(M (theta n)).xs^2 ≤ Ccal^2*
        laplaceComparisonStrength (M (theta n)).data.d (M (theta n)).lam (M (theta n)).xs := by
      intro n
      have H1:=(le_div_iff₀ (sq_pos_of_pos (M (theta n)).hxs)).mp (Htheta n)
      have H2:=mul_le_mul_of_nonneg_left H1 (sq_nonneg Ccal)
      have H3:=mul_le_mul_of_nonneg_right hCsq (sq_nonneg (M (theta n)).xs)
      nlinarith only [H2,H3]
    have Hgood:=eventually_actual_comparable_test_point_strict_profile_original_q
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
      (fun n=>M (theta n)) (G.comp_original_q theta htheta)
      (htheta.tendsto_atTop.eventually hWupper) hclmargin hcumargin Hcompare
    obtain ⟨n,hn⟩:=(Hgood.and (htheta.tendsto_atTop.eventually Hbad)).exists
    exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩
  change Tendsto f atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  filter_upwards [Hsmall eta heta] with n hn
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (hf n)] using hn

end OAI.SKFluctuations.LaplaceWindowFormalization

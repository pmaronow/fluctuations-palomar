module

public import ComparisonNativeActualGeneralHistoryStrictTest
public import ComparisonNativeActualGeneralHistoryMacroscopicDirectProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 24000000
theorem eventually_actual_weak_history_test_point_strict_profile_of_working_scale_lower
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∀ᶠn in atTop,cl*(M n).xs < (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs < cu*(M n).xs := by
  classical
  have hlo : ∀ᶠn in atTop,w0 ≤ (M n).canonicalDirectTestBandScale := by
    simpa only [hcanonical] using hWlower
  have hlarge := actual_weak_history_strength_ratio_atTop_of_working_scale_lower M G hw0 hlo
  by_contra Hbad
  have Hfreq : ∃ᶠn in atTop,¬(cl*(M n).xs < (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs < cu*(M n).xs) := by
    simpa only [Filter.Frequently,not_not] using Hbad
  obtain ⟨theta,htheta,Htheta⟩:=extraction_of_frequently_atTop Hfreq
  obtain ⟨phi,hphi,htotal,d,HU,HV,hklo,hkup⟩:=
    exists_actual_selected_bad_history_high_linear_profile_along_weak_macro
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
      (fun n=>M (theta n)) (G.comp theta htheta) (fun n=>W (theta n))
      (fun n=>hcanonical (theta n)) w0 hw0
      (htheta.tendsto_atTop.eventually hWlower) (htheta.tendsto_atTop.eventually hWupper)
      (fun n=>hcompare (theta n))
      (hlarge.comp htheta.tendsto_atTop)
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

theorem exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero
    (W : ℕ→ℝ) (hW : ∀n,0 ≤ W n)
    (H : ¬Tendsto W atTop (𝓝 0)) :
    ∃w0 : ℝ,0 < w0 ∧ ∃phi : ℕ→ℕ,StrictMono phi ∧ ∀n,w0 ≤ W (phi n) := by
  classical
  have Hfreq : ∃w0 : ℝ,0 < w0 ∧ ∃ᶠn in atTop,w0 ≤ W n := by
    by_contra Hnone
    apply H
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    have Hn : ¬(∃ᶠn in atTop,eps ≤ W n) := fun Hf=>Hnone ⟨eps,heps,Hf⟩
    have Hsmall : ∀ᶠn in atTop,W n < eps := by
      simpa only [Filter.Frequently,not_not,not_le] using Hn
    filter_upwards [Hsmall] with n hn
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (hW n)] using hn
  obtain ⟨w0,hw0,Hfreq⟩:=Hfreq
  obtain ⟨phi,hphi,Hphi⟩:=extraction_of_frequently_atTop Hfreq
  exact ⟨w0,hw0,phi,hphi,Hphi⟩

theorem eventually_actual_weak_history_test_point_strict_profile
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (hWupper : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1)
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∀ᶠn in atTop,cl*(M n).xs < (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs < cu*(M n).xs := by
  classical
  by_contra Hbad
  have Hfreq : ∃ᶠn in atTop,¬(cl*(M n).xs < (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs < cu*(M n).xs) := by
    simpa only [Filter.Frequently,not_not] using Hbad
  obtain ⟨theta,htheta,Htheta⟩:=extraction_of_frequently_atTop Hfreq
  let W:=fun n=>(M (theta n)).canonicalDirectTestBandScale
  by_cases HW : Tendsto W atTop (𝓝 0)
  · have Hgood:=eventually_actual_weak_history_test_point_strict_profile_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
      (fun n=>M (theta n)) (G.comp theta htheta) W (fun _=>rfl) HW
      hclmargin hcumargin (fun n=>hcompare (theta n))
    obtain ⟨n,hn⟩:=Hgood.exists
    exact Htheta n hn
  · obtain ⟨w0,hw0,psi,hpsi,Hpsi⟩:=
      exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero W
        (fun n=>(M (theta n)).canonical_direct_test_band_pos.le) HW
    have Hgood:=eventually_actual_weak_history_test_point_strict_profile_of_working_scale_lower
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (theta (psi n))) (hdim.comp (htheta.comp hpsi).tendsto_atTop)
      (fun n=>M (theta (psi n))) (G.comp (theta ∘ psi) (htheta.comp hpsi))
      (fun n=>W (psi n)) (fun _=>rfl) w0 hw0 (Eventually.of_forall Hpsi)
      ((htheta.comp hpsi).tendsto_atTop.eventually hWupper)
      hclmargin hcumargin (fun n=>hcompare (theta (psi n)))
    obtain ⟨n,hn⟩:=Hgood.exists
    exact Htheta (psi n) hn

theorem actual_weak_history_bad_test_strength_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (hWupper : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1)
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (Hbad : ∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) :
    Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop (𝓝 0) := by
  classical
  let f:=fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2
  have hf : ∀n,0 ≤ f n:=fun n=>div_nonneg
    (laplaceComparisonStrength_pos (M n).context.d (M n).hlam (M n).xs).le (sq_nonneg _)
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
        laplaceComparisonStrength (M (theta n)).context.d (M (theta n)).lam (M (theta n)).xs := by
      intro n
      have H1:=(le_div_iff₀ (sq_pos_of_pos (M (theta n)).hxs)).mp (Htheta n)
      have H2:=mul_le_mul_of_nonneg_left H1 (sq_nonneg Ccal)
      have H3:=mul_le_mul_of_nonneg_right hCsq (sq_nonneg (M (theta n)).xs)
      nlinarith only [H2,H3]
    have Hgood:=eventually_actual_weak_history_test_point_strict_profile
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
      (fun n=>M (theta n)) (G.comp theta htheta)
      (htheta.tendsto_atTop.eventually hWupper) hclmargin hcumargin Hcompare
    obtain ⟨n,hn⟩:=(Hgood.and (htheta.tendsto_atTop.eventually Hbad)).exists
    exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩
  change Tendsto f atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  filter_upwards [Hsmall eta heta] with n hn
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (hf n)] using hn

end OAI.SKFluctuations.LaplaceWindowFormalization

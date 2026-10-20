module

public import ComparisonActualHighOnlyFullThermalMacroscopicDirectProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity ActualHighOnlyOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 24000000
theorem high_only_exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero
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

theorem eventually_actual_high_only_comparable_test_point_strict_profile_of_full_thermal_working_scale_lower
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2) atTop (𝓝 0))
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
  have hlarge := actual_comparable_context_strength_ratio_atTop_of_working_scale_lower_high_only M G hw0 hlo
  by_contra Hbad
  have Hfreq : ∃ᶠn in atTop,¬(cl*(M n).xs < (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs < cu*(M n).xs) := by
    simpa only [Filter.Frequently,not_not] using Hbad
  obtain ⟨theta,htheta,Htheta⟩:=extraction_of_frequently_atTop Hfreq
  obtain ⟨phi,hphi,htotal,d,HU,HV,hklo,hkup⟩:=
    exists_actual_selected_bad_history_high_linear_profile_along_comparable_macro_high_only_of_full_thermal
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
      (fun n=>M (theta n)) (G.comp theta htheta) (Hfull.comp htheta.tendsto_atTop) (fun n=>W (theta n))
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

theorem actual_high_only_comparable_bad_test_working_scale_tendsto_zero_of_full_thermal
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (hWupper : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1)
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hbad : ∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) :
    Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0) := by
  classical
  by_contra Hnone
  obtain ⟨w0,hw0,phi,hphi,Hphi⟩ :=
    high_only_exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero
      (fun n=>(M n).canonicalDirectTestBandScale)
      (fun n=>(M n).canonical_direct_test_band_pos.le) Hnone
  have Hgood := eventually_actual_high_only_comparable_test_point_strict_profile_of_full_thermal_working_scale_lower
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp phi hphi) (Hfull.comp hphi.tendsto_atTop)
    (fun n=>(M (phi n)).canonicalDirectTestBandScale) (fun _=>rfl)
    w0 hw0 (Eventually.of_forall Hphi) (hphi.tendsto_atTop.eventually hWupper)
    hclmargin hcumargin (fun n=>hcompare (phi n))
  obtain ⟨n,hn⟩ := (Hgood.and (hphi.tendsto_atTop.eventually Hbad)).exists
  exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

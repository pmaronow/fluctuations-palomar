module

public import SKProof.Port.ComparisonActualOriginalQCavityClockMacroscopicThermal
public import SKProof.Port.ComparisonActualOriginalQFullThermalMacroscopicStrictTest
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000
set_option linter.unusedVariables false
theorem exists_actual_selected_bad_history_complete_direct_profile_along_comparable_macro_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∃phi : ℕ → ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualOriginalQLocalScalarLimitData
          (G.hT) T
          (fun n => M (phi n)) htotal,
          let hT := G.hT
          let kappa := (T/T)*scalarInitialDensityConstant hT d.beta
          (∀t > 0,d.U.mass t=kappa*t) ∧ (∀t > 0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu ∧
            2*T*Real.exp (-12*T) ≤ kappa ∧
            kappa ≤ T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) ∧
            TendstoLocallyUniformlyOn
              (fun n v=>(M (phi n)).sweepRadius ((M (phi n)).xs*v)/(M (phi n)).xs)
              (fun v=>v/kappa) atTop (Ioi (0:ℝ)) ∧ d.sigma=0 ∧
            (∀t ≥ 0,comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma t=0) ∧
            (∀t ≥ 0,comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma t=0) ∧
            ∀R : ℝ,0 < R →
              TendstoUniformlyOn (fun n => comparisonLocalScalarSlope hT T
                ((M (phi n)).inheritedScalarMassProfileBare hT (htotal n)) (M (phi n)).xs)
                (fun _ => 0) atTop (Icc (0 : ℝ) R) ∧
              TendstoUniformlyOn (fun n => comparisonRescaledScalarResponse
                (scalarCovarianceResponse hT ((M (phi n)).inheritedScalarMassProfileBare hT (htotal n)))
                T (M (phi n)).xs) (fun _ => 0) atTop (Icc (0 : ℝ) R) := by
  have Hlo : ∀ᶠn in atTop,w0≤(M n).directTestWorkingScale:=by
    simpa only [hcanonical] using hWlower
  have Hup : ∀ᶠn in atTop,(M n).directTestWorkingScale≤1:=by
    simpa only [hcanonical] using hWupper
  have Hfull:=actual_comparable_context_full_thermal_density_tendsto_zero_of_working_scale_lower_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hw0 dim hdim M G
    (Eventually.of_forall hcompare) Hlo Hup
  exact exists_actual_selected_bad_history_complete_direct_profile_along_comparable_macro_of_full_thermal_original_q hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper
    hcompare

theorem eventually_actual_comparable_test_point_strict_profile_of_working_scale_lower_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∀ᶠn in atTop,cl*(M n).xs < (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs < cu*(M n).xs := by
  have Hlo : ∀ᶠn in atTop,w0≤(M n).directTestWorkingScale:=by
    simpa only [hcanonical] using hWlower
  have Hup : ∀ᶠn in atTop,(M n).directTestWorkingScale≤1:=by
    simpa only [hcanonical] using hWupper
  have Hfull:=actual_comparable_context_full_thermal_density_tendsto_zero_of_working_scale_lower_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hw0 dim hdim M G
    (Eventually.of_forall hcompare) Hlo Hup
  exact eventually_actual_comparable_test_point_strict_profile_of_full_thermal_working_scale_lower_original_q hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper
    hclmargin hcumargin hcompare

theorem actual_comparable_bad_test_working_scale_tendsto_zero_original_q
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
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Hbad : ∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) :
    Tendsto (fun n=>(M n).directTestWorkingScale) atTop (𝓝 0) := by
  classical
  by_contra Hnone
  obtain ⟨w0,hw0,phi,hphi,Hphi⟩ :=
    exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero_original_q
      (fun n=>(M n).directTestWorkingScale)
      (fun n=>(M n).canonical_direct_test_band_pos.le) Hnone
  have Hgood := eventually_actual_comparable_test_point_strict_profile_of_working_scale_lower_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp_original_q phi hphi)
    (fun n=>(M (phi n)).directTestWorkingScale) (fun _=>rfl)
    w0 hw0 (Eventually.of_forall Hphi) (hphi.tendsto_atTop.eventually hWupper)
    hclmargin hcumargin (fun n=>hcompare (phi n))
  obtain ⟨n,hn⟩ := (Hgood.and (hphi.tendsto_atTop.eventually Hbad)).exists
  exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

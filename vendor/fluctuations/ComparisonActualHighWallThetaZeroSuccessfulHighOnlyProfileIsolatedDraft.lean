module

public import ComparisonActualHighWallThetaZeroSuccessfulHighOnlyContextIsolatedDraft
public import ComparisonActualHighOnlyCompleteComparableProfile
public import ComparisonNativeActualChildDirectCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum

theorem theta_zero_successful_high_only_child_linear_profile_from_context
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hCt : 0 ≤ Ct) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (G : ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext Q T)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (hQxs : ∀n,(Q n).xs=x n)
    (hQd : ∀n,(Q n).context.d=c0*x n)
    (hQlam : ∀n,(Q n).lam=(c0*x n)^2) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧ ∃kappa : ℝ,
      2*T*Real.exp (-12*T) ≤ kappa ∧
      kappa ≤ T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
        (2*Real.exp (-12*T)) ∧
      TendstoLocallyUniformlyOn
        (fun n v=>(Q (phi n)).R (x (phi n)*v)/x (phi n))
        (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
  let Ccal := max 1 (1/c0^3)
  have hCcal : 1 ≤ Ccal := le_max_left _ _
  have Hcompare : ∀n,(Q n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (Q n).context.d (Q n).lam (Q n).xs := by
    intro n
    rw [hQxs,hQd,hQlam]
    exact (actual_child_direct_calibration_at_parent_test (delta:=delta)
      (d:=(Q n).context.d) (by omega : 0<dim n+1)
      hc0 hc01 (Q n).hlam (hx n)).2.2
  have HD : Tendsto (fun n=>(Q n).context.d) atTop (𝓝 0) := by
    simpa only [hQd,mul_zero,Function.comp_def] using hxlim.const_mul c0
  have HW : Tendsto (fun n=>(Q n).canonicalDirectTestBandScale)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(Q n).canonical_direct_test_band_pos.le)
      (fun n=>((Q n).canonical_direct_test_band_geometry (sq_nonneg Ccal)
        (Hcompare n)).1)
    simpa only [mul_zero] using HD.const_mul (Ccal^2+1)
  obtain ⟨phi,hphi,htotal,d,HU,HV,hklo,hkup,Hklo,Hkup,Hinv,Hrest⟩ :=
    exists_actual_high_only_comparable_complete_direct_profile
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim Q G
      (HW.eventually (eventually_le_nhds zero_lt_one)) Hcompare
  let kappa := (T/T)*scalarInitialDensityConstant G.hT d.beta
  exact ⟨phi,hphi,kappa,Hklo,Hkup,by simpa only [hQxs] using Hinv⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

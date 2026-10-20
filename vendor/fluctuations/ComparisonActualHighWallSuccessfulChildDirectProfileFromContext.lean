module

public import ComparisonActualHighOnlyCompleteComparableProfile
public import ComparisonNativeActualChildDirectCalibration
public import ComparisonActualHighWallLocalAllMassChildTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 22000000
namespace ActualHighWallOverlapMinimum

private theorem fixed_wall_successful_child_linear_profile
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (Q : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (G : ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext Q T)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hQxs : ∀ n, (Q n).xs = x n)
    (hQd : ∀ n, (Q n).context.d = c0*x n)
    (hQlam : ∀ n, (Q n).lam = (c0*x n)^2) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ kappa : ℝ,
      2*T*Real.exp (-12*T) ≤ kappa ∧
      kappa ≤ T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) ∧
      TendstoLocallyUniformlyOn
        (fun n v => (Q (phi n)).R (x (phi n)*v)/x (phi n))
        (fun v => v/kappa) atTop (Ioi (0:ℝ)) := by
  let Ccal := max 1 (1/c0^3)
  have hCcal : 1 ≤ Ccal := le_max_left _ _
  have Hcompare : ∀ n, (Q n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (Q n).context.d (Q n).lam (Q n).xs := by
    intro n
    rw [hQxs, hQd, hQlam]
    exact (actual_child_direct_calibration_at_parent_test (delta := delta)
      (d := (Q n).context.d) (Q n).context.hn hc0 hc01 (Q n).hlam (hx n)).2.2
  have HD : Tendsto (fun n => (Q n).context.d) atTop (𝓝 0) := by
    simpa only [hQd, mul_zero, Function.comp_def] using hxlim.const_mul c0
  have HW : Tendsto (fun n => (Q n).canonicalDirectTestBandScale) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (Q n).canonical_direct_test_band_pos.le)
      (fun n => ((Q n).canonical_direct_test_band_geometry (sq_nonneg Ccal)
        (Hcompare n)).1)
    simpa only [mul_zero] using HD.const_mul (Ccal^2+1)
  obtain ⟨phi, hphi, htotal, d, HU, HV, hklo, hkup, Hklo, Hkup, Hinv, Hrest⟩ :=
    exists_actual_high_only_comparable_complete_direct_profile
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim Q G
      (HW.eventually (eventually_le_nhds zero_lt_one)) Hcompare
  let kappa := (T/T)*scalarInitialDensityConstant G.hT d.beta
  exact ⟨phi, hphi, kappa, Hklo, Hkup, by simpa only [hQxs] using Hinv⟩

theorem successful_high_only_child_parent_direct_profile_from_context
    {m delta cl cu Az C0 Ct D Bclock T c0 C CtChild DChild BclockChild : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hC : 1 ≤ C) (hCtChild : 0 ≤ CtChild)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ) → ActualShiftedParentChildCall (dim n+1) delta)
    (Q : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta
      (cl/4) (4*cu) (4*C/cl) C0 CtChild DChild BclockChild)
    (G : ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext Q T)
    (x : ℕ → ℝ) (hxs : ∀ n, (M n).xs ≤ x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀ n, (a n).context = (M n).data.shiftedParentData)
    (hR : ∀ n, (a n).R = (M n).data.wallRadius (M n).alpha)
    (hchild : ∀ᶠ n in atTop, (a n).childRadius = c0*x n ∧
      (a n).childLam = (c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (M n).data.d ((M n).data.d^2) (x n))
    (hweak : Tendsto (fun n => (M n).data.g (x n)/(x n)^2) atTop (𝓝 0))
    (hs : Tendsto (fun n => (M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n => (M n).data.rmin/x n) atTop (𝓝 0))
    (hQ : ∀ n, (Q n).R = (a n).Z ∧ (Q n).xs = x n ∧
      (Q n).context.d = c0*x n ∧ (Q n).lam = (c0*x n)^2) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ kappa : ℝ,
      2*T*Real.exp (-12*T) ≤ kappa ∧
      kappa ≤ T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
        (2*Real.exp (-12*T)) ∧
      TendstoLocallyUniformlyOn
        (fun n v => (M (phi n)).data.wallRadius (M (phi n)).alpha
          (x (phi n)*v)/x (phi n))
        (fun v => v/kappa) atTop (Ioi (0:ℝ)) ∧
      ∀ᶠ n in atTop, cl*x (phi n) < (M (phi n)).alpha.val.val (x (phi n)) ∧
        (M (phi n)).alpha.val.val (x (phi n)) < cu*x (phi n) := by
  have hcl' : 0 < cl/4 := by positivity
  have hcu' : 0 < 4*cu := by positivity
  have hAz' : 0 ≤ 4*C/cl := by positivity
  have hx (n : ℕ) : 0 < x n := (M n).hxs.trans_le (hxs n)
  obtain ⟨phi, hphi, kappa, hklo, hkup, HQ⟩ :=
    fixed_wall_successful_child_linear_profile
      hm hdelta hroom hcl' hcu' hAz' hC0 hCtChild hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim Q G x hx hxlim
      (fun n => (hQ n).2.1) (fun n => (hQ n).2.2.1)
      (fun n => (hQ n).2.2.2)
  have heq (n : ℕ) : (Q n).R = (a n).Z := (hQ n).1
  have HZ : TendstoLocallyUniformlyOn
      (fun n v => (a (phi n)).Z (x (phi n)*v)/x (phi n))
      (fun v => v/kappa) atTop (Ioi (0:ℝ)) := by
    simpa only [heq] using HQ
  have Hparent := successful_high_only_child_parent_profile_transfer
    hm hdelta hcl hAz hC0 hc0
    (fun n => dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n => M (phi n)) (fun n => a (phi n)) (fun n => x (phi n))
    (fun n => hxs (phi n)) (hxlim.comp hphi.tendsto_atTop)
    (fun n => hcontext (phi n)) (fun n => hR (phi n))
    (hphi.tendsto_atTop.eventually hchild)
    (hweak.comp hphi.tendsto_atTop) (hs.comp hphi.tendsto_atTop)
    (hr.comp hphi.tendsto_atTop) (hclmargin.trans_le hklo)
    (hkup.trans_lt hcumargin) HZ
  exact ⟨phi, hphi, kappa, hklo, hkup, Hparent.1, Hparent.2⟩

theorem successful_all_mass_child_parent_direct_profile_from_context
    {m delta cl cu Az C0 Ct D Bclock T c0 C CtChild DChild BclockChild : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hC : 1 ≤ C) (hCtChild : 0 ≤ CtChild)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ) → ActualShiftedAllMassParentChildCall (dim n+1) delta)
    (Q : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta
      (cl/4) (4*cu) (4*C/cl) C0 CtChild DChild BclockChild)
    (G : ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext Q T)
    (x : ℕ → ℝ) (hxs : ∀ n, (M n).xs ≤ x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀ n, (a n).context = (M n).data.shiftedParentData)
    (hR : ∀ n, (a n).R = (M n).data.wallRadius (M n).alpha)
    (hchild : ∀ᶠ n in atTop, (a n).childRadius = c0*x n ∧
      (a n).childLam = (c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (M n).data.d ((M n).data.d^2) (x n))
    (hweak : Tendsto (fun n => (M n).data.g (x n)/(x n)^2) atTop (𝓝 0))
    (hs : Tendsto (fun n => (M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n => (M n).data.rmin/x n) atTop (𝓝 0))
    (hQ : ∀ n, (Q n).R = (a n).Z ∧ (Q n).xs = x n ∧
      (Q n).context.d = c0*x n ∧ (Q n).lam = (c0*x n)^2) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ kappa : ℝ,
      2*T*Real.exp (-12*T) ≤ kappa ∧
      kappa ≤ T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
        (2*Real.exp (-12*T)) ∧
      TendstoLocallyUniformlyOn
        (fun n v => (M (phi n)).data.wallRadius (M (phi n)).alpha
          (x (phi n)*v)/x (phi n))
        (fun v => v/kappa) atTop (Ioi (0:ℝ)) ∧
      ∀ᶠ n in atTop, cl*x (phi n) < (M (phi n)).alpha.val.val (x (phi n)) ∧
        (M (phi n)).alpha.val.val (x (phi n)) < cu*x (phi n) := by
  have hcl' : 0 < cl/4 := by positivity
  have hcu' : 0 < 4*cu := by positivity
  have hAz' : 0 ≤ 4*C/cl := by positivity
  have hx (n : ℕ) : 0 < x n := (M n).hxs.trans_le (hxs n)
  obtain ⟨phi, hphi, kappa, hklo, hkup, HQ⟩ :=
    fixed_wall_successful_child_linear_profile
      hm hdelta hroom hcl' hcu' hAz' hC0 hCtChild hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim Q G x hx hxlim
      (fun n => (hQ n).2.1) (fun n => (hQ n).2.2.1)
      (fun n => (hQ n).2.2.2)
  have heq (n : ℕ) : (Q n).R = (a n).Z := (hQ n).1
  have HZ : TendstoLocallyUniformlyOn
      (fun n v => (a (phi n)).Z (x (phi n)*v)/x (phi n))
      (fun v => v/kappa) atTop (Ioi (0:ℝ)) := by
    simpa only [heq] using HQ
  have Hparent := successful_all_mass_child_parent_profile_transfer
    hm hdelta hcl hAz hC0 hc0
    (fun n => dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n => M (phi n)) (fun n => a (phi n)) (fun n => x (phi n))
    (fun n => hxs (phi n)) (hxlim.comp hphi.tendsto_atTop)
    (fun n => hcontext (phi n)) (fun n => hR (phi n))
    (hphi.tendsto_atTop.eventually hchild)
    (hweak.comp hphi.tendsto_atTop) (hs.comp hphi.tendsto_atTop)
    (hr.comp hphi.tendsto_atTop) (hclmargin.trans_le hklo)
    (hkup.trans_lt hcumargin) HZ
  exact ⟨phi, hphi, kappa, hklo, hkup, Hparent.1, Hparent.2⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

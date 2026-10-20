module

public import ComparisonNativeActualRadiusStripGeometry
public import ComparisonNativeActualInheritedHistoryGeometry
public import ComparisonNativeActualSelectedBadHistoryReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}

theorem eventually_actual_shell_history_radius_strip_geometry
    (hcl : 0 < cl) (hcu : 0 ≤ cu) (hAz : 0 ≤ Az)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (ts : ℕ→List ComparisonHistoryTerm) (epsilon shell c C : ℝ)
    (hshell : 0 < shell) (hc : 0 < c)
    (hb : ∀ᶠn in atTop,∀u,(M n).b u=historyMatrixClock T epsilon shell (ts n) u)
    (hh : ∀ᶠn in atTop,∀u,(M n).h u=historyFieldClock (ts n) u) :
    ∀ᶠn in atTop,
      0 < (M n).actualRadiusStripLower c ∧
      (M n).actualRadiusStripLower c ≤ (M n).actualRadiusStripUpper c C ∧
      (M n).actualRadiusStripUpper c C ≤ 1 ∧
      (M n).xs ≤ (M n).actualRadiusStripUpper c C ∧
      (M n).actualRadiusStripUpper c C ≤ actualRadiusStripConstant cl Az c C*(M n).xs ∧
      (M n).alpha.val.val ((M n).actualRadiusStripLower c)=c*(M n).xs ∧
      (M n).alpha.val.val ((M n).actualRadiusStripUpper c C) < shell ∧
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun r=>(M n).b ((M n).alpha.val.val r))
          (Icc ((M n).actualRadiusStripLower c) ((M n).actualRadiusStripUpper c C)) ∧
        LipschitzOnWith Kh (fun r=>(M n).h ((M n).alpha.val.val r))
          (Icc ((M n).actualRadiusStripLower c) ((M n).actualRadiusStripUpper c C)) := by
  have hcsmall : ∀ᶠn in atTop,c*(M n).xs ≤ 1 := by
    have H : Tendsto (fun n=>c*(M n).xs) atTop (𝓝 0) := by
      simpa only [mul_zero] using hxs.const_mul c
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have hCsmall : ∀ᶠn in atTop,actualRadiusStripConstant cl Az c C*(M n).xs ≤ 1 := by
    have H : Tendsto (fun n=>actualRadiusStripConstant cl Az c C*(M n).xs) atTop (𝓝 0) := by
      simpa only [mul_zero] using hxs.const_mul (actualRadiusStripConstant cl Az c C)
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have hmasssmall : ∀ᶠn in atTop,cu*(actualRadiusStripConstant cl Az c C+Az)*(M n).xs < shell := by
    have H : Tendsto (fun n=>cu*(actualRadiusStripConstant cl Az c C+Az)*(M n).xs) atTop (𝓝 0) := by
      simpa only [mul_zero] using hxs.const_mul (cu*(actualRadiusStripConstant cl Az c C+Az))
    exact H.eventually (gt_mem_nhds hshell)
  filter_upwards [hcsmall,hCsmall,hmasssmall,hb,hh] with n hnc hnC hnm hnb hnh
  obtain ⟨ha,haz,hz,hxz,hzC,hmass,_hstrip⟩ :=
    (M n).actual_radius_strip_geometry hcl hAz hc hnc hnC
  have hbranch := ((M n).actual_radius_strip_upper_mass_le hcu hAz hz hzC).trans_lt hnm
  exact ⟨ha,haz,hz,hxz,hzC,hmass,hbranch,
    (M n).inherited_shell_history_clock_lipschitz (ts n) T epsilon shell
      ((M n).actualRadiusStripLower c) ((M n).actualRadiusStripUpper c C)
      hnb hnh ha.le haz hz (Or.inl hbranch)⟩

theorem ActualSelectedBadHistoryChain.eventually_radius_strip_geometry
    (hcl : 0 < cl) (hcu : 0 ≤ cu) (hAz : 0 ≤ Az)
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (epsilon shell c C : ℝ) (hshell : 0 < shell) (hc : 0 < c)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ∀ᶠn in atTop,
      0 < (M n).actualRadiusStripLower c ∧
      (M n).actualRadiusStripLower c ≤ (M n).actualRadiusStripUpper c C ∧
      (M n).actualRadiusStripUpper c C ≤ 1 ∧
      (M n).xs ≤ (M n).actualRadiusStripUpper c C ∧
      (M n).actualRadiusStripUpper c C ≤ actualRadiusStripConstant cl Az c C*(M n).xs ∧
      (M n).alpha.val.val ((M n).actualRadiusStripLower c)=c*(M n).xs ∧
      (M n).alpha.val.val ((M n).actualRadiusStripUpper c C) < shell ∧
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun r=>(M n).b ((M n).alpha.val.val r))
          (Icc ((M n).actualRadiusStripLower c) ((M n).actualRadiusStripUpper c C)) ∧
        LipschitzOnWith Kh (fun r=>(M n).h ((M n).alpha.val.val r))
          (Icc ((M n).actualRadiusStripLower c) ((M n).actualRadiusStripUpper c C)) := by
  obtain ⟨ps,hps⟩ := Hhistory.literal_readout epsilon shell hb hh
  exact eventually_actual_shell_history_radius_strip_geometry hcl hcu hAz M hxs
    (fun n=>(ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) epsilon shell c C hshell hc
    (hps.mono (fun _ hn=>hn.2.1)) (hps.mono (fun _ hn=>hn.2.2))

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

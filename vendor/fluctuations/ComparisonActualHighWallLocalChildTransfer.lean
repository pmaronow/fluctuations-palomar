module

public import ComparisonActualShiftedAbsoluteDisagreementMass
public import ComparisonActualHighWallShiftedParentData
public import ComparisonActualHighWallPairedFarGeometry
public import ComparisonNativeOuterAbsoluteDisagreementMass
public import SelectivePropagationIntegration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

theorem successful_high_only_child_working_scale_agreement
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ) → ActualShiftedParentChildCall (dim n+1) delta)
    (x : ℕ → ℝ) (hxs : ∀ n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀ n,(a n).context = (M n).data.shiftedParentData)
    (hR : ∀ n,(a n).R = (M n).data.wallRadius (M n).alpha)
    (hchild : ∀ᶠ n in atTop,(a n).childRadius = c0*x n ∧ (a n).childLam = (c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1 : ℕ) : ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).data.d ((M n).data.d^2) (x n))
    (hweak : Tendsto (fun n => (M n).data.g (x n)/(x n)^2) atTop (𝓝 0))
    (hs : Tendsto (fun n => (M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n => (M n).data.rmin/x n) atTop (𝓝 0)) :
    ∀ left right eps theta : ℝ,0 < left → left < right → 0 < eps → 0 < theta →
      ∀ᶠ n in atTop,volume (physicalPropagationDisagreementMassSet
        ((M n).data.wallRadius (M n).alpha) (a n).Z
        (x n*left) (x n*right) (eps*x n)) < ENNReal.ofReal (theta*x n) := by
  intro left right eps theta hleft hlr heps htheta
  have hright : 0 < right := hleft.trans hlr
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  let step := eps/3
  let C := (Az+1/cl)*(1+right)
  have hstep : 0 < step := by dsimp [step];positivity
  have hC : 0 < C := by dsimp [C];positivity
  obtain ⟨J,hJ⟩ := exists_nat_gt (C/step)
  have hCJ : C ≤ (J : ℝ)*step := ((div_lt_iff₀ hstep).mp hJ).le
  let ell := theta/(4*((J : ℝ)+1))
  have hell : 0 < ell := by dsimp [ell];positivity
  obtain ⟨eta,heta,heta1,Hmass⟩ := eventually_actual_shifted_absolute_disagreement_mass_le
    (Dbound := D) (eps := step) (ell := ell) J hdelta
    (show 0 < 1/C0 by positivity) hm hc0 hstep hell
  have Hweak := hweak.eventually (gt_mem_nhds (pow_pos heta 3))
  have Hs := hs.eventually (eventually_le_nhds hleft)
  have Hr := hr.eventually (eventually_le_nhds
    (show 0 < step/(4*((J : ℝ)+2)) by positivity))
  have Hunit := hxlim.eventually (eventually_le_nhds zero_lt_one)
  have Hright : Tendsto (fun n => x n*right) atTop (𝓝 0) := by simpa using hxlim.mul_const right
  have Hdim : Tendsto (fun n => dim n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hdim
  filter_upwards [Hdim.eventually Hmass,Hweak,Hs,Hr,Hunit,hchild,
    Hright.eventually (eventually_le_nhds zero_lt_one)] with n hn hw hsn hrn hxn hc hyr
  have hlo : (1/C0)*((dim n+1 : ℕ) : ℝ)^(-(2 : ℝ)/3+m)*(a n).context.d ≤ (a n).context.E := by
    rw [hcontext n]
    have H := mul_le_mul_of_nonneg_left (M n).hlower (show 0 ≤ 1/C0 by positivity)
    simpa only [ActualHighWallData.shiftedParentData,ActualShiftedParentData.d,ActualShiftedParentData.E,
      ←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using H
  have hdD : (a n).context.d ≤ D := by rw [hcontext n];exact (M n).hdD
  have hupp : Real.sqrt ((dim n+1 : ℕ) : ℝ)*(a n).context.E ≤ (a n).context.d^2 := by
    rw [hcontext n];exact (M n).hupper
  have hax : comparisonLowerScale ((dim n+1 : ℕ) : ℝ) (a n).context.E (a n).context.d ≤ x n := by
    rw [hcontext n];exact (M n).hscale.trans (hxs n)
  have hwe : (a n).e (x n) ≤ eta^3*(x n)^2 := by
    change laplaceComparisonStrength (a n).context.d (a n).context.lam (x n) ≤ _
    rw [hcontext n]
    exact (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hw.le
  have herr : (a n).err ≤ ((dim n+1 : ℕ) : ℝ)^(20*delta)*
      actualChildErrorBudget (dim n+1) delta c0 (a n).context.d (a n).lam (x n) := by
    change (a n).err ≤ _*actualChildErrorBudget _ _ _ _ (a n).context.lam _
    rw [hcontext n]
    exact hc.2.2
  have horigin : (a n).context.r0 ≤ (step*x n)/(4*((J : ℝ)+2)) := by
    rw [hcontext n]
    change (M n).data.rmin ≤ _
    have H := (div_le_iff₀ (hx n)).mp hrn
    exact H.trans_eq (by ring)
  have ha : (a n).context.s ≤ x n*left := by
    rw [hcontext n]
    exact (div_le_iff₀ (hx n)).mp hsn |>.trans_eq (by ring)
  have hcap : ∀ u ∈ Icc (x n*left) (x n*right),(a n).R u ≤ (J : ℝ)*(step*x n) := by
    intro u hu
    have hui : u ∈ Icc (0 : ℝ) 1 := ⟨(mul_pos (hx n) hleft).le.trans hu.1,hu.2.trans hyr⟩
    rw [hR n]
    have H := (M n).inverse_radius_le_source_mass hcl hAz hui
    have Hxu : (M n).xs+u ≤ (1+right)*x n := by nlinarith only [hxs n,hu.2]
    have Hscale := mul_le_mul_of_nonneg_left Hxu (show 0 ≤ Az+1/cl by positivity)
    have HJ := mul_le_mul_of_nonneg_right hCJ (hx n).le
    dsimp only [C] at HJ
    nlinarith only [H,Hscale,HJ]
  have H := hn (a n) (x n) (x n*left) (x n*right) hdD hupp hlo
    ⟨hx n,hxn⟩ hax (a n).hld hwe hc.1 hc.2.1 herr horigin ha hyr hcap
  have Hsub : physicalPropagationDisagreementMassSet ((M n).data.wallRadius (M n).alpha) (a n).Z
      (x n*left) (x n*right) (eps*x n) ⊆
      {u | u ∈ Icc (x n*left) (x n*right) ∧ 3*(step*x n) ≤ |(a n).Z u-(a n).R u|} := by
    intro u hu
    refine ⟨hu.1,?_⟩
    rw [hR n]
    dsimp only [step]
    nlinarith only [hu.2.le]
  exact ((measure_mono Hsub).trans H).trans_lt
    (native_disagreement_measure_coefficient_lt J htheta (hx n))

theorem eventually_inverse_test_strict_of_linear_wall_radius_profile
    {dim : ℕ → ℕ}
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (hx : ∀ n,0 < x n) (hxlim : Tendsto x atTop (𝓝 0))
    (horigin : ∀ᶠ n in atTop,(M n).data.rmin ≤ x n)
    {kappa : ℝ} (hcl : 0 < cl) (hclmargin : cl < kappa) (hcumargin : kappa < cu)
    (hprofile : TendstoLocallyUniformlyOn
      (fun n v => (M n).data.wallRadius (M n).alpha (x n*v)/x n)
      (fun v => v/kappa) atTop (Ioi (0 : ℝ))) :
    ∀ᶠ n in atTop,cl*x n < (M n).alpha.val.val (x n) ∧
      (M n).alpha.val.val (x n) < cu*x n := by
  have hkappa : 0 < kappa := hcl.trans hclmargin
  have hcu : 0 < cu := hkappa.trans hcumargin
  have Hlo := (hprofile.tendsto_at hcl).eventually
    (gt_mem_nhds (show cl/kappa < 1 from (div_lt_one₀ hkappa).mpr hclmargin))
  have Hup := (hprofile.tendsto_at hcu).eventually
    (lt_mem_nhds (show 1 < cu/kappa from (one_lt_div₀ hkappa).mpr hcumargin))
  filter_upwards [Hlo,Hup,horigin,hxlim.eventually (eventually_le_nhds zero_lt_one)]
    with n hnlo hnup hnorigin hnx
  have Hradlo : (M n).data.wallRadius (M n).alpha (x n*cl) < x n := by
    simpa only [one_mul] using (div_lt_iff₀ (hx n)).mp hnlo
  have Hradup : x n < (M n).data.wallRadius (M n).alpha (x n*cu) := by
    simpa only [one_mul] using (lt_div_iff₀ (hx n)).mp hnup
  have Hinv := (M n).data.wallRadius_inverse (M n).alpha ⟨hnorigin,hnx⟩
  constructor
  · by_contra H
    have Hmono := (M n).data.wallRadius_monotone (M n).alpha
      (show (M n).alpha.val.val (x n) ≤ x n*cl by simpa only [mul_comm] using not_lt.mp H)
    rw [Hinv] at Hmono
    exact not_lt_of_ge Hmono Hradlo
  · by_contra H
    have Hmono := (M n).data.wallRadius_monotone (M n).alpha
      (show x n*cu ≤ (M n).alpha.val.val (x n) by simpa only [mul_comm] using not_lt.mp H)
    rw [Hinv] at Hmono
    exact not_lt_of_ge Hmono Hradup

theorem successful_high_only_child_parent_profile_transfer
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ) → ActualShiftedParentChildCall (dim n+1) delta)
    (x : ℕ → ℝ) (hxs : ∀ n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀ n,(a n).context = (M n).data.shiftedParentData)
    (hR : ∀ n,(a n).R = (M n).data.wallRadius (M n).alpha)
    (hchild : ∀ᶠ n in atTop,(a n).childRadius = c0*x n ∧ (a n).childLam = (c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1 : ℕ) : ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).data.d ((M n).data.d^2) (x n))
    (hweak : Tendsto (fun n => (M n).data.g (x n)/(x n)^2) atTop (𝓝 0))
    (hs : Tendsto (fun n => (M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n => (M n).data.rmin/x n) atTop (𝓝 0))
    {kappa : ℝ} (hclmargin : cl < kappa) (hcumargin : kappa < cu)
    (hprofile : TendstoLocallyUniformlyOn (fun n v => (a n).Z (x n*v)/x n)
      (fun v => v/kappa) atTop (Ioi (0 : ℝ))) :
    TendstoLocallyUniformlyOn
      (fun n v => (M n).data.wallRadius (M n).alpha (x n*v)/x n)
      (fun v => v/kappa) atTop (Ioi (0 : ℝ)) ∧
      ∀ᶠ n in atTop,cl*x n < (M n).alpha.val.val (x n) ∧
        (M n).alpha.val.val (x n) < cu*x n := by
  have hkappa : 0 < kappa := hcl.trans hclmargin
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have Hagree := successful_high_only_child_working_scale_agreement hm hdelta hcl hAz hC0 hc0
    dim hdim M a x hxs hxlim hcontext hR hchild hweak hs hr
  have Hparent := selective_propagation_transfer_working_child_locally_uniform
    (fun n => (M n).data.wallRadius (M n).alpha) (fun n => (a n).Z) x (inv_pos.mpr hkappa)
    hx hxlim (fun n => ((M n).data.wallRadius_monotone (M n).alpha).monotoneOn _)
    (fun n => (a n).child_radius_monotone.monotoneOn _)
    (fun v hv => by simpa only [div_eq_mul_inv,mul_comm] using hprofile.tendsto_at hv) Hagree
  have Hparent' : TendstoLocallyUniformlyOn
      (fun n v => (M n).data.wallRadius (M n).alpha (x n*v)/x n)
      (fun v => v/kappa) atTop (Ioi (0 : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_comm] using Hparent
  have Horigin : ∀ᶠ n in atTop,(M n).data.rmin ≤ x n := by
    filter_upwards [hr.eventually (eventually_le_nhds zero_lt_one)] with n hn
    simpa only [one_mul] using (div_le_iff₀ (hx n)).mp hn
  exact ⟨Hparent',eventually_inverse_test_strict_of_linear_wall_radius_profile
    M x hx hxlim Horigin hcl hclmargin hcumargin Hparent'⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

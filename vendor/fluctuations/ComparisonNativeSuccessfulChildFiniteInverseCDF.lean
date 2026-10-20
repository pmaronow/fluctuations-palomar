module

public import ComparisonNativeActualBadScaleMassTransfer
public import ComparisonNativeActualOuterChildRadiusBounds
public import SelectivePropagationIntegration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem comparison_native_inverse_outer_regular_of_quantile_bounds
    {c : ℝ} {k cap : ℝ→ℝ} (hc : 0 < c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn cap (Icc (0:ℝ) 1)) (hcap : 0 ≤ cap 1)
    (alpha : inverseIntegralConstraints 0 0 k cap)
    {lo up cutoff : ℝ} (hlo : 0 < lo) (hlo1 : lo ≤ 1)
    (hloup : lo ≤ up) (hcutoff : 0 ≤ cutoff)
    (hq : ∀u∈Icc cutoff 1,
      u/up ≤ comparisonSweepQuantile hc hk hkc hm hcap alpha u ∧
      comparisonSweepQuantile hc hk hkc hm hcap alpha u ≤ u/lo) :
    ∀r∈Icc (cutoff/lo) 1,lo*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ up*r := by
  have hup : 0 < up := hlo.trans_le hloup
  intro r hr
  have hr0 : 0 ≤ r := (div_nonneg hcutoff hlo.le).trans hr.1
  have hlowcut : cutoff ≤ lo*r := by
    have H := (div_le_iff₀ hlo).mp hr.1
    simpa only [mul_comm] using H
  have hlow1 : lo*r ≤ 1 :=
    (mul_le_mul_of_nonneg_right hlo1 hr0).trans (by simpa using hr.2)
  have hlowspec := comparisonSweepQuantile_spec hc hk hkc hm hcap alpha
    (show lo*r∈Icc (0:ℝ) 1 from ⟨mul_nonneg hlo.le hr0,hlow1⟩)
  have hlowrad : comparisonSweepQuantile hc hk hkc hm hcap alpha (lo*r) ≤ r := by
    simpa only [mul_div_cancel_left₀ _ hlo.ne'] using (hq (lo*r) ⟨hlowcut,hlow1⟩).2
  have hlow := alpha.val.property.2 hlowrad
  rw [hlowspec] at hlow
  refine ⟨hlow,?_⟩
  by_cases hhigh1 : up*r ≤ 1
  · have hhighcut : cutoff ≤ up*r :=
      hlowcut.trans (mul_le_mul_of_nonneg_right hloup hr0)
    have hhighspec := comparisonSweepQuantile_spec hc hk hkc hm hcap alpha
      (show up*r∈Icc (0:ℝ) 1 from ⟨mul_nonneg hup.le hr0,hhigh1⟩)
    have hhighrad : r ≤ comparisonSweepQuantile hc hk hkc hm hcap alpha (up*r) := by
      simpa only [mul_div_cancel_left₀ _ hup.ne'] using (hq (up*r) ⟨hhighcut,hhigh1⟩).1
    have hhigh := alpha.val.property.2 hhighrad
    rw [hhighspec] at hhigh
    exact hhigh
  · exact (alpha.val.property.1 r).2.trans (le_of_not_ge hhigh1)

theorem comparison_native_successful_child_inverse_outer_regular
    {c : ℝ} {k cap : ℝ→ℝ} (hc : 0 < c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn cap (Icc (0:ℝ) 1)) (hcap : 0 ≤ cap 1)
    (alpha : inverseIntegralConstraints 0 0 k cap)
    {cl cu C x : ℝ} (hcl : 0 < cl) (hcu : 0 < cu)
    (hcl1 : cl ≤ 1) (hclcu : cl ≤ cu) (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hq : ∀u∈Icc (C*x) 1,
      u/(4*cu) ≤ comparisonSweepQuantile hc hk hkc hm hcap alpha u ∧
      comparisonSweepQuantile hc hk hkc hm hcap alpha u ≤ 4*u/cl) :
    ∀r∈Icc ((4*C/cl)*x) 1,
      (cl/4)*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ (4*cu)*r := by
  have H := comparison_native_inverse_outer_regular_of_quantile_bounds hc hk hkc hm hcap
    alpha (show 0 < cl/4 by positivity) (show cl/4 ≤ 1 by linarith)
    (show cl/4 ≤ 4*cu by linarith) (mul_nonneg hC hx) (fun u hu=>by
      have he : u/(cl/4)=4*u/cl := by field_simp
      simpa only [he] using hq u hu)
  have he : (C*x)/(cl/4)=(4*C/cl)*x := by field_simp
  simpa only [he] using H

namespace NativeOverlapContext
variable {n : ℕ} {delta : ℝ}

theorem original_inverse_test_strict_of_radius_bracket
    (c : NativeOverlapContext n delta) (alpha : c.Profile)
    {x lower upper : ℝ} (hx : x∈Icc (0:ℝ) 1)
    (hlower : lower∈Icc (0:ℝ) 1) (hupper : upper∈Icc (0:ℝ) 1)
    (hlo : c.R alpha lower < x) (hup : x < c.R alpha upper) :
    lower < alpha.val.val x ∧ alpha.val.val x < upper := by
  constructor
  · by_contra H
    exact (not_le_of_gt hlo) ((c.profile_le_mass_iff_radius_le alpha hx hlower).mp
      (not_lt.mp H))
  · by_contra H
    exact (not_le_of_gt hup) ((c.mass_le_profile_iff_radius_le alpha hx hupper).mp
      (not_lt.mp H))

end NativeOverlapContext

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_original_inverse_test_strict_of_linear_radius_profile
    {N : ℕ→ℕ}
    (M : (n : ℕ)→NativeOverlapMinimum (N n) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxlim : Tendsto x atTop (𝓝 0))
    {kappa : ℝ} (hcl : 0 < cl) (hclmargin : cl < kappa) (hcumargin : kappa < cu)
    (hprofile : TendstoLocallyUniformlyOn (fun n v=>(M n).R (x n*v)/x n)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ))) :
    ∀ᶠn in atTop,cl*x n < (M n).alpha.val.val (x n) ∧
      (M n).alpha.val.val (x n) < cu*x n := by
  have hkappa : 0 < kappa := hcl.trans hclmargin
  have hcu : 0 < cu := hkappa.trans hcumargin
  have Hlo := (hprofile.tendsto_at hcl).eventually
    (gt_mem_nhds (show cl/kappa < 1 from (div_lt_one₀ hkappa).mpr hclmargin))
  have Hup := (hprofile.tendsto_at hcu).eventually
    (lt_mem_nhds (show 1 < cu/kappa from (one_lt_div₀ hkappa).mpr hcumargin))
  have Hx := hxlim.eventually (gt_mem_nhds zero_lt_one)
  have Hcllim : Tendsto (fun n=>x n*cl) atTop (𝓝 0) := by
    simpa using hxlim.mul_const cl
  have Hculim : Tendsto (fun n=>x n*cu) atTop (𝓝 0) := by
    simpa using hxlim.mul_const cu
  filter_upwards [Hlo,Hup,Hx,Hcllim.eventually (gt_mem_nhds zero_lt_one),
    Hculim.eventually (gt_mem_nhds zero_lt_one)] with n hnlo hnup hnx hncl hncu
  have Hradlo : (M n).R (x n*cl) < x n := by
    simpa only [one_mul] using (div_lt_iff₀ (hx n)).mp hnlo
  have Hradup : x n < (M n).R (x n*cu) := by
    simpa only [one_mul] using (lt_div_iff₀ (hx n)).mp hnup
  have H := (M n).context.original_inverse_test_strict_of_radius_bracket (M n).alpha
    ⟨(hx n).le,hnx.le⟩ ⟨mul_nonneg (hx n).le hcl.le,hncl.le⟩
    ⟨mul_nonneg (hx n).le hcu.le,hncu.le⟩ Hradlo Hradup
  simpa only [mul_comm] using H

theorem actual_minimum_successful_child_parent_profile_transfer
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (N n) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→NativeChildBarrierCall (N n) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hparent : ∀n,(a n).context.E=(M n).context.E ∧
      (a n).context.d=(M n).context.d ∧ (a n).lam=(M n).lam ∧ (a n).R=(M n).R)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ (N n:ℝ)^(20*delta)*
        actualChildErrorBudget (N n) delta c0 (M n).context.d (M n).lam (x n))
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    {kappa : ℝ} (hclmargin : cl < kappa) (hcumargin : kappa < cu)
    (hprofile : TendstoLocallyUniformlyOn (fun n v=>(a n).Z (x n*v)/x n)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ))) :
    TendstoLocallyUniformlyOn (fun n v=>(M n).R (x n*v)/x n)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) ∧
      ∀ᶠn in atTop,cl*x n < (M n).alpha.val.val (x n) ∧
        (M n).alpha.val.val (x n) < cu*x n := by
  have hkappa : 0 < kappa := hcl.trans hclmargin
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have Hagree := actual_minimum_successful_child_two_scale_agreement hm hdelta hcl hcu
    hAz hC0 hc0 N hN M a x hxs hxlim hparent hchild hweak
  have Hband left right eps theta (hleft : 0 < left) (hlr : left < right)
      (heps : 0 < eps) (htheta : 0 < theta) :
      ∀ᶠn in atTop,volume (physicalPropagationDisagreementMassSet (M n).R (a n).Z
        (x n*left) (x n*right) (eps*x n)) < ENNReal.ofReal (theta*x n) := by
    have Hright : Tendsto (fun n=>x n*right) atTop (𝓝 0) := by
      simpa using hxlim.mul_const right
    filter_upwards [Hagree 1 left right eps theta zero_lt_one hleft hlr heps htheta,
      Hright.eventually (gt_mem_nhds zero_lt_one)] with n hn hnr
    exact hn (x n) (by simp) hnr.le
  have Hparent := selective_propagation_transfer_working_child_locally_uniform
    (fun n=>(M n).R) (fun n=>(a n).Z) x (inv_pos.mpr hkappa) hx hxlim
    (fun n=>(comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
    (fun n=>(a n).hZm) (fun v hv=>by
      simpa only [div_eq_mul_inv,mul_comm] using hprofile.tendsto_at hv) Hband
  have Hparent' : TendstoLocallyUniformlyOn (fun n v=>(M n).R (x n*v)/x n)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
    simpa only [div_eq_mul_inv,mul_comm] using Hparent
  exact ⟨Hparent',eventually_original_inverse_test_strict_of_linear_radius_profile
    M x hx hxlim hcl hclmargin hcumargin Hparent'⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

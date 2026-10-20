module

public import ComparisonNativeActualChildSequentialClocks
public import ComparisonNativeActualChildPositiveBandSequenceGeneral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {N : ℕ→ℕ}

theorem actual_selected_bad_child_sequential_clocks_of_call_bounded
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hN : Tendsto N atTop atTop)
    (P M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).context.N delta (P n).context.E (P n).lam ≤ x n)
    (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hd : ∀ᶠn in atTop,(M n).context.d=actualChildRadius c0 (x n))
    (hE : ∀ᶠn in atTop,(M n).context.E=actualChildErrorBudget (N n+1) delta c0 (P n).context.d (P n).lam (x n))
    (hb : ∀ᶠn in atTop,∀u,(M n).b u=(P n).b u-laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u))
    (hh : ∀ᶠn in atTop,∀u,(M n).h u=(P n).h u+laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u)
    (Hparent : NativeSequentialPositiveBandClocks P T) : NativeSequentialPositiveBandClocks M T := by
  have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
  have Hcut : ∀ᶠn in atTop,
      comparisonLowerScale (P n).context.N (P n).context.E (P n).context.d ≤
      comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d := by
    filter_upwards [hN.eventually (eventually_actual_parent_cap_and_cutoff_inherit (cl:=cl) (cu:=cu)
      (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hAz hC0 hc0 hmargin hcapmargin),
      Hweak,htarget,hcap,hd,hE] with n hn hnweak hntarget hncap hnd hnE
    exact (hn (P n) (M n) (x n) (hx n) hntarget
      (by simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le)
      hncap hnd hnE).2
  intro y hy hay C epsilon hC heps
  have HayP : ∀ᶠn in atTop,comparisonLowerScale (P n).context.N (P n).context.E (P n).context.d ≤ y n := by
    filter_upwards [Hcut,hay] with n hn hn'
    exact hn.trans hn'
  have HP:=Hparent y hy HayP C (epsilon/2) hC (half_pos heps)
  have HI:=actual_child_positive_band_increments_vanish_of_call_bounded hdelta hcl hAz hC0 hc0 hc01 hgapmargin
    N hN P x hx hxunit htarget hcap hweak C (epsilon/2) hC (half_pos heps)
  filter_upwards [HP,HI,hay,hd,hE,hb,hh] with n hnP hnI hny hnd hnE hnb hnh
  intro u hu
  have hchild : actualChildCutoff (N n+1) delta c0 (P n).context.d (P n).lam (x n) ≤ y n := by
    simpa only [comparisonLowerScale,hnd,hnE,actualChildCutoff] using hny
  have Hinc:=hnI (y n) hchild u hu
  have Hpar:=hnP u hu
  have hg : 0 ≤ laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u):=
    (laplaceComparisonStrength_pos _ (P n).hlam _).le
  have hr:=(comparisonSweepQuantile_bounds (P n).context.hc (P n).context.hk (P n).context.hkc
    (P n).context.hm (P n).context.hM (P n).alpha u).1
  constructor
  · rw [hnb u]
    have H:=abs_sub ((P n).b u-T) (laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u))
    rw [abs_of_nonneg hg] at H
    have he : (P n).b u-laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)-T=
        ((P n).b u-T)-laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u) := by ring
    rw [he]
    linarith only [H,Hpar.1,Hinc.1]
  · rw [hnh u]
    have H:=abs_add_le ((P n).h u)
      (laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u)
    rw [abs_of_nonneg (mul_nonneg hg hr)] at H
    linarith only [H,Hpar.2,Hinc.2]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeActualWeakSelectedHistoryClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}

def NativeSequentialComparableBandClocks
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ℝ) : Prop :=
  ∀y : ℕ→ℝ,Tendsto y atTop (𝓝 0) →
    (∀ᶠn in atTop,comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ y n) →
    ∀c C epsilon : ℝ,0 < c → 0 ≤ C → 0 < epsilon → ∀ᶠn in atTop,
      ∀u∈Icc (c*y n) (min (C*y n) 1),
        |(M n).b u-T| ≤ epsilon*(y n)^2 ∧ |(M n).h u| ≤ epsilon*(y n)^3

theorem NativeSequentialPositiveBandClocks.toComparable
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : NativeSequentialPositiveBandClocks M T) : NativeSequentialComparableBandClocks M T := by
  intro y hy hay c C epsilon hc hC hepsilon
  have Hpos : ∀ᶠn in atTop,0 < y n := by
    filter_upwards [hay] with n hn
    exact (div_pos (mul_pos (Real.sqrt_pos.mpr (M n).context.hN) (M n).context.hE)
      (M n).context.hd).trans_le hn
  filter_upwards [H y hy hay C epsilon hC hepsilon,Hpos] with n hn hny
  intro u hu
  exact hn u ⟨(mul_pos hc hny).le.trans hu.1,hu.2⟩

theorem actual_selected_bad_child_comparable_clocks_of_call_bounded
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    (P Q : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).context.N delta (P n).context.E (P n).lam ≤ x n)
    (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hd : ∀ᶠn in atTop,(Q n).context.d=actualChildRadius c0 (x n))
    (hE : ∀ᶠn in atTop,(Q n).context.E=actualChildErrorBudget (dim n+1) delta c0
      (P n).context.d (P n).lam (x n))
    (hb : ∀ᶠn in atTop,∀u,(Q n).b u=(P n).b u-
      laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u))
    (hh : ∀ᶠn in atTop,∀u,(Q n).h u=(P n).h u+
      laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u)
    (Hparent : NativeSequentialComparableBandClocks P T) :
    NativeSequentialComparableBandClocks Q T := by
  have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
  have Hcut : ∀ᶠn in atTop,
      comparisonLowerScale (P n).context.N (P n).context.E (P n).context.d  ≤ 
      comparisonLowerScale (Q n).context.N (Q n).context.E (Q n).context.d := by
    filter_upwards [hdim.eventually (eventually_actual_parent_cap_and_cutoff_inherit (cl:=cl) (cu:=cu)
      (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hAz hC0 hc0 hmargin hcapmargin),
      Hweak,htarget,hcap,hd,hE] with n hn hnweak hntarget hncap hnd hnE
    exact (hn (P n) (Q n) (x n) (hx n) hntarget
      (by simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le)
      hncap hnd hnE).2
  intro y hy hay c C epsilon hc hC heps
  have HayP : ∀ᶠn in atTop,
      comparisonLowerScale (P n).context.N (P n).context.E (P n).context.d ≤ y n := by
    filter_upwards [Hcut,hay] with n hn hn'
    exact hn.trans hn'
  have HP:=Hparent y hy HayP c C (epsilon/2) hc hC (half_pos heps)
  have HI:=actual_child_positive_band_increments_vanish_of_call_bounded hdelta hcl hAz hC0 hc0 hc01
    hgapmargin dim hdim P x hx hxunit htarget hcap hweak C (epsilon/2) hC (half_pos heps)
  filter_upwards [HP,HI,hay,hd,hE,hb,hh] with n hnP hnI hny hnd hnE hnb hnh
  intro u hu
  have hchild : actualChildCutoff (dim n+1) delta c0 (P n).context.d (P n).lam (x n) ≤ y n := by
    simpa only [comparisonLowerScale,hnd,hnE,actualChildCutoff] using hny
  have hpositive : 0 < y n:=(actual_child_cutoff_pos_le_radius (P n).context.hN
    hc0 (P n).hlam (hx n)).1.trans_le hchild
  have Hinc:=hnI (y n) hchild u ⟨(mul_pos hc hpositive).le.trans hu.1,hu.2⟩
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

theorem ActualWeakSelectedHistoryChain.comparable_clocks
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (Hroot : NativeSequentialComparableBandClocks root T) :
    NativeSequentialComparableBandClocks M T := by
  induction H with
  | root => exact Hroot
  | @child P Q history x hx hxunit htarget hcap hweak hd hE hb hh ih =>
    exact actual_selected_bad_child_comparable_clocks_of_call_bounded
      hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
      P Q x hx hxunit htarget hcap hweak hd hE hb hh ih

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

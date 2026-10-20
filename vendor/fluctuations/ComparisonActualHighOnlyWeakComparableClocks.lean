module

public import ComparisonActualHighOnlyChildClocks
public import ComparisonActualHighWallComparableBandClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {N dim : ℕ→ℕ}

def HighOnlySequentialComparableBandClocks
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ℝ) : Prop :=
  ∀y : ℕ→ℝ,Tendsto y atTop (𝓝 0) →
    (∀ᶠn in atTop,comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ y n) →
    ∀c C epsilon : ℝ,0 < c → 0 ≤ C → 0 < epsilon → ∀ᶠn in atTop,
      ∀u∈Icc (c*y n) (min (C*y n) 1),
        |(M n).b u-T| ≤ epsilon*(y n)^2 ∧ |(M n).h u| ≤ epsilon*(y n)^3

theorem actual_selected_bad_child_comparable_clocks_of_call_bounded
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    (P Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
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
      (P n).coefficient u)
    (hh : ∀ᶠn in atTop,∀u,(Q n).h u=(P n).h u+
      (P n).coefficient u*(P n).R u)
    (Hparent : HighOnlySequentialComparableBandClocks P T) :
    HighOnlySequentialComparableBandClocks Q T := by
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
  have hg : 0 ≤ (P n).coefficient u := (P n).coefficient_nonneg u
  have hr:=(omittedSweepQuantile_bounds zero_le_one ⟨(P n).data.hs.1,(P n).data.hs1⟩
    (P n).context.hc (P n).context.hk (P n).context.hkc (P n).context.hm
    (P n).context.hM (P n).alpha u).1
  have he : (P n).coefficient u ≤ laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u) := by
    unfold coefficient ActualHighOnlyComparisonData.coefficient omittedStrengthCoefficient
    split_ifs
    · exact le_rfl
    · exact (laplaceComparisonStrength_pos _ (P n).hlam _).le
  have hfield:=mul_le_mul_of_nonneg_right he hr
  constructor
  · rw [hnb u]
    have H:=abs_sub ((P n).b u-T) ((P n).coefficient u)
    rw [abs_of_nonneg hg] at H
    have heq : (P n).b u-(P n).coefficient u-T=
        ((P n).b u-T)-(P n).coefficient u := by ring
    rw [heq]
    linarith only [H,Hpar.1,Hinc.1,he]
  · rw [hnh u]
    have H:=abs_add_le ((P n).h u)
      ((P n).coefficient u*(P n).R u)
    rw [abs_of_nonneg (mul_nonneg hg hr)] at H
    linarith only [H,Hpar.2,Hinc.2,hfield]

inductive ActualWeakHighOnlyHistoryChain (c0 : ℝ)
    (root : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock) :
    ((n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)→Prop
  | root : ActualWeakHighOnlyHistoryChain c0 root root
  | child {P M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
      (history : ActualWeakHighOnlyHistoryChain c0 root P)
      (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
      (htarget : ∀ᶠn in atTop,
        comparisonConditionalScale (P n).context.N delta (P n).context.E (P n).lam ≤ x n)
      (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
      (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam (x n)/(x n)^2)
        atTop (𝓝 0))
      (hd : ∀ᶠn in atTop,(M n).context.d=actualChildRadius c0 (x n))
      (hE : ∀ᶠn in atTop,(M n).context.E=actualChildErrorBudget (N n+1) delta c0 (P n).context.d (P n).lam (x n))
      (hs : ∀ᶠn in atTop,(M n).data.s=(P n).data.s)
      (hb : ∀ᶠn in atTop,∀u,(M n).b u=(P n).b u-(P n).coefficient u)
      (hh : ∀ᶠn in atTop,∀u,(M n).h u=(P n).h u+(P n).coefficient u*(P n).R u) :
      ActualWeakHighOnlyHistoryChain c0 root M

theorem ActualWeakHighOnlyHistoryChain.comparable_clocks
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (Hroot : HighOnlySequentialComparableBandClocks root T) :
    HighOnlySequentialComparableBandClocks M T := by
  induction H with
  | root => exact Hroot
  | @child P Q history x hx hxunit htarget hcap hweak hd hE hs hb hh ih =>
    exact actual_selected_bad_child_comparable_clocks_of_call_bounded
      hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
      P Q x hx hxunit htarget hcap hweak hd hE hb hh ih

theorem SequentialComparableBareClocks.toHighOnly
    {a : ℕ→ℝ} {b h : ℕ→ℝ→ℝ}
    (H : SequentialComparableBareClocks a b h T)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (ha : ∀ᶠn in atTop,a n ≤ comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d)
    (hb : ∀ᶠn in atTop,∀u,(M n).b u=b n u)
    (hh : ∀ᶠn in atTop,∀u,(M n).h u=h n u) : HighOnlySequentialComparableBandClocks M T := by
  intro y hy hay c C eps hc hC heps
  have hay' : ∀ᶠn in atTop,a n ≤ y n := by
    filter_upwards [ha,hay] with n hn hn'
    exact hn.trans hn'
  filter_upwards [H y hy hay' c C eps hc hC heps,hb,hh] with n hn hnb hnh
  simpa only [hnb,hnh] using hn

theorem ActualWeakHighOnlyHistoryChain.same_omission
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M) : ∀ᶠn in atTop,(M n).data.s=(root n).data.s := by
  induction H with
  | root=>exact Eventually.of_forall (fun _=>rfl)
  | @child P Q history x hx hxunit htarget hcap hweak hd hE hs hb hh ih=>
    filter_upwards [ih,hs] with n hn hns
    exact hns.trans hn

theorem ActualWeakHighOnlyHistoryChain.cutoff_inherits_root
    (hm : 0 < m) (hdelta : 0 < delta) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hN : Tendsto N atTop atTop)
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M) :
    ∀ᶠn in atTop,comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d ≤
      comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d := by
  induction H with
  | root=>exact Eventually.of_forall (fun _=>le_rfl)
  | @child P Q history x hx hxunit htarget hcap hweak hd hE hs hb hh ih=>
    have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [ih,hN.eventually (eventually_actual_parent_cap_and_cutoff_inherit
      hm hdelta hAz hC0 hc0 hmargin hcapmargin),Hweak,htarget,hcap,hd,hE]
      with n hn hncut hnweak hnt hncap hnd hnE
    exact hn.trans ((hncut (P n) (Q n) (x n) (hx n) hnt
      (by simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le)
      hncap hnd hnE).2)

theorem ActualWeakHighOnlyHistoryChain.total_root
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (Hroot : ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(root n).h u+(root n).b u ≤ T) ∧ (root n).h 0=0) :
    ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0 := by
  induction H with
  | root=>exact Hroot
  | @child P Q history x hx hxunit htarget hcap hweak hd hE hs hb hh ih=>
    filter_upwards [ih,hb,hh] with n hn hnb hnh
    constructor
    · intro u hu
      rw [hnb,hnh]
      have hr:=(omittedSweepQuantile_bounds zero_le_one ⟨(P n).data.hs.1,(P n).data.hs1⟩
        (P n).data.hc (P n).data.hk (P n).data.hkc (P n).data.hm (P n).data.hM (P n).alpha u).2
      have H:=mul_le_mul_of_nonneg_left hr ((P n).coefficient_nonneg u)
      linarith [hn.1 u hu]
    · rw [hnh,hn.2,(P n).R_zero,mul_zero,add_zero]

theorem ActualWeakHighOnlyHistoryChain.bare_field_budget
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m) (hN : Tendsto N atTop atTop)
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (Hroot : ∃C : ℝ,0 ≤ C ∧ ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(root n).h u ≤
      C*(comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d+u)) :
    ∃C : ℝ,0 ≤ C ∧ ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u ≤
      C*(comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d+u) := by
  induction H with
  | root=>exact Hroot
  | @child P Q history x hx hxunit htarget hcap hweak hd hE hs hb hh ih=>
    obtain ⟨C,hC,HC⟩:=ih
    let K:=Az*max 1 (D^2/c0)
    have hK : 0 ≤ K:=by dsimp only [K];positivity
    refine ⟨C+K+D^2/cl,by positivity,?_⟩
    have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [HC,hN.eventually (eventually_actual_parent_cap_and_cutoff_inherit
      hm hdelta hAz hC0 hc0 hmargin hcapmargin),Hweak,htarget,hcap,hd,hE,hh]
      with n hn hncut hnweak hnt hncap hnd hnE hnh u hu
    have Hcut:=hncut (P n) (Q n) (x n) (hx n) hnt
      (by simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le) hncap hnd hnE
    have Hbare:=(hn u hu).trans (mul_le_mul_of_nonneg_left (add_le_add Hcut.2 le_rfl) hC)
    have Hfield:=(P n).comparison_field_le_regular_cap hcl hu
    have hD : 0 ≤ D:=(P n).context.hd.le.trans (P n).hdD
    have hlam : (P n).lam ≤ D^2:=
      (P n).hld.trans (pow_le_pow_left₀ (P n).context.hd.le (P n).hdD 2)
    have Hlam:=mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlam hcl.le) hu.1
    have Hlow : 0 ≤ comparisonLowerScale (Q n).context.N (Q n).context.E (Q n).context.d:=
      (div_pos (mul_pos (Real.sqrt_pos.mpr (Q n).context.hN) (Q n).context.hE) (Q n).context.hd).le
    have HX:=mul_nonneg hK hu.1
    have HY:=mul_nonneg (div_nonneg (sq_nonneg D) hcl.le) Hlow
    rw [hnh]
    have Hcap:=Hcut.1
    change (P n).lam*(P n).z ≤ K*comparisonLowerScale (Q n).context.N (Q n).context.E (Q n).context.d at Hcap
    nlinarith only [Hbare,Hfield,Hcap,Hlam,HX,HY]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

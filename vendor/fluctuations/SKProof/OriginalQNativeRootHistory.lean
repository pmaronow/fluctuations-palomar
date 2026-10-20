module

public import ComparisonActualHighWallThetaZeroChildComparableClocks
public import ComparisonActualHighWallThetaZeroChildClockNumerics
public import ComparisonActualHighWallThetaZeroHighOnlySourceClocks
public import ComparisonActualHighWallThetaZeroHighOnlySourceField
public import ComparisonNativeActualGeneralBareHistoryCavityContext
public import ComparisonNativeActualComparableBandContext
public import ComparisonNativeActualMinimumChild
public import ComparisonActualHighWallThetaZeroMacroscopicEndpoint
public import ComparisonNativeActualGeneralBareEndpointCost
public import ComparisonNativeActualComparableBandWorkingScale
public import ComparisonNativeActualComparableBandCompleteProfile
public import ComparisonNativeActualWeakHistoryOperations
public import ComparisonNativeActualGeneralProfileHistoryAssembly
public import ComparisonActualHighWallThetaZeroWeakenConstantsIsolatedDraft
public import ComparisonActualHighWallThetaZeroNativeChildPullback

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

theorem ActualWeakSelectedHistoryChain.exists_theta_zero_comparable_context_original_q
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hTpos : 0 < T)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (hT : ∀ᶠn in atTop, (P n).data.T = T)
    (hunit : ∀ᶠn in atTop, (P n).xs ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).data.N delta
        (P n).data.E (P n).lam ≤ (P n).xs)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (P n).data.d (P n).lam (P n).xs/(P n).xs^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n => (P n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs) atTop (𝓝 0))
    (hcut : ∀ᶠn in atTop,
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs ≤
      comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d)
    (hb : ∀ᶠn in atTop, ∀u,
      (root n).b u = (P n).changedBare u)
    (hh : ∀ᶠn in atTop, ∀u,
      (root n).h u = (P n).changedField u)
    (hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0)) :
    Nonempty (NativeActualComparableBandContext M T) := by
  have Hroot : ∀ᶠn in atTop,
      (∀u∈Icc (0:ℝ) 1, (root n).h u+(root n).b u ≤ T) ∧
      (root n).h 0 = 0 := by
    filter_upwards [hT,hb,hh] with n hnT hnb hnh
    constructor
    · intro u hu
      rw [hnb,hnh,←hnT]
      exact (P n).changed_total_clock_le_temperature hu
    · rw [hnh]
      exact (P n).changed_root_field_zero
  have Hstrength : ∀ᶠn in atTop, (P n).lam ≤
      (actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs)^2 := by
    have Hweak := hweak.eventually
      (gt_mem_nhds (pow_pos hc0 3))
    filter_upwards [hdim.eventually
      (eventually_theta_zero_strength_le_child_cutoff_sq
        hdelta hC0 hc0 hc01 (show (0:ℝ)<1 by norm_num)
        (show (1:ℝ)≤1 by norm_num) hgapmargin),
      hunit,htarget,Hweak] with n hn hnunit hntarget hnweak
    have Hnumeric : laplaceComparisonStrength (P n).data.d
        (P n).lam (P n).xs ≤ ((1:ℝ)*c0)^3*(P n).xs^2 := by
      simpa only [one_mul] using
        (div_le_iff₀ (sq_pos_of_pos (P n).hxs)).mp hnweak.le
    simpa only [one_pow,one_mul] using
      hn (P n) hnunit hntarget Hnumeric
  have Hfield : ∀ᶠn in atTop,
      ∀u∈Icc (0:ℝ) 1, (root n).h u ≤
      (1:ℝ)*(comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d+u) := by
    filter_upwards [hh,hcut,hunit,Hstrength] with n hnh hncut hnunit
      hnstrength u hu
    have Hcut : 0 < actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs ∧
        actualChildCutoff (dim n+1) delta c0
          (P n).data.d (P n).lam (P n).xs ≤ c0*(P n).xs :=
      actual_child_cutoff_pos_le_radius
        (P n).data.hN hc0 (P n).hlam (P n).hxs
    have Hcut1 : actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs ≤ 1 :=
      Hcut.2.trans ((mul_le_mul_of_nonneg_left hnunit hc0.le).trans
        (by simpa only [mul_one] using hc01))
    have HcutSq : (actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs)^2 ≤
        actualChildCutoff (dim n+1) delta c0
          (P n).data.d (P n).lam (P n).xs := by
      have Hprod := mul_nonneg Hcut.1.le (sub_nonneg.mpr Hcut1)
      nlinarith only [Hprod]
    rw [hnh,one_mul]
    exact ((P n).changed_field_le_selected_strength hu).trans
      (by linarith only [hnstrength,HcutSq,hncut,hu.1])
  have Hbare : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val
        (root n).b (root n).h 0 1 := by
    filter_upwards [hb,hh] with n hnb hnh
    have HB : (root n).b = (P n).changedBare := funext hnb
    have HH : (root n).h = (P n).changedField := funext hnh
    rw [HB,HH]
    change NativePullbackClockRegularity (M n).alpha.val.val
      (fun u =>
        ((P n).data.thetaZeroShiftedParentData
          (P n).lam (P n).hlam (P n).hld).b u-
        ((P n).data.thetaZeroShiftedParentData
          (P n).lam (P n).hlam (P n).hld).coefficient (P n).alpha u)
      (fun u =>
        ((P n).data.thetaZeroShiftedParentData
          (P n).lam (P n).hlam (P n).hld).h u+
        ((P n).data.thetaZeroShiftedParentData
          (P n).lam (P n).hlam (P n).hld).coefficient (P n).alpha u*
        ((P n).data.thetaZeroShiftedParentData
          (P n).lam (P n).hlam (P n).hld).R (P n).alpha u) 0 1
    exact (P n).changed_pullback_on_native_child_profile
      (M n).context.toChildBarrierParameters (M n).alpha
  obtain ⟨G⟩ := H.exists_general_bare_cavity_clock_context
    hm hdelta hcl hAz hC0 hc0 hTpos zero_le_one
    hmargin hcapmargin hdim Hroot Hfield Hbare hxs
  have Hpositive := theta_zero_first_child_comparable_bare_clocks
    hdelta hcl hAz hC0 hc0 hc01 hgapmargin
    dim hdim P hT hunit htarget hweak hs
  have Hseed := Hpositive.toNative root hcut hb hh
  exact ⟨⟨G,H.comparable_clocks hm hdelta hcl hAz hC0
    hc0 hc01 hmargin hcapmargin hgapmargin hdim Hseed⟩⟩

theorem ActualWeakSelectedHistoryChain.endpoint_cost_tendsto_zero_original_q
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ → ℕ}
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (hT : ∀ᶠn in atTop, (P n).data.T = T)
    (hs : Tendsto (fun n => (P n).data.s) atTop (𝓝 0))
    (hunit : ∀ᶠn in atTop, (P n).xs ≤ 1)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (P n).data.d (P n).lam (P n).xs/(P n).xs^2) atTop (𝓝 0))
    (hb : ∀ᶠn in atTop, ∀u, (root n).b u = (P n).changedBare u)
    (hh : ∀ᶠn in atTop, ∀u, (root n).h u = (P n).changedField u) :
    Tendsto (fun n => comparisonEndpointL1Cost T (M n).b (M n).h)
      atTop (𝓝 0) := by
  have hlam := actual_comparison_parameter_tendsto_zero_of_weak_bounded_call
    (hunit.mono fun n hn =>
      ⟨(P n).data.hd, (P n).hlam.le, (P n).hxs, hn, (P n).hld⟩)
    hweak
  have hbound : Tendsto (fun n =>
      T*(P n).data.s/4+(3/4:ℝ)*(P n).lam) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div, add_zero] using
      (hs.const_mul T |>.div_const 4).add (hlam.const_mul (3/4:ℝ))
  have hchanged : Tendsto (fun n => comparisonEndpointL1Cost T
      (P n).changedBare (P n).changedField) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Eventually.of_forall (fun n =>
        actual_high_only_endpoint_l1_cost_nonneg T
          (P n).changedBare (P n).changedField)) ?_ hbound
    filter_upwards [hT] with n hnT
    have hcost := (P n).theta_zero_changed_endpoint_cost_le
    have hmass : 0 ≤ (P n).data.s := (P n).data.hs.1.le
    have heps := (P n).data.hepsilon.2.le
    rw [hnT] at hcost heps
    have hmul := mul_le_mul_of_nonneg_left heps hmass
    nlinarith only [hcost, hmul]
  have hroot : Tendsto (fun n => comparisonEndpointL1Cost T
      (root n).b (root n).h) atTop (𝓝 0) := by
    apply Filter.Tendsto.congr' ?_ hchanged
    filter_upwards [hb,hh] with n hbn hhn
    have hb' : (root n).b = (P n).changedBare := funext hbn
    have hh' : (root n).h = (P n).changedField := funext hhn
    rw [hb',hh']
  exact actual_weak_general_bare_history_endpoint_cost_tendsto_zero H hroot

theorem ActualWeakSelectedHistoryChain.bad_native_weak_strength_original_q
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hTpos : 0 < T)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclmargin : cl < T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (hT : ∀ᶠn in atTop, (P n).data.T = T)
    (hunit : ∀ᶠn in atTop, (P n).xs ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).data.N delta
        (P n).data.E (P n).lam ≤ (P n).xs)
    (hparentWeak : Tendsto (fun n => laplaceComparisonStrength
      (P n).data.d (P n).lam (P n).xs/(P n).xs^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n => (P n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs) atTop (𝓝 0))
    (hcut : ∀ᶠn in atTop,
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs ≤
      comparisonLowerScale (root n).context.N
        (root n).context.E (root n).context.d)
    (hb : ∀ᶠn in atTop, ∀u, (root n).b u = (P n).changedBare u)
    (hh : ∀ᶠn in atTop, ∀u, (root n).h u = (P n).changedField u)
    (hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0))
    (hd : ∀ᶠn in atTop, (M n).context.d ≤ 1)
    (hbad : ∀ᶠn in atTop,
      ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) :
    Tendsto (fun n => laplaceComparisonStrength
      (M n).context.d (M n).lam (M n).xs/(M n).xs^2)
      atTop (𝓝 0) := by
  obtain ⟨G⟩ := H.exists_theta_zero_comparable_context_original_q
    hm hdelta hcl hAz hC0 hc0 hc01 hTpos
    hmargin hcapmargin hgapmargin dim hdim P root M
    hT hunit htarget hparentWeak hs hcut hb hh hxs
  have hWupper := eventually_actual_comparable_context_working_scale_le_one
    M G hd
  exact actual_comparable_context_bad_test_strength_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G
    hWupper hclmargin hcumargin hbad

structure OriginalQNativeRootHistory
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ → ℕ}
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock) (T c0 : ℝ) where
  wall : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
    m delta cl cu Az C0 Ct D Bclock
  root : (n : ℕ) → NativeOverlapMinimum (dim n+1)
    m delta cl cu Az C0 Ct D Bclock
  history : ActualWeakSelectedHistoryChain c0 root M
  hTemp : ∀ᶠn in atTop, (wall n).data.T = T
  hunit : ∀ᶠn in atTop, (wall n).xs ≤ 1
  htarget : ∀ᶠn in atTop,
    comparisonConditionalScale (wall n).data.N delta
      (wall n).data.E (wall n).lam ≤ (wall n).xs
  hweak : Tendsto (fun n => laplaceComparisonStrength
    (wall n).data.d (wall n).lam (wall n).xs/(wall n).xs^2)
    atTop (𝓝 0)
  hsZero : Tendsto (fun n => (wall n).data.s) atTop (𝓝 0)
  hsCut : Tendsto (fun n => (wall n).data.s/
    actualChildCutoff (dim n+1) delta c0
      (wall n).data.d (wall n).lam (wall n).xs) atTop (𝓝 0)
  hcut : ∀ᶠn in atTop,
    actualChildCutoff (dim n+1) delta c0
      (wall n).data.d (wall n).lam (wall n).xs ≤
    comparisonLowerScale (root n).context.N
      (root n).context.E (root n).context.d
  hb : ∀ᶠn in atTop, ∀u, (root n).b u = (wall n).changedBare u
  hh : ∀ᶠn in atTop, ∀u, (root n).h u = (wall n).changedField u
  hT : 0 < T

namespace OriginalQNativeRootHistory

variable {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ → ℕ}
variable {M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
  m delta cl cu Az C0 Ct D Bclock}

theorem total_root_original_q (G : OriginalQNativeRootHistory M T c0) :
    ∀ᶠn in atTop,
      (∀u∈Icc (0:ℝ) 1, (M n).h u+(M n).b u ≤ T) ∧
      (M n).h 0 = 0 := by
  apply G.history.total_root_general_bare
  filter_upwards [G.hTemp,G.hb,G.hh] with n hnT hnb hnh
  constructor
  · intro u hu
    rw [hnb,hnh]
    exact ((G.wall n).changed_total_clock_le_temperature hu).trans_eq hnT
  · rw [hnh]
    exact (G.wall n).changed_root_field_zero

theorem endpoint_cost_tendsto_zero_original_q
    (G : OriginalQNativeRootHistory M T c0) :
    Tendsto (fun n => comparisonEndpointL1Cost T (M n).b (M n).h)
      atTop (𝓝 0) :=
  ActualWeakSelectedHistoryChain.endpoint_cost_tendsto_zero_original_q
    G.wall G.root M G.history G.hTemp G.hsZero G.hunit G.hweak
    G.hb G.hh

theorem exists_context_original_q
    (hm : 0 < m) (hdelta : 0 < delta)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hdim : Tendsto dim atTop atTop)
    (G : OriginalQNativeRootHistory M T c0)
    (hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0)) :
    Nonempty (NativeActualComparableBandContext M T) :=
  G.history.exists_theta_zero_comparable_context_original_q
    hm hdelta hcl hAz hC0 hc0 hc01 G.hT
    hmargin hcapmargin hgapmargin dim hdim G.wall G.root M
    G.hTemp G.hunit G.htarget G.hweak G.hsCut
    G.hcut G.hb G.hh hxs

def comp_original_q (G : OriginalQNativeRootHistory M T c0)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    OriginalQNativeRootHistory (fun n => M (phi n)) T c0 where
  wall := fun n => G.wall (phi n)
  root := fun n => G.root (phi n)
  history := G.history.comp phi hphi.tendsto_atTop
  hTemp := hphi.tendsto_atTop.eventually G.hTemp
  hunit := hphi.tendsto_atTop.eventually G.hunit
  htarget := hphi.tendsto_atTop.eventually G.htarget
  hweak := G.hweak.comp hphi.tendsto_atTop
  hsZero := G.hsZero.comp hphi.tendsto_atTop
  hsCut := G.hsCut.comp hphi.tendsto_atTop
  hcut := hphi.tendsto_atTop.eventually G.hcut
  hb := hphi.tendsto_atTop.eventually G.hb
  hh := hphi.tendsto_atTop.eventually G.hh
  hT := G.hT

def append_child_original_q (G : OriginalQNativeRootHistory M T c0)
    (Q : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (hx : ∀n, 0 < x n)
    (hxunit : ∀ᶠn in atTop, x n ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta
        (M n).context.E (M n).lam ≤ x n)
    (hcap : ∀ᶠn in atTop, (M n).z ≤ Az*x n)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (M n).context.d (M n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (hd : ∀ᶠn in atTop, (Q n).context.d = actualChildRadius c0 (x n))
    (hE : ∀ᶠn in atTop, (Q n).context.E = actualChildErrorBudget
      (dim n+1) delta c0 (M n).context.d (M n).lam (x n))
    (hb : ∀ᶠn in atTop, ∀u, (Q n).b u = (M n).b u-
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))
    (hh : ∀ᶠn in atTop, ∀u, (Q n).h u = (M n).h u+
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
        (M n).R u) :
    OriginalQNativeRootHistory Q T c0 where
  wall := G.wall
  root := G.root
  history := .child G.history x hx hxunit htarget hcap hweak hd hE hb hh
  hTemp := G.hTemp
  hunit := G.hunit
  htarget := G.htarget
  hweak := G.hweak
  hsZero := G.hsZero
  hsCut := G.hsCut
  hcut := G.hcut
  hb := G.hb
  hh := G.hh
  hT := G.hT

def weaken_constants_original_q (G : OriginalQNativeRootHistory M T c0)
    {cl' cu' Az' Ct' D' Bclock' : ℝ}
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    OriginalQNativeRootHistory
      (fun n => (M n).weakenConstants hcl hcu hAz hCt hD hB) T c0 where
  wall := fun n => (G.wall n).weakenConstants
    hcl hcu hAz hCt hD hB
  root := fun n => (G.root n).weakenConstants hcl hcu hAz hCt hD hB
  history := G.history.weaken_constants hcl hcu hAz hCt hD hB
  hTemp := G.hTemp
  hunit := G.hunit
  htarget := G.htarget
  hweak := G.hweak
  hsZero := G.hsZero
  hsCut := G.hsCut
  hcut := G.hcut
  hb := G.hb
  hh := G.hh
  hT := G.hT

end OriginalQNativeRootHistory

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

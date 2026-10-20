module

public import ComparisonActualHighWallThetaZeroHighOnlyHistoryContext
public import ComparisonActualHighOnlyHistoryWeakenConstants
public import ComparisonActualHighOnlyHistoryReindex
public import ComparisonActualHighOnlyWeakHistoryEndpointCost
public import ComparisonActualHighWallThetaZeroHighOnlyRootEndpointCost
public import ComparisonActualHighWallThetaZeroHighOnlyRootGap
public import ComparisonActualHighWallThetaZeroWeakenConstantsIsolatedDraft
public import ComparisonNativeActualChildParameterGrowth

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
namespace ActualHighOnlyOverlapMinimum
variable {m cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ → ℕ}

structure OriginalQHighOnlyHistory
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock) (T c0 : ℝ) where
  wall : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
    m (m/10000) cl cu Az C0 Ct D Bclock
  root : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
    m (m/10000) cl cu Az C0 Ct D Bclock
  history : ActualWeakHighOnlyHistoryChain c0 root M
  temperature : ∀ᶠ n in atTop, (wall n).data.T = T
  error : ∀ᶠ n in atTop, (wall n).data.E = wallHighError m (dim n+1)
  radius : ∀ᶠ n in atTop, (wall n).data.d = wallHighD m (dim n+1)
  omission : ∀ᶠ n in atTop, (wall n).data.s = wallHighMass m (dim n+1)
  same_mass : ∀ᶠ n in atTop, (root n).data.s = (wall n).data.s
  wall_unit : ∀ᶠ n in atTop, (wall n).xs ≤ 1
  wall_target : ∀ᶠ n in atTop, comparisonConditionalScale (wall n).data.N (m/10000)
    (wall n).data.E (wall n).lam ≤ (wall n).xs
  wall_weak : Tendsto (fun n => laplaceComparisonStrength (wall n).data.d
    (wall n).lam (wall n).xs/(wall n).xs^2) atTop (𝓝 0)
  wall_cut : Tendsto (fun n => (wall n).data.s/actualChildCutoff (dim n+1)
    (m/10000) c0 (wall n).data.d (wall n).lam (wall n).xs) atTop (𝓝 0)
  first_radius : ∀ᶠ n in atTop, (root n).context.d = actualChildRadius c0 (wall n).xs
  first_error : ∀ᶠ n in atTop, (root n).context.E = actualChildErrorBudget
    (dim n+1) (m/10000) c0 (wall n).data.d (wall n).lam (wall n).xs
  bare : ∀ᶠ n in atTop, ∀ u, (root n).b u = (wall n).changedBare u
  field : ∀ᶠ n in atTop, ∀ u, (root n).h u = (wall n).changedField u
  hT : 0 < T

namespace OriginalQHighOnlyHistory
variable {M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
  m (m/10000) cl cu Az C0 Ct D Bclock}

def comp (G : OriginalQHighOnlyHistory M T c0)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    OriginalQHighOnlyHistory (fun n => M (phi n)) T c0 where
  wall := fun n => G.wall (phi n)
  root := fun n => G.root (phi n)
  history := G.history.comp phi hphi.tendsto_atTop
  temperature := hphi.tendsto_atTop.eventually G.temperature
  error := hphi.tendsto_atTop.eventually G.error
  radius := hphi.tendsto_atTop.eventually G.radius
  omission := hphi.tendsto_atTop.eventually G.omission
  same_mass := hphi.tendsto_atTop.eventually G.same_mass
  wall_unit := hphi.tendsto_atTop.eventually G.wall_unit
  wall_target := hphi.tendsto_atTop.eventually G.wall_target
  wall_weak := G.wall_weak.comp hphi.tendsto_atTop
  wall_cut := G.wall_cut.comp hphi.tendsto_atTop
  first_radius := hphi.tendsto_atTop.eventually G.first_radius
  first_error := hphi.tendsto_atTop.eventually G.first_error
  bare := hphi.tendsto_atTop.eventually G.bare
  field := hphi.tendsto_atTop.eventually G.field
  hT := G.hT

def weaken_constants (G : OriginalQHighOnlyHistory M T c0)
    {cl' cu' Az' Ct' D' Bclock' : ℝ}
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    OriginalQHighOnlyHistory
      (fun n => (M n).weakenConstants hcl hcu hAz hCt hD hB) T c0 where
  wall := fun n => (G.wall n).weakenConstants hcl hcu hAz hCt hD hB
  root := fun n => (G.root n).weakenConstants hcl hcu hAz hCt hD hB
  history := G.history.weaken_constants hcl hcu hAz hCt hD hB
  temperature := G.temperature
  error := G.error
  radius := G.radius
  omission := G.omission
  same_mass := G.same_mass
  wall_unit := G.wall_unit
  wall_target := G.wall_target
  wall_weak := G.wall_weak
  wall_cut := G.wall_cut
  first_radius := G.first_radius
  first_error := G.first_error
  bare := G.bare
  field := G.field
  hT := G.hT

def append_child (G : OriginalQHighOnlyHistory M T c0)
    (Q : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n) (hxunit : ∀ᶠ n in atTop, x n ≤ 1)
    (htarget : ∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N (m/10000)
      (M n).context.E (M n).lam ≤ x n)
    (hcap : ∀ᶠ n in atTop, (M n).z ≤ Az*x n)
    (hweak : Tendsto (fun n => laplaceComparisonStrength (M n).context.d
      (M n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (hd : ∀ᶠ n in atTop, (Q n).context.d = actualChildRadius c0 (x n))
    (hE : ∀ᶠ n in atTop, (Q n).context.E = actualChildErrorBudget (dim n+1)
      (m/10000) c0 (M n).context.d (M n).lam (x n))
    (hs : ∀ᶠ n in atTop, (Q n).data.s = (M n).data.s)
    (hb : ∀ᶠ n in atTop, ∀ u, (Q n).b u = (M n).b u-(M n).coefficient u)
    (hh : ∀ᶠ n in atTop, ∀ u, (Q n).h u =
      (M n).h u+(M n).coefficient u*(M n).R u) :
    OriginalQHighOnlyHistory Q T c0 where
  wall := G.wall
  root := G.root
  history := .child G.history x hx hxunit htarget hcap hweak hd hE hs hb hh
  temperature := G.temperature
  error := G.error
  radius := G.radius
  omission := G.omission
  same_mass := G.same_mass
  wall_unit := G.wall_unit
  wall_target := G.wall_target
  wall_weak := G.wall_weak
  wall_cut := G.wall_cut
  first_radius := G.first_radius
  first_error := G.first_error
  bare := G.bare
  field := G.field
  hT := G.hT

def with_current (G : OriginalQHighOnlyHistory M T c0)
    (Q : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (H : ActualWeakHighOnlyHistoryChain c0 G.root Q) :
    OriginalQHighOnlyHistory Q T c0 where
  wall := G.wall
  root := G.root
  history := H
  temperature := G.temperature
  error := G.error
  radius := G.radius
  omission := G.omission
  same_mass := G.same_mass
  wall_unit := G.wall_unit
  wall_target := G.wall_target
  wall_weak := G.wall_weak
  wall_cut := G.wall_cut
  first_radius := G.first_radius
  first_error := G.first_error
  bare := G.bare
  field := G.field
  hT := G.hT

theorem exists_context (G : OriginalQHighOnlyHistory M T c0)
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hdim : Tendsto dim atTop atTop)
    (hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0)) :
    Nonempty (HighOnlyActualComparableBandContext M T) := by
  have hdelta : 0 < m/10000 := by positivity
  have Hcut : ∀ᶠ n in atTop, actualChildCutoff (dim n+1) (m/10000) c0
      (G.wall n).data.d (G.wall n).lam (G.wall n).xs ≤
        comparisonLowerScale (G.root n).context.N
          (G.root n).context.E (G.root n).context.d := by
    filter_upwards [G.first_radius, G.first_error] with n hnd hnE
    simp only [comparisonLowerScale, ActualHighOnlyComparisonData.N,
      hnd, hnE, actualChildCutoff]
    exact le_rfl
  exact G.history.exists_theta_zero_wall_comparable_context hm hdelta hcl hAz hC0
    hc0 hc01 G.hT (by linarith) (by linarith) (by linarith)
    dim hdim G.wall G.root M G.temperature G.same_mass G.wall_unit G.wall_target
    G.wall_weak G.wall_cut Hcut G.bare G.field hxs

theorem wall_limits (G : OriginalQHighOnlyHistory M T c0)
    (hmsmall : m ≤ (1:ℝ)/120) (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => (G.wall n).data.s) atTop (𝓝 0) ∧
      Tendsto (fun n => (G.wall n).data.d) atTop (𝓝 0) := by
  have HN : Tendsto (fun n => ((dim n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  constructor
  · have H := (tendsto_rpow_neg_atTop (show 0 < (1:ℝ)/6-5*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [G.omission] with n hn
    simp only [Function.comp_apply]
    rw [hn]
    unfold wallHighMass
    congr 1
    ring
  · have H := (tendsto_rpow_neg_atTop (show 0 < (1:ℝ)/6-15*m by linarith)).comp HN
    apply H.congr'
    filter_upwards [G.radius] with n hn
    simp only [Function.comp_apply]
    rw [hn]
    unfold wallHighD
    congr 1
    ring

theorem root_endpoint_cost_tendsto_zero (G : OriginalQHighOnlyHistory M T c0)
    (hmsmall : m ≤ (1:ℝ)/120) (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => comparisonEndpointL1Cost T (G.root n).b (G.root n).h)
      atTop (𝓝 0) :=
  ActualThetaZeroOverlapMinimum.high_only_root_endpoint_cost_tendsto_zero
    G.wall G.root G.temperature (G.wall_limits hmsmall hdim).1 G.wall_unit
    G.wall_weak G.bare G.field

theorem endpoint_cost_tendsto_zero (G : OriginalQHighOnlyHistory M T c0)
    (hmsmall : m ≤ (1:ℝ)/120) (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0) :=
  G.history.endpoint_cost_tendsto_zero (G.root_endpoint_cost_tendsto_zero hmsmall hdim)

theorem same_omission (G : OriginalQHighOnlyHistory M T c0) :
    ∀ᶠ n in atTop, (M n).data.s = (G.wall n).data.s := by
  filter_upwards [G.history.same_omission, G.same_mass] with n hn hr
  exact hn.trans hr

theorem omission_tendsto_zero (G : OriginalQHighOnlyHistory M T c0)
    (hmsmall : m ≤ (1:ℝ)/120) (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => (M n).data.s) atTop (𝓝 0) :=
  (G.wall_limits hmsmall hdim).1.congr' (G.same_omission.mono (fun _ hn=>hn.symm))

theorem total_root (G : OriginalQHighOnlyHistory M T c0) :
    ∀ᶠ n in atTop, (∀ u ∈ Icc (0:ℝ) 1, (M n).h u+(M n).b u ≤ T) ∧
      (M n).h 0 = 0 := by
  apply G.history.total_root
  filter_upwards [G.temperature, G.bare, G.field] with n hnT hb hh
  constructor
  · intro u hu
    rw [hb, hh]
    exact ((G.wall n).changed_total_clock_le_temperature hu).trans_eq hnT
  · rw [hh]
    exact (G.wall n).changed_root_field_zero

theorem root_cutoff_gates (G : OriginalQHighOnlyHistory M T c0)
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => (G.wall n).data.s/actualChildCutoff (dim n+1) (m/10000)
      c0 (G.wall n).data.d (G.wall n).lam (G.wall n).xs) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, actualChildCutoff (dim n+1) (m/10000) c0
        (G.wall n).data.d (G.wall n).lam (G.wall n).xs ≤
          comparisonLowerScale (G.root n).context.N
            (G.root n).context.E (G.root n).context.d) ∧
      (∀ᶠ n in atTop, (G.wall n).data.d^2 ≤ comparisonLowerScale
        (G.root n).context.N (G.root n).context.E (G.root n).context.d) := by
  have hdelta : 0 < m/10000 := by positivity
  have Hcut : ∀ᶠ n in atTop, actualChildCutoff (dim n+1) (m/10000) c0
      (G.wall n).data.d (G.wall n).lam (G.wall n).xs ≤
        comparisonLowerScale (G.root n).context.N
          (G.root n).context.E (G.root n).context.d := by
    filter_upwards [G.first_radius, G.first_error] with n hnd hnE
    simp only [comparisonLowerScale, ActualHighOnlyComparisonData.N,
      hnd, hnE, actualChildCutoff]
    exact le_rfl
  have Hdim : Tendsto (fun n => dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  have Hparam := Hdim.eventually (eventually_actual_child_parameters_from_target
    hm hdelta (one_div_pos.mpr hC0) hc0 (by linarith))
  have Hweak := G.wall_weak.eventually (gt_mem_nhds zero_lt_one)
  have Hinherit : ∀ᶠ n in atTop, comparisonLowerScale (G.wall n).data.N
      (G.wall n).data.E (G.wall n).data.d ≤ actualChildCutoff (dim n+1)
        (m/10000) c0 (G.wall n).data.d (G.wall n).lam (G.wall n).xs := by
    filter_upwards [Hparam, Hweak, G.wall_target] with n hn hnWeak hnTarget
    have hlo : (1/C0)*((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(G.wall n).data.d ≤
        (G.wall n).data.E := by
      calc
        _ = (((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(G.wall n).data.d)/C0 := by ring
        _ ≤ _ := (div_le_iff₀ hC0).mpr
          ((G.wall n).hlower.trans_eq (mul_comm C0 (G.wall n).data.E))
    have hup : (G.wall n).data.E ≤ (G.wall n).data.d^2/
        Real.sqrt ((dim n+1:ℕ):ℝ) :=
      (le_div_iff₀ (Real.sqrt_pos.mpr (G.wall n).data.hN)).mpr
        ((mul_comm (G.wall n).data.E (Real.sqrt (G.wall n).data.N)).trans_le
          (G.wall n).hupper)
    have hweak : laplaceComparisonStrength (G.wall n).data.d (G.wall n).lam
        (G.wall n).xs ≤ (G.wall n).xs^2 :=
      (div_le_one₀ (sq_pos_of_pos (G.wall n).hxs)).mp hnWeak.le
    exact (hn (G.wall n).data.d (G.wall n).lam (G.wall n).data.E (G.wall n).xs
      (G.wall n).data.hd (G.wall n).hlam (G.wall n).hld (G.wall n).data.hE
      (G.wall n).hxs hlo hup hnTarget hweak).2.2.2.1
  have Hfieldscale : ∀ᶠ n in atTop, (G.wall n).data.d^2 ≤ comparisonLowerScale
      (G.root n).context.N (G.root n).context.E (G.root n).context.d := by
    filter_upwards [G.error, G.radius, Hinherit, Hcut] with n hnE hnd hnIn hnCut
    have Hnum := NativeOverlapMinimum.concrete_wall_square_strength_le_lower_scale
      hmsmall (by omega : 0 < dim n+1)
    rw [←hnd, ←hnE] at Hnum
    exact Hnum.trans (hnIn.trans hnCut)
  exact ⟨G.wall_cut, Hcut, Hfieldscale⟩

theorem root_field_budget (G : OriginalQHighOnlyHistory M T c0)
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hdim : Tendsto dim atTop atTop) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ᶠ n in atTop, ∀ u ∈ Icc (0:ℝ) 1,
      (G.root n).h u ≤ Cf*(comparisonLowerScale
        (G.root n).context.N (G.root n).context.E (G.root n).context.d+u) := by
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [G.field, (G.root_cutoff_gates hm hmsmall hC0 hc0 hdim).2.2]
    with n hnh hn u hu
  rw [hnh, one_mul]
  exact ((G.wall n).changed_field_le_selected_strength hu).trans
    ((G.wall n).hld.trans (by linarith only [hn, hu.1]))

theorem root_all_profile_pullback (G : OriginalQHighOnlyHistory M T c0) :
    ∀ᶠ n in atTop, ∀ child : ActualHighOnlyComparisonData (dim n+1) (m/10000),
      ∀ alpha : child.Profile, child.s = (G.root n).data.s →
        NativePullbackClockRegularity alpha.val.val (G.root n).b (G.root n).h 0 1 := by
  filter_upwards [G.same_mass, G.bare, G.field] with n hns hnb hnh child alpha ha
  have hsame : child.s = (G.wall n).data.s := ha.trans hns
  have HB : (G.root n).b = (G.wall n).changedBare := funext hnb
  have HH : (G.root n).h = (G.wall n).changedField := funext hnh
  rw [HB, HH]
  exact (G.wall n).changed_pullback_on_high_only_profile child alpha hsame

theorem eventually_mass_below_child_cutoff
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hAz : 0≤Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hdim : Tendsto dim atTop atTop)
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock}
    (G : OriginalQHighOnlyHistory M T c0)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).context.N
      (m/10000) (M n).context.E (M n).lam≤(M n).xs)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0)) :
    ∀ᶠn in atTop,(M n).data.s≤actualChildCutoff (dim n+1) (m/10000)
      c0 (M n).context.d (M n).lam (M n).xs := by
  obtain ⟨HwallMass, HfirstCut, _⟩ := G.root_cutoff_gates hm hmsmall hC0 hc0 hdim
  have hdelta : 0 < m/10000 := by positivity
  have hmargin : (m/10000)/4 < 3*m-99*(m/10000) := by linarith
  have hcapmargin : 100*(m/10000) < (1:ℝ)/3+m := by linarith
  have Hdim : Tendsto (fun n=>dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  have Hparam := Hdim.eventually
    (eventually_actual_child_parameters_from_target hm hdelta
      (one_div_pos.mpr hC0) hc0 hmargin)
  have HrootMass := HwallMass.eventually
    (eventually_le_nhds zero_lt_one)
  have Hcut := G.history.cutoff_inherits_root hm hdelta hAz hC0 hc0
    hmargin hcapmargin hdim
  have Hweak := hweak.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [G.history.same_omission,G.same_mass,HrootMass,HfirstCut,Hcut,Hparam,Hweak,htarget]
    with n hnS hnSame hnMass hnFirstCut hnCut hnParam hnWeak hnTarget
  have hwallCut : 0 < actualChildCutoff (dim n+1) (m/10000) c0
      (G.wall n).data.d (G.wall n).lam (G.wall n).xs :=
    (actual_child_cutoff_pos_le_radius (G.wall n).data.hN hc0
      (G.wall n).hlam (G.wall n).hxs).1
  have hsRoot : (G.root n).data.s≤comparisonLowerScale
      (G.root n).context.N (G.root n).context.E (G.root n).context.d := by
    rw [hnSame]
    exact ((div_le_one₀ hwallCut).mp hnMass).trans hnFirstCut
  have hweakPoint : laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs≤(M n).xs^2 :=
    (div_le_one₀ (sq_pos_of_pos (M n).hxs)).mp hnWeak.le
  have hlo : (1/C0)*((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*
      (M n).context.d≤(M n).context.E := by
    calc
      _ = (((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(M n).context.d)/C0 := by ring
      _ ≤ _ := (div_le_iff₀ hC0).mpr
        ((M n).hlower.trans_eq (mul_comm C0 (M n).context.E))
  have hup : (M n).context.E≤(M n).context.d^2/
      Real.sqrt ((dim n+1:ℕ):ℝ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr (M n).context.hN)).mpr
      ((mul_comm (M n).context.E (Real.sqrt (M n).context.N)).trans_le
        (M n).hupper)
  have hp := hnParam (M n).context.d (M n).lam (M n).context.E
    (M n).xs (M n).context.hd (M n).hlam (M n).hld
    (M n).context.hE (M n).hxs hlo hup hnTarget hweakPoint
  rw [hnS]
  exact hsRoot.trans (hnCut.trans hp.2.2.2.1)

theorem root_gap (G : OriginalQHighOnlyHistory M T c0)
    (heps : ∀ᶠ n in atTop, T/4 ≤ (G.wall n).data.epsilon)
    (hd : ∀ᶠ n in atTop, (G.wall n).data.d^2 ≤ T/8) :
    ∀ᶠ n in atTop, ∀ u ∈ Ico (0:ℝ) (G.root n).data.s,
      (G.root n).b u + T/8 ≤ (G.root n).b (G.root n).data.s :=
  ActualThetaZeroOverlapMinimum.eventually_first_high_only_root_gap
    G.wall G.root G.temperature heps hd G.same_mass G.bare

end OriginalQHighOnlyHistory
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

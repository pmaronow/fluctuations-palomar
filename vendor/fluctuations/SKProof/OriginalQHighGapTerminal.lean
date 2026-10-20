module

public import SKProof.OriginalQHighOnlySelector
public import SKProof.OriginalQHighOnlyFinitePropagation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal

namespace ActualHighOnlyOverlapMinimum
variable {m cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ → ℕ}

private structure HighGapHistory_original_q
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock) (T c0 : ℝ) where
  wall : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
    m (m/10000) cl cu Az C0 Ct D Bclock
  root : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
    m (m/10000) cl cu Az C0 Ct D Bclock
  history : ActualWeakHighOnlyHistoryChain c0 root M
  temperature : ∀ᶠ n in atTop, (wall n).data.T = T
  omission_zero : Tendsto (fun n => (wall n).data.s) atTop (𝓝 0)
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

namespace HighGapHistory_original_q
variable {M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
  m (m/10000) cl cu Az C0 Ct D Bclock}

private def comp_original_q (G : HighGapHistory_original_q M T c0)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    HighGapHistory_original_q (fun n => M (phi n)) T c0 where
  wall := fun n => G.wall (phi n)
  root := fun n => G.root (phi n)
  history := G.history.comp phi hphi.tendsto_atTop
  temperature := hphi.tendsto_atTop.eventually G.temperature
  omission_zero := G.omission_zero.comp hphi.tendsto_atTop
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

private def weaken_constants_original_q (G : HighGapHistory_original_q M T c0)
    {cl' cu' Az' Ct' D' Bclock' : ℝ}
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    HighGapHistory_original_q
      (fun n => (M n).weakenConstants hcl hcu hAz hCt hD hB) T c0 where
  wall := fun n => (G.wall n).weakenConstants hcl hcu hAz hCt hD hB
  root := fun n => (G.root n).weakenConstants hcl hcu hAz hCt hD hB
  history := G.history.weaken_constants hcl hcu hAz hCt hD hB
  temperature := G.temperature
  omission_zero := G.omission_zero
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

private def append_child_original_q (G : HighGapHistory_original_q M T c0)
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
    HighGapHistory_original_q Q T c0 where
  wall := G.wall
  root := G.root
  history := .child G.history x hx hxunit htarget hcap hweak hd hE hs hb hh
  temperature := G.temperature
  omission_zero := G.omission_zero
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

private def with_current_original_q (G : HighGapHistory_original_q M T c0)
    (Q : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (H : ActualWeakHighOnlyHistoryChain c0 G.root Q) :
    HighGapHistory_original_q Q T c0 where
  wall := G.wall
  root := G.root
  history := H
  temperature := G.temperature
  omission_zero := G.omission_zero
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

private theorem exists_context_original_q (G : HighGapHistory_original_q M T c0)
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

private theorem root_endpoint_cost_tendsto_zero_original_q (G : HighGapHistory_original_q M T c0)
    (_hmsmall : m ≤ (1:ℝ)/120) (_hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => comparisonEndpointL1Cost T (G.root n).b (G.root n).h)
      atTop (𝓝 0) :=
  ActualThetaZeroOverlapMinimum.high_only_root_endpoint_cost_tendsto_zero
    G.wall G.root G.temperature G.omission_zero G.wall_unit
    G.wall_weak G.bare G.field

private theorem endpoint_cost_tendsto_zero_original_q (G : HighGapHistory_original_q M T c0)
    (_hmsmall : m ≤ (1:ℝ)/120) (_hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0) :=
  G.history.endpoint_cost_tendsto_zero (G.root_endpoint_cost_tendsto_zero_original_q _hmsmall _hdim)

private theorem same_omission_original_q (G : HighGapHistory_original_q M T c0) :
    ∀ᶠ n in atTop, (M n).data.s = (G.wall n).data.s := by
  filter_upwards [G.history.same_omission, G.same_mass] with n hn hr
  exact hn.trans hr

private theorem omission_tendsto_zero_original_q (G : HighGapHistory_original_q M T c0)
    (_hmsmall : m ≤ (1:ℝ)/120) (_hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => (M n).data.s) atTop (𝓝 0) :=
  G.omission_zero.congr' (G.same_omission_original_q.mono (fun _ hn=>hn.symm))

private theorem total_root_original_q (G : HighGapHistory_original_q M T c0) :
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

private theorem first_cutoff_original_q (G : HighGapHistory_original_q M T c0) :
    ∀ᶠ n in atTop, actualChildCutoff (dim n+1) (m/10000) c0
      (G.wall n).data.d (G.wall n).lam (G.wall n).xs ≤
        comparisonLowerScale (G.root n).context.N
          (G.root n).context.E (G.root n).context.d := by
  filter_upwards [G.first_radius, G.first_error] with n hnd hnE
  simp only [comparisonLowerScale, ActualHighOnlyComparisonData.N,
    hnd, hnE, actualChildCutoff]
  exact le_rfl

private theorem root_all_profile_pullback_original_q (G : HighGapHistory_original_q M T c0) :
    ∀ᶠ n in atTop, ∀ child : ActualHighOnlyComparisonData (dim n+1) (m/10000),
      ∀ alpha : child.Profile, child.s = (G.root n).data.s →
        NativePullbackClockRegularity alpha.val.val (G.root n).b (G.root n).h 0 1 := by
  filter_upwards [G.same_mass, G.bare, G.field] with n hns hnb hnh child alpha ha
  have hsame : child.s = (G.wall n).data.s := ha.trans hns
  have HB : (G.root n).b = (G.wall n).changedBare := funext hnb
  have HH : (G.root n).h = (G.wall n).changedField := funext hnh
  rw [HB, HH]
  exact (G.wall n).changed_pullback_on_high_only_profile child alpha hsame

private theorem eventually_mass_below_child_cutoff_original_q
    (hm : 0 < m) (_hmsmall : m ≤ (1:ℝ)/120) (hAz : 0≤Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hdim : Tendsto dim atTop atTop)
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock}
    (G : HighGapHistory_original_q M T c0)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).context.N
      (m/10000) (M n).context.E (M n).lam≤(M n).xs)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0)) :
    ∀ᶠn in atTop,(M n).data.s≤actualChildCutoff (dim n+1) (m/10000)
      c0 (M n).context.d (M n).lam (M n).xs := by
  have HwallMass := G.wall_cut
  have HfirstCut := G.first_cutoff_original_q
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

private theorem root_gap_original_q (G : HighGapHistory_original_q M T c0)
    (heps : ∀ᶠ n in atTop, T/4 ≤ (G.wall n).data.epsilon)
    (hd : ∀ᶠ n in atTop, (G.wall n).data.d^2 ≤ T/8) :
    ∀ᶠ n in atTop, ∀ u ∈ Ico (0:ℝ) (G.root n).data.s,
      (G.root n).b u + T/8 ≤ (G.root n).b (G.root n).data.s :=
  ActualThetaZeroOverlapMinimum.eventually_first_high_only_root_gap
    G.wall G.root G.temperature heps hd G.same_mass G.bare

end HighGapHistory_original_q

set_option maxHeartbeats 26000000 in
private theorem eventually_bad_parent_excludes_successful_child_sequence_terminal_original_q
    {m cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (G : HighGapHistory_original_q M T c0)
    (a : (n : ℕ) → ActualHighOnlyChildBarrierCall (dim n+1) (m/10000))
    (x : ℕ → ℝ) (hxs : ∀ n, (M n).xs ≤ x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀ n, (a n).context = (M n).context)
    (hlam : ∀ n, (a n).lam = (M n).lam)
    (hR : ∀ n, (a n).R = (M n).R)
    (hchild : ∀ᶠ n in atTop, (a n).childRadius = c0*x n ∧
      (a n).childLam = (c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
        (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (x n))
    (hEchild : ∀ᶠ n in atTop, (a n).childData.E = actualChildErrorBudget
      (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (x n))
    (htarget : ∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N
      (m/10000) (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n => laplaceComparisonStrength (M n).context.d
      (M n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (Hbad : ∀ᶠ n in atTop, ¬(cl*x n ≤ (M n).alpha.val.val (x n) ∧
      (M n).alpha.val.val (x n) ≤ cu*x n)) : False := by
  let delta : ℝ := m/10000
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hroom : delta < 3*m := by dsimp [delta]; linarith
  have hmargin : delta/4 < 3*m-99*delta := by dsimp [delta]; linarith
  have hcapmargin : 100*delta < (1:ℝ)/3+m := by dsimp [delta]; linarith
  have hgapmargin : 0 < 9*m-298*delta := by dsimp [delta]; linarith
  have HMlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n=>(M n).hxs.le) hxs hxlim
  obtain ⟨Gm⟩ := G.exists_context_original_q hm hmsmall hcl hAz hC0 hc0 hc01 hdim HMlim
  have homission : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>div_nonneg (M n).data.hs.1
      ((M n).hxs.trans_le (hxs n)).le) _ Gm.omission_ratio
    intro n
    exact div_le_div_of_nonneg_left (M n).data.hs.1
      (div_pos (mul_pos (Real.sqrt_pos.mpr (M n).context.hN)
        (M n).context.hE) (M n).context.hd)
      ((M n).hscale.trans (hxs n))
  have hx (n:ℕ) : 0 < x n := (M n).hxs.trans_le (hxs n)
  have hcl1 : cl≤1 := by
    have H1:=((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).1
    simpa only [mul_one,(M 0).alpha.property.2] using H1
  have hcu1 : 1≤cu := by
    have H1:=((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).2
    simpa only [mul_one,(M 0).alpha.property.2] using H1
  have hparent (n:ℕ) : (a n).context.E=(M n).context.E ∧
      (a n).context.d=(M n).context.d ∧ (a n).lam=(M n).lam ∧
      (a n).R=(M n).R ∧ (a n).context.s=(M n).context.s := by
    refine ⟨?_,?_,hlam n,hR n,?_⟩  <;> rw [hcontext n]
  have hcoeff (n:ℕ) (u:ℝ) : (a n).coefficient u=(M n).coefficient u := by
    change omittedStrengthCoefficient (a n).context.d (a n).context.s
      (a n).R (a n).lam u = omittedStrengthCoefficient
        (M n).context.d (M n).context.s (M n).R (M n).lam u
    rw [hcontext n,hlam n,hR n]
  have hschild (n:ℕ) : (a n).childData.s=(M n).data.s := by
    rw [(a n).sameInitialMass,hcontext n]
  have hbchild (n:ℕ) (u:ℝ) : (a n).childData.b u=
      (M n).b u-(M n).coefficient u := by
    have H:=congrFun (a n).childBareMatrix u
    change (a n).childData.b u=(a n).context.b u-(a n).coefficient u at H
    rw [hcontext n,hcoeff n u] at H
    exact H
  have hhchild (n:ℕ) (u:ℝ) : (a n).childData.h u=
      (M n).h u+(M n).coefficient u*(M n).R u := by
    have H:=congrFun (a n).childBareField u
    change (a n).childData.h u=(a n).context.h u+
      (a n).coefficient u*(a n).R u at H
    rw [hcontext n,hcoeff n u,hR n] at H
    exact H
  have Htotal := G.total_root_original_q
  have htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,
      (a n).childData.h u+(a n).childData.b u≤ max Bclock T := by
    filter_upwards [Htotal] with n hn u hu
    rw [hbchild n u,hhchild n u,
      ←((M n).inherited_clock_coe hu).1,
      ←((M n).inherited_clock_coe hu).2]
    exact ((M n).inherited_total_clock_le hn.1 u hu).trans (le_max_right _ _)
  obtain ⟨Cold,hCold,HquantOld⟩:=actual_high_only_successful_child_outer_radius_bounds
    hm hdelta hcl hcu hAz hC0 hc0 dim hdim M a x hxs hxlim hparent hchild homission hweak
  let C:=max Cold (cl*Az/4)
  have hC : 1≤C:=hCold.trans (le_max_left _ _)
  have hAzC : Az≤4*C/cl := by
    apply (le_div_iff₀ hcl).mpr
    have H:=le_max_right Cold (cl*Az/4)
    nlinarith only [H]
  have hquant : ∀ᶠn in atTop,∀u∈Icc (C*x n) 1,
      u/(4*cu)≤(a n).Z u ∧ (a n).Z u≤4*u/cl := by
    filter_upwards [HquantOld] with n hn u hu
    exact hn u ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _) (hx n).le).trans hu.1,hu.2⟩
  have Hdim : Tendsto (fun n=>dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  have Hparam:=Hdim.eventually (eventually_actual_child_parameters_from_target
    hm hdelta (one_div_pos.mpr hC0) hc0 hmargin)
  have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
  have Hunit:=hxlim.eventually (eventually_le_nhds zero_lt_one)
  have hready : ∀ᶠn in atTop,
      (a n).childRadius=c0*x n ∧
      (a n).childLam=(c0*x n)^2 ∧
      (a n).childData.E=actualChildErrorBudget (dim n+1) delta c0
        (M n).context.d (M n).lam (x n) ∧
      (a n).childRadius≤ max D 1 ∧
      Real.sqrt ((dim n+1:ℕ):ℝ)*(a n).childData.E≤(a n).childRadius^2 ∧
      ((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(a n).childRadius≤C0*(a n).childData.E ∧
      (∀u∈Icc (0:ℝ) 1,(a n).childData.h u+(a n).childData.b u≤ max Bclock T) ∧
      (∀u∈Icc (C*x n) 1,u/(4*cu)≤(a n).Z u ∧ (a n).Z u≤4*u/cl) := by
    filter_upwards [hchild,hEchild,Hparam,Hweak,Hunit,htarget,htotal,hquant]
      with n hnChild hnE hnParam hnWeak hnUnit hnTarget hnTotal hnQuant
    have hlo : (1/C0)*((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*
        (M n).context.d≤(M n).context.E := by
      calc
        _ = (((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(M n).context.d)/C0 := by ring
        _ ≤ _ := (div_le_iff₀ hC0).mpr
          ((M n).hlower.trans_eq (mul_comm C0 (M n).context.E))
    have hup : (M n).context.E≤(M n).context.d^2/
        Real.sqrt ((dim n+1:ℕ):ℝ) :=
      (le_div_iff₀ (Real.sqrt_pos.mpr (M n).context.hN)).mpr
        (by simpa only [mul_comm] using (M n).hupper)
    have hparentweak : laplaceComparisonStrength (M n).context.d
        (M n).lam (x n)≤(x n)^2 :=
      (div_le_one₀ (sq_pos_of_pos (hx n))).mp hnWeak.le
    have HP:=hnParam (M n).context.d (M n).lam (M n).context.E (x n)
      (M n).context.hd (M n).hlam (M n).hld (M n).context.hE
      (hx n) hlo hup hnTarget hparentweak
    have hupper : Real.sqrt ((dim n+1:ℕ):ℝ)*(a n).childData.E≤
        (a n).childRadius^2 := by
      have H:=(le_div_iff₀ (Real.sqrt_pos.mpr (M n).context.hN)).mp HP.2.1
      rw [hnE,hnChild.1]
      simpa only [actualChildRadius,mul_comm] using H
    have hlower : ((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(a n).childRadius≤
        C0*(a n).childData.E := by
      have H:=mul_le_mul_of_nonneg_left HP.1 hC0.le
      have hcanc : C0*(1/C0)=1 := by field_simp
      rw [hnE,hnChild.1]
      simpa only [←mul_assoc,hcanc,one_mul,actualChildRadius] using H
    have hdD : (a n).childRadius≤ max D 1 := by
      rw [hnChild.1]
      have H:=(mul_le_mul_of_nonneg_right hc01 (hx n).le).trans
        (by simpa using hnUnit)
      exact H.trans (le_max_right _ _)
    exact ⟨hnChild.1,hnChild.2.1,hnE,hdD,hupper,hlower,hnTotal,hnQuant⟩
  obtain ⟨N,hN⟩:=eventually_atTop.mp hready
  let shift : ℕ→ℕ:=fun n=>n+N
  have hshift : StrictMono shift:=fun i j hij=>Nat.add_lt_add_right hij N
  have Hn (n:ℕ) := hN (shift n) (by dsimp [shift];omega)
  obtain ⟨Q,hQ⟩:=ActualHighOnlyChildBarrierCall.exists_regular_successful_child_sequence
    hc0 hc01 hcl hcu hcl1 hcu1 hC (le_max_right Ct 1)
    (fun n=>dim (shift n)) (fun n=>a (shift n)) (fun n=>x (shift n))
    (fun n=>hx (shift n))
    (fun n=>(Hn n).1)
    (fun n=>by rw [(Hn n).1];exact (Hn n).2.1)
    (fun n=>(Hn n).2.2.2.1)
    (fun n=>(Hn n).2.2.2.2.1)
    (fun n=>(Hn n).2.2.2.2.2.1)
    (fun n=>(Hn n).2.2.2.2.2.2.1)
    (fun n=>(Hn n).2.2.2.2.2.2.2)
  have hQxs (n:ℕ) : (Q n).xs=x (shift n):=(hQ n).2.2.1
  have hQd (n:ℕ) : (Q n).context.d=c0*x (shift n) := by
    rw [(hQ n).1]
    exact (Hn n).1
  have hQlam (n:ℕ) : (Q n).lam=(c0*x (shift n))^2 := by
    rw [(hQ n).2.2.2]
    exact (Hn n).2.1
  have hQE : ∀n,(Q n).context.E=actualChildErrorBudget
      (dim (shift n)+1) delta c0 (M (shift n)).context.d
      (M (shift n)).lam (x (shift n)) := by
    intro n
    rw [(hQ n).1]
    exact (Hn n).2.2.1
  have hQs : ∀n,(Q n).data.s=(M (shift n)).data.s := by
    intro n
    change (Q n).context.s=(M (shift n)).data.s
    rw [(hQ n).1]
    exact hschild (shift n)
  have hQb : ∀n,∀u,(Q n).b u=(M (shift n)).b u-
      (M (shift n)).coefficient u := by
    intro n u
    change (Q n).context.b u=(M (shift n)).b u-(M (shift n)).coefficient u
    rw [(hQ n).1]
    exact hbchild (shift n) u
  have hQh : ∀n,∀u,(Q n).h u=(M (shift n)).h u+
      (M (shift n)).coefficient u*(M (shift n)).R u := by
    intro n u
    change (Q n).context.h u=(M (shift n)).h u+
      (M (shift n)).coefficient u*(M (shift n)).R u
    rw [(hQ n).1]
    exact hhchild (shift n) u
  have hclW : cl/4 ≤ cl := by linarith
  have hcuW : cu ≤ 4*cu := by linarith
  let G0 := G.comp_original_q shift hshift
  let Gw := G0.weaken_constants_original_q hclW hcuW hAzC
    (le_max_left Ct 1) (le_max_left D 1) (le_max_left Bclock T)
  have hcapW : ∀ᶠn in atTop,(M (shift n)).z ≤ (4*C/cl)*x (shift n) := by
    apply Eventually.of_forall
    intro n
    exact (M (shift n)).hzxs.trans
      ((mul_le_mul_of_nonneg_left (hxs (shift n)) hAz).trans
        (mul_le_mul_of_nonneg_right hAzC (hx (shift n)).le))
  let Gchild := Gw.append_child_original_q Q (fun n=>x (shift n))
    (fun n=>hx (shift n))
    ((hxlim.comp hshift.tendsto_atTop).eventually (eventually_le_nhds zero_lt_one))
    (hshift.tendsto_atTop.eventually htarget) hcapW
    (hweak.comp hshift.tendsto_atTop)
    (Eventually.of_forall hQd) (Eventually.of_forall hQE)
    (Eventually.of_forall hQs) (Eventually.of_forall hQb) (Eventually.of_forall hQh)
  have hQlim : Tendsto (fun n=>(Q n).xs) atTop (𝓝 0) := by
    simpa only [hQxs,Function.comp_def] using hxlim.comp hshift.tendsto_atTop
  obtain ⟨GQ⟩ := Gchild.exists_context_original_q hm hmsmall
    (by positivity) (by positivity) hC0 hc0 hc01
    (hdim.comp hshift.tendsto_atTop) hQlim
  have hparent0 (n:ℕ) : (a (shift n)).context.E=(M (shift n)).context.E ∧
      (a (shift n)).context.d=(M (shift n)).context.d ∧
      (a (shift n)).lam=(M (shift n)).lam ∧
      (a (shift n)).R=(M (shift n)).R ∧
      (a (shift n)).context.s=(M (shift n)).context.s := hparent (shift n)
  have hQjoin (n:ℕ) : (Q n).R=(a (shift n)).Z ∧
      (Q n).xs=x (shift n) ∧ (Q n).context.d=c0*x (shift n) ∧
      (Q n).lam=(c0*x (shift n))^2 :=
    ⟨(hQ n).2.1,hQxs n,hQd n,hQlam n⟩
  obtain ⟨phi,hphi,kappa,hklo,hkup,Hprofile,Hstrict⟩:=
    successful_child_parent_direct_profile_of_context hm hdelta hroom hcl hcu
      hAz hC0 hc0 hc01 hC hmargin hcapmargin hgapmargin
      hclmargin hcumargin (fun n=>dim (shift n))
      (hdim.comp hshift.tendsto_atTop) (fun n=>M (shift n))
      (fun n=>a (shift n)) Q GQ (fun n=>x (shift n))
      (fun n=>hxs (shift n)) (hxlim.comp hshift.tendsto_atTop)
      hparent0 (hshift.tendsto_atTop.eventually hchild)
      (homission.comp hshift.tendsto_atTop)
      (hweak.comp hshift.tendsto_atTop) hQjoin
  have Hbad0:=hphi.tendsto_atTop.eventually
    (hshift.tendsto_atTop.eventually Hbad)
  obtain ⟨n,hn⟩:=(Hstrict.and Hbad0).exists
  exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩

set_option maxHeartbeats 24000000 in
private theorem eventually_shrinking_bad_parent_macro_child_cost_failure_terminal_original_q
    {m cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (G : HighGapHistory_original_q M T c0)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (htarget : ∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N
      (m/10000) (M n).context.E (M n).lam ≤ (M n).xs)
    (hweak : Tendsto (fun n => laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0))
    (hroomChild : ∀ᶠ n in atTop, (M n).lam+(c0*(M n).xs)^2 ≤ (M n).b (M n).data.s)
    (hcross : ∀ᶠ n in atTop, ∀ u ∈ Ico (0:ℝ) (M n).data.s,
      (M n).b u+(M n).lam+(c0*(M n).xs)^2 ≤ (M n).b (M n).data.s)
    (Hbad : ∀ᶠ n in atTop, ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) :
    ∀ᶠ n in atTop, ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
      (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs <
        (M n).macroChildSweepCost hc0 := by
  let delta : ℝ := m/10000
  classical
  by_contra Hfailure
  have Hfreq : ∃ᶠn in atTop,
      (M n).macroChildSweepCost hc0 ≤
        ((dim n+1:ℕ):ℝ)^(20*delta)*actualChildErrorBudget (dim n+1)
          delta c0 (M n).context.d (M n).lam (M n).xs := by
    simpa only [Filter.Frequently,not_le,delta] using Hfailure
  obtain ⟨phi,hphi,Hphi⟩ := extraction_of_frequently_atTop
    (Hfreq.and_eventually (hroomChild.and hcross))
  have Hfactory (n : ℕ) :
      ∃a : ActualHighOnlyChildBarrierCall (dim (phi n)+1) delta,
        a.context=(M (phi n)).context ∧
        a.lam=(M (phi n)).lam ∧ a.R=(M (phi n)).R ∧
        a.childRadius=c0*(M (phi n)).xs ∧
        a.childLam=(c0*(M (phi n)).xs)^2 ∧
        a.childData.E=actualChildErrorBudget (dim (phi n)+1) delta c0
          (M (phi n)).context.d (M (phi n)).lam (M (phi n)).xs ∧
        a.childData.s=(M (phi n)).data.s ∧
        a.childData.b=(fun u=>(M (phi n)).b u-(M (phi n)).coefficient u) ∧
        a.childData.h=(fun u=>(M (phi n)).h u+
          (M (phi n)).coefficient u*(M (phi n)).R u) ∧
        a.err=(M (phi n)).macroChildSweepCost hc0 :=
    exists_actual_high_only_macro_child_at_parent_with_budget
      (M (phi n)) hc0 (Hphi n).2.1 (Hphi n).2.2
  choose a haCtx haLam haR haD haChildLam haE haS haB haH haErr
    using Hfactory
  have hparent (n : ℕ) :
      (a n).context.E=(M (phi n)).context.E ∧
      (a n).context.d=(M (phi n)).context.d ∧
      (a n).lam=(M (phi n)).lam ∧
      (a n).R=(M (phi n)).R ∧
      (a n).context.s=(M (phi n)).context.s := by
    refine ⟨?_,?_,haLam n,haR n,?_⟩  <;> rw [haCtx n]
  have hchild : ∀ᶠn in atTop,
      (a n).childRadius=c0*(M (phi n)).xs ∧
      (a n).childLam=(c0*(M (phi n)).xs)^2 ∧
      (a n).err≤((dim (phi n)+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim (phi n)+1) delta c0
          (M (phi n)).context.d (M (phi n)).lam (M (phi n)).xs :=
    Eventually.of_forall (fun n=>⟨haD n,haChildLam n,by
      rw [haErr n]
      exact (Hphi n).1⟩)
  exact eventually_bad_parent_excludes_successful_child_sequence_terminal_original_q
    hm hmsmall hcl hcu hAz hC0 hc0 hc01 hclmargin hcumargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp_original_q phi hphi) a (fun n=>(M (phi n)).xs)
    (fun _=>le_rfl) (hxlim.comp hphi.tendsto_atTop)
    haCtx haLam haR hchild (Eventually.of_forall haE)
    (hphi.tendsto_atTop.eventually htarget)
    (hweak.comp hphi.tendsto_atTop)
    (hphi.tendsto_atTop.eventually Hbad)

set_option maxHeartbeats 26000000 in
private theorem exists_bad_parent_sharp_child_cost_failure_constants_terminal_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 Ct D Bclock c0 : ℝ,
        0 < m → m ≤ (1:ℝ)/120 → 0 < cl → 0 < cu → 0 ≤ Az → 0 < C0 →
        ∀ hc0 : 0 < c0, c0 ≤ 1 → cl ≤ lower → upper ≤ cu →
        cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
        ∀ M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 Ct D Bclock,
        HighGapHistory_original_q M ((beta:ℝ)^2) c0 →
        (∀ n, (M n).xs ≤ 1) →
        (∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N (m/10000)
          (M n).context.E (M n).lam ≤ (M n).xs) →
        Tendsto (fun n => laplaceComparisonStrength (M n).context.d
          (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) →
        (∀ᶠ n in atTop, (M n).lam+(c0*(M n).xs)^2 ≤ (M n).b (M n).data.s) →
        (∀ᶠ n in atTop, ∀ u ∈ Ico (0:ℝ) (M n).data.s,
          (M n).b u+(M n).lam+(c0*(M n).xs)^2 ≤ (M n).b (M n).data.s) →
        (∀ᶠ n in atTop, ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
          (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) →
        ∀ᶠ n in atTop, ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
          (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs <
            (M n).macroChildSweepCost hc0 := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hmacro⟩ :=
    exists_macro_bad_parent_child_cost_failure_constants hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu Az C0 Ct D Bclock c0 hm hmsmall hcl hcu hAz hC0 hc0 hc01
    hclMacro hcuMacro hclSlack hcuSlack dim hdim M G hunit htarget hweak
    hroomChild hcross Hbad
  have hdelta : 0 < m/10000 := by positivity
  by_contra Hnone
  have Hfreq : ∃ᶠ n in atTop, (M n).macroChildSweepCost hc0 ≤
      ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
        (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs := by
    simpa only [Filter.Frequently, not_le] using Hnone
  obtain ⟨phi, hphi, Hphi⟩ := extraction_of_frequently_atTop Hfreq
  let x := fun n => (M (phi n)).xs
  by_cases HX : Tendsto x atTop (𝓝 0)
  · have Hfailure := eventually_shrinking_bad_parent_macro_child_cost_failure_terminal_original_q
      hm hmsmall hcl hcu hAz hC0 hc0 hc01 hclSlack hcuSlack
      (fun n => dim (phi n)) (hdim.comp hphi.tendsto_atTop)
      (fun n => M (phi n)) (G.comp_original_q phi hphi) HX
      (hphi.tendsto_atTop.eventually htarget) (hweak.comp hphi.tendsto_atTop)
      (hphi.tendsto_atTop.eventually hroomChild) (hphi.tendsto_atTop.eventually hcross)
      (hphi.tendsto_atTop.eventually Hbad)
    obtain ⟨n, hn⟩ := Hfailure.exists
    exact (not_lt_of_ge (Hphi n)) hn
  · obtain ⟨xlo, hxlo, psi, hpsi, Hpsi⟩ :=
      exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero
        x (fun n => (M (phi n)).hxs.le) HX
    let sigma := phi ∘ psi
    have hsigma : StrictMono sigma := hphi.comp hpsi
    have hc0Temp : c0^2 < (beta:ℝ)^2 := by
      have H := pow_le_pow_left₀ hc0.le hc01 2
      norm_num only [one_pow] at H
      exact H.trans_lt hTemp
    have Hfailure := Hmacro m (m/10000) cl cu Az C0 Ct D Bclock c0
      hm hdelta hC0 hc0 hc0Temp hclMacro hcuMacro
      (fun n => dim (sigma n)) (hdim.comp hsigma.tendsto_atTop)
      (fun n => M (sigma n)) xlo hxlo
      (fun n => ⟨Hpsi n, hunit (sigma n)⟩)
      ((G.omission_tendsto_zero_original_q hmsmall hdim).comp hsigma.tendsto_atTop)
      (hweak.comp hsigma.tendsto_atTop)
      (hsigma.tendsto_atTop.eventually hroomChild)
      (hsigma.tendsto_atTop.eventually hcross)
      ((G.endpoint_cost_tendsto_zero_original_q hmsmall hdim).comp hsigma.tendsto_atTop)
      (hsigma.tendsto_atTop.eventually Hbad)
    obtain ⟨n, hn⟩ := Hfailure.exists
    exact (not_lt_of_ge (Hphi (psi n))) hn

private theorem exists_high_only_history_bad_test_strength_saving_terminal_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 Ct D Bclock c0 : ℝ,
        0 < m → m ≤ (1:ℝ)/120 → 0 < cl → 0 < cu → 0 ≤ Az →
        0 < C0 → 0 ≤ Ct → D ≤ 1 → 0 < c0 → c0 ≤ 1 →
        cl ≤ lower → upper ≤ cu →
        cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
        ∀ M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 Ct D Bclock,
        HighGapHistory_original_q M ((beta:ℝ)^2) c0 →
        (∀ n, (M n).xs ≤ 1) →
        (∀ᶠ n in atTop,
          ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
            (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) →
        Tendsto (fun n => laplaceComparisonStrength (M n).context.d
          (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) := by
  obtain ⟨lower, upper, hlower, hupper, H⟩ :=
    exists_theta_zero_high_only_history_bad_test_strength_saving hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu Az C0 Ct D Bclock c0 hm hmsmall hcl hcu hAz hC0 hCt hD
    hc0 hc01 hclMacro hcuMacro hclSlack hcuSlack dim hdim M G hunit Hbad
  have hdelta : 0 < m/10000 := by positivity
  have hroom : m/10000 < 3*m := by linarith
  have hmargin : (m/10000)/4 < 3*m-99*(m/10000) := by linarith
  have hcapmargin : 100*(m/10000) < (1:ℝ)/3+m := by linarith
  have hgapmargin : 0 < 9*m-298*(m/10000) := by linarith
  have Hcut := G.wall_cut
  have HfirstCut := G.first_cutoff_original_q
  exact H m (m/10000) cl cu Az C0 Ct D Bclock c0
    hm hdelta hroom hcl hcu hAz hC0 hCt hD hc0 hc01
    hmargin hcapmargin hgapmargin hclMacro hcuMacro hclSlack hcuSlack
    dim hdim G.wall G.root M G.history G.temperature G.same_mass
    G.wall_unit G.wall_target G.wall_weak Hcut HfirstCut G.bare G.field
    (G.omission_tendsto_zero_original_q hmsmall hdim)
    (G.root_endpoint_cost_tendsto_zero_original_q hmsmall hdim) hunit Hbad

private theorem HighGapHistory_original_q.eventually_select_bad_child_of_sharp_failure_terminal_original_q
    {m cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ→ℕ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl≤cu)
    (hAz : 2≤Az) (hCt : 1≤Ct) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0≤1) (hc0D : c0≤D) (hTB : T≤Bclock)
    (hdim : Tendsto dim atTop atTop)
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock}
    (G : HighGapHistory_original_q M T c0)
    (hxsunit : ∀n,(M n).xs≤1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).context.N
      (m/10000) (M n).context.E (M n).lam≤(M n).xs)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0))
    (hroomChild : ∀ᶠn in atTop,
      (M n).lam+(c0*(M n).xs)^2≤(M n).b (M n).data.s)
    (hcross : ∀ᶠn in atTop,∀u∈Ico (0:ℝ) (M n).data.s,
      (M n).b u+(M n).lam+(c0*(M n).xs)^2≤
        (M n).b (M n).data.s)
    (hcost : ∀ᶠn in atTop,
      ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
        (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs <
          (M n).macroChildSweepCost hc0) :
    ∀ᶠn in atTop,
      ∃Q : ActualHighOnlyOverlapMinimum (dim n+1)
        m (m/10000) cl cu Az C0 Ct D Bclock,
        Q.context.d=c0*(M n).xs ∧
        Q.context.E=actualChildErrorBudget (dim n+1)
          (m/10000) c0 (M n).context.d (M n).lam (M n).xs ∧
        (M n).context.N^((m/10000)/4)*(M n).context.E≤Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N (m/10000)
          Q.context.E Q.lam) 1 ∧
        (Q.alpha.val.val Q.xs < cl*Q.xs ∨
          cu*Q.xs < Q.alpha.val.val Q.xs) ∧
        Q.data.s=(M n).data.s ∧
        Q.b=(fun u=>(M n).b u-(M n).coefficient u) ∧
        Q.h=(fun u=>(M n).h u+(M n).coefficient u*(M n).R u) := by
  have hdelta : 0 < m/10000 := by positivity
  have hroom : m/10000 < 3*m := by linarith
  have hmargin : (m/10000)/4 < 3*m-99*(m/10000) := by linarith
  have Hselector := hdim.eventually
    (eventually_exists_selected_bad_child_of_sharp_failure
      (D:=D) (Bclock:=Bclock) hm hdelta
      hroom hcl hcu hclcu hAz hCt hC0 hc0 hmargin)
  have Hmass := G.eventually_mass_below_child_cutoff_original_q
    hm hmsmall (by linarith : 0≤Az) hC0 hc0 hdim htarget hweak
  have Hclock := G.history.child_pullback_all_profiles G.root_all_profile_pullback_original_q
  have Htotal := G.total_root_original_q
  have Hs4 : ∀ᶠn in atTop,(G.root n).data.s≤1/4 := by
    have Hs := G.omission_zero.eventually
      (eventually_le_nhds (show (0:ℝ)<1/4 by norm_num))
    filter_upwards [G.same_mass, Hs] with n hn hs
    rw [hn]
    exact hs
  have Hweak := hweak.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [Hselector,Hmass,Hclock,Htotal,G.history.same_omission,
    Hs4,hroomChild,hcross,hcost,htarget,Hweak]
    with n hnSelect hnMass hnClock hnTotal hnSame hnS4 hnRoom hnCross
      hnCost hnTarget hnWeak
  let child := (M n).data.childData (M n).alpha
    (Echild:=actualChildErrorBudget (dim n+1) (m/10000) c0
      (M n).data.d (M n).lam (M n).xs)
    (dchild:=c0*(M n).xs) (M n).lam_mem
    (actual_child_budget_pos (M n).data.hN hc0 (M n).hlam (M n).hxs)
    (mul_pos hc0 (M n).hxs) hnRoom hnCross
  have hchild1 : c0*(M n).xs≤1 := by
    have H := mul_le_mul_of_nonneg_right hc01 (M n).hxs.le
    simp only [one_mul] at H
    exact H.trans (hxsunit n)
  have hchildD : c0*(M n).xs≤D := by
    have H := mul_le_mul_of_nonneg_left (hxsunit n) hc0.le
    simp only [mul_one] at H
    exact H.trans hc0D
  have hmass : (M n).data.s≤comparisonLowerScale child.N child.E child.d := by
    change (M n).data.s≤actualChildCutoff (dim n+1) (m/10000) c0
      (M n).context.d (M n).lam (M n).xs
    exact hnMass
  have hs4M : (M n).data.s≤1/4 := by rw [hnSame];exact hnS4
  have hweakPoint : laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs≤(M n).xs^2 :=
    (div_le_one₀ (sq_pos_of_pos (M n).hxs)).mp hnWeak.le
  have htotal : ∀u∈Icc (0:ℝ) 1,child.h u+child.b u≤Bclock := by
    intro u hu
    have hr := (omittedSweepQuantile_bounds zero_le_one
      ⟨(M n).data.hs.1,(M n).data.hs1⟩
      (M n).data.hc (M n).data.hk (M n).data.hkc
      (M n).data.hm (M n).data.hM (M n).alpha u).2
    have hc := (M n).coefficient_nonneg u
    have hcR := mul_le_mul_of_nonneg_left hr hc
    change (M n).h u+(M n).coefficient u*(M n).R u+
      ((M n).b u-(M n).coefficient u)≤Bclock
    linarith only [hnTotal.1 u hu,hcR,hTB]
  have hclock : ∀alpha : child.Profile,
      NativePullbackClockRegularity alpha.val.val child.b child.h 0 1 := by
    exact hnClock child rfl rfl rfl
  have hfail : child.N^(20*(m/10000))*child.E < child.cost (child.d^2) := by
    change ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
      (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs <
        (M n).macroChildSweepCost hc0
    exact hnCost
  exact hnSelect (M n) hnRoom hnCross hchild1 hchildD hs4M
    hmass hnTarget hweakPoint htotal hclock hfail

private theorem exists_weak_bad_parent_finite_child_step_constants_terminal_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 Ct D Bclock c0 margin : ℝ,
        0 < m → m ≤ (1:ℝ)/120 → 0 < cl → 0 < cu → cl≤cu →
        2≤Az → 1≤Ct → 0 < C0 →
        ∀ _hc0 : 0 < c0, c0≤1 → c0≤D → (beta:ℝ)^2≤Bclock →
        cl≤lower → upper≤cu →
        cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ→ℕ, Tendsto dim atTop atTop →
        ∀ M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 Ct D Bclock,
        ∀ G : HighGapHistory_original_q M ((beta:ℝ)^2) c0,
        ∀ q : ℕ,
        ActualFiniteWeakHighOnlyHistory c0 G.root q M →
        ActualHighOnlyErrorGrowthHistory G.root q M →
        (∀ᶠ n in atTop, (G.root n).context.d≤c0) →
        (∀ᶠ n in atTop, ∀ u∈Ico (0:ℝ) (G.root n).data.s,
          (G.root n).b u+margin≤(G.root n).b (G.root n).data.s) →
        (∀ᶠ n in atTop, 0 < (G.root n).data.s) →
        ((q:ℝ)+2)*c0^2≤ margin →
        (∀ n, (M n).xs≤1) →
        (∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N (m/10000)
          (M n).context.E (M n).lam≤(M n).xs) →
        Tendsto (fun n => laplaceComparisonStrength (M n).context.d
          (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) →
        (∀ᶠ n in atTop, ¬(cl*(M n).xs≤(M n).alpha.val.val (M n).xs ∧
          (M n).alpha.val.val (M n).xs≤cu*(M n).xs)) →
        ∃ N : ℕ,
          ∃ Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim (n+N)+1)
            m (m/10000) cl cu Az C0 Ct D Bclock,
            ActualFiniteWeakHighOnlyHistory c0 (fun n=>G.root (n+N)) (q+1) Q ∧
            ActualHighOnlyErrorGrowthHistory (fun n=>G.root (n+N)) (q+1) Q ∧
            (∀ n, (Q n).xs∈Icc (comparisonConditionalScale (Q n).context.N
              (m/10000) (Q n).context.E (Q n).lam) 1) ∧
            (∀ n, (Q n).alpha.val.val (Q n).xs < cl*(Q n).xs ∨
              cu*(Q n).xs < (Q n).alpha.val.val (Q n).xs) := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hcost⟩ :=
    exists_bad_parent_sharp_child_cost_failure_constants_terminal_original_q hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu Az C0 Ct D Bclock c0 margin hm hmsmall hcl hcu hclcu
    hAz hCt hC0 hc0 hc01 hc0D hTB hclCost hcuCost hclSlack hcuSlack
    dim hdim M G q Hfinite Herror hrootCap hrootGap hrootPos hbudget
    hunit htarget hweak Hbad
  have Hroom := Hfinite.next_child_room hc0.le hrootCap hrootGap hrootPos
    hbudget (fun n=>(M n).xs) (fun n=>(M n).hxs)
    (Eventually.of_forall hunit)
  have HroomChild : ∀ᶠ n in atTop,
      (M n).lam+(c0*(M n).xs)^2≤(M n).b (M n).data.s :=
    Hroom.mono (fun n hn=>hn.1)
  have Hcross : ∀ᶠ n in atTop, ∀ u∈Ico (0:ℝ) (M n).data.s,
      (M n).b u+(M n).lam+(c0*(M n).xs)^2≤(M n).b (M n).data.s :=
    Hroom.mono (fun n hn=>hn.2)
  have Hfail := Hcost m cl cu Az C0 Ct D Bclock c0
    hm hmsmall hcl hcu (by linarith : 0≤Az) hC0 hc0 hc01
    hclCost hcuCost hclSlack hcuSlack dim hdim M G hunit htarget hweak
    HroomChild Hcross Hbad
  have Hselected := G.eventually_select_bad_child_of_sharp_failure_terminal_original_q
    hm hmsmall hcl hcu hclcu hAz hCt hC0 hc0 hc01 hc0D hTB hdim
    hunit htarget hweak HroomChild Hcross Hfail
  exact selected_bad_child_extends_finite_histories Hfinite Herror
    hunit htarget hweak Hselected

private theorem exists_finite_high_only_propagation_terminal_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 Ct D Bclock c0 margin : ℝ,
        0 < m → m ≤ (1:ℝ)/120 → 0 < cl → 0 < cu → cl≤cu →
        2≤Az → 1≤Ct → 0 < C0 → D≤1 →
        ∀ _hc0 : 0 < c0, c0≤1 → c0≤D → (beta:ℝ)^2≤Bclock →
        (((actualPropagationDepth (m/10000):ℕ):ℝ)+2)*c0^2≤ margin →
        margin≤(beta:ℝ)^2/8 → cl≤lower → upper≤cu →
        cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ→ℕ, Tendsto dim atTop atTop →
        ∀ root : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 Ct D Bclock,
        ∀ G : HighGapHistory_original_q root ((beta:ℝ)^2) c0,
        G.root = root →
        (∀ᶠ n in atTop, (beta:ℝ)^2/4≤(G.wall n).data.epsilon) →
        (∀ᶠ n in atTop, (G.wall n).data.d^2≤(beta:ℝ)^2/8) →
        (∀ n, (root n).xs≤1) →
        (∀ᶠ n in atTop, comparisonConditionalScale (root n).context.N
          (m/10000) (root n).context.E (root n).lam≤(root n).xs) →
        (∀ᶠ n in atTop, ¬(cl*(root n).xs≤(root n).alpha.val.val (root n).xs ∧
          (root n).alpha.val.val (root n).xs≤cu*(root n).xs)) → False := by
  classical
  obtain ⟨lowerS, upperS, hlowerS, hupperS, Hstrength⟩ :=
    exists_high_only_history_bad_test_strength_saving_terminal_original_q hbeta hTemp
  obtain ⟨lowerC, upperC, hlowerC, hupperC, Hstep⟩ :=
    exists_weak_bad_parent_finite_child_step_constants_terminal_original_q hbeta hTemp
  refine ⟨min lowerS lowerC, max upperS upperC,
    lt_min hlowerS hlowerC, hupperS.trans_le (le_max_left _ _), ?_⟩
  intro m cl cu Az C0 Ct D Bclock c0 margin hm hmsmall hcl hcu hclcu
    hAz hCt hC0 hD hc0 hc01 hc0D hTB hbudget hmarginT hclBounds hcuBounds
    hclTemp hcuTemp dim hdim root G hGroot hWallEps hWallD hrootUnit hrootTarget hrootBad
  have hdelta : 0 < m/10000 := by positivity
  have hclS : cl≤lowerS := hclBounds.trans (min_le_left _ _)
  have hcuS : upperS≤cu := (le_max_left _ _).trans hcuBounds
  have hclC : cl≤lowerC := hclBounds.trans (min_le_right _ _)
  have hcuC : upperC≤cu := (le_max_right _ _).trans hcuBounds
  have hTempCost : cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) := by
    have hp : 0 < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) :=
      mul_pos (zero_lt_one.trans hTemp) (Real.exp_pos _)
    linarith only [hclTemp,hp]
  have hrootPos : ∀ᶠ n in atTop, 0 < (G.root n).data.s := by
    filter_upwards [G.same_mass] with n hn
    rw [hn]
    exact (G.wall n).data.hs.1
  have hrootCap : ∀ᶠ n in atTop, (G.root n).context.d≤c0 := by
    filter_upwards [G.wall_unit, G.first_radius] with n hn hnd
    rw [hnd]
    simpa only [actualChildRadius, mul_one] using mul_le_mul_of_nonneg_left hn hc0.le
  have hrootGap : ∀ᶠ n in atTop, ∀ u∈Ico (0:ℝ) (G.root n).data.s,
      (G.root n).b u+margin≤(G.root n).b (G.root n).data.s := by
    filter_upwards [G.root_gap_original_q hWallEps hWallD] with n hn u hu
    linarith only [hn u hu, hmarginT]
  let depth := actualPropagationDepth (m/10000)
  have Hchains : ∀ k : ℕ, k≤depth →
      ∃ phi : ℕ→ℕ, StrictMono phi ∧
      ∃ M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim (phi n)+1)
        m (m/10000) cl cu Az C0 Ct D Bclock,
        ActualFiniteWeakHighOnlyHistory c0 (fun n=>G.root (phi n)) k M ∧
        ActualHighOnlyErrorGrowthHistory (fun n=>G.root (phi n)) k M ∧
        (∀ n, (M n).xs≤1) ∧
        (∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N
          (m/10000) (M n).context.E (M n).lam≤(M n).xs) ∧
        (∀ᶠ n in atTop, ¬(cl*(M n).xs≤(M n).alpha.val.val (M n).xs ∧
          (M n).alpha.val.val (M n).xs≤cu*(M n).xs)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have HF : ActualFiniteWeakHighOnlyHistory c0 G.root 0 root := by
        rw [hGroot]
        exact ActualFiniteWeakHighOnlyHistory.root root
      have HE : ActualHighOnlyErrorGrowthHistory G.root 0 root := by
        rw [hGroot]
        exact .root
      exact ⟨id, strictMono_id, root, HF, HE, hrootUnit, hrootTarget, hrootBad⟩
    | succ k ih =>
      intro hk
      obtain ⟨phi, hphi, M, Hfinite, Herror, Hunit, Htarget, Hbad⟩ :=
        ih (Nat.le_of_succ_le hk)
      let Gcurrent : HighGapHistory_original_q M ((beta:ℝ)^2) c0 :=
        (G.comp_original_q phi hphi).with_current_original_q M Hfinite.weak
      have HfiniteCurrent : ActualFiniteWeakHighOnlyHistory c0 Gcurrent.root k M := Hfinite
      have HerrorCurrent : ActualHighOnlyErrorGrowthHistory Gcurrent.root k M := Herror
      have hbudgetK : ((k:ℝ)+2)*c0^2≤ margin := by
        have HK : (k:ℝ)≤(depth:ℝ) := by exact_mod_cast Nat.le_of_succ_le hk
        have HB : ((depth:ℝ)+2)*c0^2≤ margin := by simpa only [depth] using hbudget
        have Hmul : ((k:ℝ)+2)*c0^2≤((depth:ℝ)+2)*c0^2 := by
          simpa only [add_comm] using
            mul_le_mul_of_nonneg_right (add_le_add_right HK 2) (sq_nonneg c0)
        exact Hmul.trans HB
      have Hweak := Hstrength m cl cu Az C0 Ct D Bclock c0 hm hmsmall hcl hcu
        (by linarith : 0≤Az) hC0 (by linarith : 0≤Ct) hD hc0 hc01
        hclS hcuS hclTemp hcuTemp (fun n=>dim (phi n))
        (hdim.comp hphi.tendsto_atTop) M Gcurrent Hunit Hbad
      obtain ⟨N, Q, HF, HE, Hscale, HbadQ⟩ :=
        Hstep m cl cu Az C0 Ct D Bclock c0 margin hm hmsmall hcl hcu hclcu
          hAz hCt hC0 hc0 hc01 hc0D hTB hclC hcuC hTempCost hcuTemp
          (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) M Gcurrent k
          HfiniteCurrent HerrorCurrent (hphi.tendsto_atTop.eventually hrootCap)
          (hphi.tendsto_atTop.eventually hrootGap)
          (hphi.tendsto_atTop.eventually hrootPos) hbudgetK Hunit Htarget Hweak Hbad
      let shift : ℕ→ℕ := fun n=>n+N
      have hshift : StrictMono shift := fun i j hij=>Nat.add_lt_add_right hij N
      let sigma := phi ∘ shift
      have hsigma : StrictMono sigma := hphi.comp hshift
      have HfiniteNew : ActualFiniteWeakHighOnlyHistory c0
          (fun n=>G.root (sigma n)) (k+1) Q := HF
      have HerrorNew : ActualHighOnlyErrorGrowthHistory
          (fun n=>G.root (sigma n)) (k+1) Q := HE
      have HbadNew : ∀ᶠ n in atTop, ¬(cl*(Q n).xs≤(Q n).alpha.val.val (Q n).xs ∧
          (Q n).alpha.val.val (Q n).xs≤cu*(Q n).xs) := by
        apply Eventually.of_forall
        intro n hn
        rcases HbadQ n with hlow | hhigh
        · exact (not_le.mpr hlow) hn.1
        · exact (not_le.mpr hhigh) hn.2
      exact ⟨sigma, hsigma, Q, HfiniteNew, HerrorNew, (fun n=>(Hscale n).2),
        Eventually.of_forall (fun n=>(Hscale n).1), HbadNew⟩
  obtain ⟨phi, hphi, M, Hfinite, Herror, _, _, _⟩ := Hchains depth le_rfl
  exact Herror.false_at_propagation_depth hm hdelta hC0 (hdim.comp hphi.tendsto_atTop)

end ActualHighOnlyOverlapMinimum

namespace ActualThetaZeroOverlapMinimum

private theorem eventually_exists_weak_high_only_first_bad_root_original_q
    {m delta cl cu Az C0 T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu)
    (hAz : 2 ≤ Az) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hc01 : c0 ≤ 1) (hmargin : delta/4 < 3*m-99*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 1 1 T)
    (hgap : ∀ n, ∀ u ∈ Ico (0:ℝ) (Q n).data.s,
      (Q n).changedBare u + (c0*(Q n).xs)^2 ≤ (Q n).changedBare (Q n).data.s)
    (hunit : ∀ᶠ n in atTop, (Q n).xs ≤ 1)
    (hs0 : Tendsto (fun n => (Q n).data.s) atTop (𝓝 0))
    (hsCut : Tendsto (fun n => (Q n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (Q n).data.d (Q n).lam (Q n).xs) atTop (𝓝 0))
    (htarget : ∀ᶠ n in atTop, comparisonConditionalScale
      (Q n).data.N delta (Q n).data.E (Q n).lam ≤ (Q n).xs)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (Q n).data.d (Q n).lam (Q n).xs/(Q n).xs^2) atTop (𝓝 0))
    (hcost : ∀ᶠ n in atTop,
      ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (Q n).data.d (Q n).lam (Q n).xs <
      (Q n).highOnlyChildSweepCost hc0 (hgap n)) :
    ∀ᶠ n in atTop,
      ∃ root : ActualHighOnlyOverlapMinimum (dim n+1)
        m delta cl cu Az C0 1 1 T,
        root.context.d = c0*(Q n).xs ∧
        root.context.E = actualChildErrorBudget (dim n+1) delta c0
          (Q n).data.d (Q n).lam (Q n).xs ∧
        (Q n).data.N^(delta/4)*(Q n).data.E ≤ root.context.E ∧
        root.xs ∈ Icc (comparisonConditionalScale root.context.N delta
          root.context.E root.lam) 1 ∧
        (root.alpha.val.val root.xs < cl*root.xs ∨
          cu*root.xs < root.alpha.val.val root.xs) ∧
        root.data.s = (Q n).data.s ∧
        root.b = (Q n).changedBare ∧ root.h = (Q n).changedField := by
  have Hselect := hdim.eventually
    (eventually_exists_selected_bad_high_only_child_original_q (D := 1) (Bclock := T)
      hm hdelta hroom hcl hcu hclcu hAz le_rfl hC0 hc0 hmargin)
  have Hs4 := hs0.eventually
    (eventually_le_nhds (show (0:ℝ) < 1/4 by norm_num))
  have Hratio := hsCut.eventually (eventually_le_nhds zero_lt_one)
  have Hweak := hweak.eventually (eventually_le_nhds zero_lt_one)
  filter_upwards [Hselect, hunit, Hs4, Hratio, htarget, Hweak, hcost]
    with n hnSelect hnUnit hnS4 hnRatio hnTarget hnWeak hnCost
  have hchild1 : c0*(Q n).xs ≤ 1 := by
    calc
      c0*(Q n).xs ≤ c0*1 := mul_le_mul_of_nonneg_left hnUnit hc0.le
      _ = c0 := mul_one c0
      _ ≤ 1 := hc01
  have hmass : (Q n).data.s ≤ comparisonLowerScale (Q n).data.N
      (actualChildErrorBudget (dim n+1) delta c0
        (Q n).data.d (Q n).lam (Q n).xs) (c0*(Q n).xs) := by
    change (Q n).data.s ≤ actualChildCutoff (dim n+1) delta c0
      (Q n).data.d (Q n).lam (Q n).xs
    have HcutPos : 0 < actualChildCutoff (dim n+1) delta c0
        (Q n).data.d (Q n).lam (Q n).xs :=
      (actual_child_cutoff_pos_le_radius
        (Q n).data.hN hc0 (Q n).hlam (Q n).hxs).1
    exact (div_le_one₀ HcutPos).mp hnRatio
  have hweakPoint : laplaceComparisonStrength (Q n).data.d
      (Q n).lam (Q n).xs ≤ (Q n).xs^2 :=
    (div_le_one₀ (sq_pos_of_pos (Q n).hxs)).mp hnWeak
  exact hnSelect (Q n) (hgap n) hchild1 hchild1 hnS4
    hmass hnTarget hweakPoint hnCost

theorem exists_high_gap_first_root_finite_contradiction_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu c0 margin : ℝ, 0 < m → m < 1/300 →
      0 < cl → 0 < cu → cl ≤ lower → upper ≤ cu →
      cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
      (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3:ℝ)^2/
        (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
      ∀ hc0 : 0 < c0, c0 ≤ 1 →
      (((actualPropagationDepth (m/10000):ℕ):ℝ)+2)*c0^2 ≤ margin →
      margin ≤ (beta:ℝ)^2/8 →
      ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu 2 1 1 1 ((beta:ℝ)^2),
      ∀ hgap : ∀ n, ∀ u ∈ Ico (0:ℝ) (Q n).data.s,
        (Q n).changedBare u + (c0*(Q n).xs)^2 ≤ (Q n).changedBare (Q n).data.s,
      (∀ᶠ n in atTop, (Q n).data.T = (beta:ℝ)^2) →
      (∀ᶠ n in atTop, (Q n).xs ≤ 1) →
      (∀ᶠ n in atTop, comparisonConditionalScale (Q n).data.N
        (m/10000) (Q n).data.E (Q n).lam ≤ (Q n).xs) →
      Tendsto (fun n => laplaceComparisonStrength (Q n).data.d
        (Q n).lam (Q n).xs/(Q n).xs^2) atTop (𝓝 0) →
      Tendsto (fun n => (Q n).data.s) atTop (𝓝 0) →
      Tendsto (fun n => (Q n).data.s/
        actualChildCutoff (dim n+1) (m/10000) c0
          (Q n).data.d (Q n).lam (Q n).xs) atTop (𝓝 0) →
      (∀ᶠ n in atTop, (beta:ℝ)^2/4 ≤ (Q n).data.epsilon) →
      (∀ᶠ n in atTop, (Q n).data.d^2 ≤ (beta:ℝ)^2/8) →
      (∀ᶠ n in atTop,
        ((dim n+1:ℕ):ℝ)^(20*(m/10000))*
          actualChildErrorBudget (dim n+1) (m/10000) c0
            (Q n).data.d (Q n).lam (Q n).xs <
        (Q n).highOnlyChildSweepCost hc0 (hgap n)) → False := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hfinite⟩ :=
    ActualHighOnlyOverlapMinimum.exists_finite_high_only_propagation_terminal_original_q
      hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu c0 margin hm hmmax hcl hcu hclBounds hcuBounds
    hclTemp hcuTemp hc0 hc01 hbudget hmarginT dim hdim Q hgap
    hWallT hunit htarget hweak hs0 hsCut heps hdSmall hcost
  have hmsmall : m ≤ (1:ℝ)/120 := by linarith only [hmmax]
  have hdelta : 0 < m/10000 := by positivity
  have hroom : m/10000 < 3*m := by linarith only [hm]
  have hmargin : (m/10000)/4 < 3*m-99*(m/10000) := by linarith only [hm]
  have hcl1 : cl ≤ 1 := by
    simpa only [mul_one, (Q 0).alpha.property.2.1] using
      ((Q 0).regular 1 ⟨(Q 0).hz.2, le_rfl⟩).1
  have hcu1 : 1 ≤ cu := by
    simpa only [mul_one, (Q 0).alpha.property.2.1] using
      ((Q 0).regular 1 ⟨(Q 0).hz.2, le_rfl⟩).2
  have hclcu : cl ≤ cu := hcl1.trans hcu1
  have Hroot := eventually_exists_weak_high_only_first_bad_root_original_q
    hm hdelta hroom hcl hcu hclcu le_rfl zero_lt_one hc0 hc01
    hmargin dim hdim Q hgap hunit hs0 hsCut htarget hweak hcost
  obtain ⟨n0, Hn0⟩ := eventually_atTop.mp Hroot
  let shift : ℕ → ℕ := fun n => n+n0
  have hshift : StrictMono shift := fun i j hij => Nat.add_lt_add_right hij n0
  have hshiftlim : Tendsto shift atTop atTop := hshift.tendsto_atTop
  have Htail (n : ℕ) := Hn0 (shift n) (by dsimp [shift]; omega)
  choose root hD hE _hGrow hXs hBad hSame hBare hField using Htail
  let dim1 : ℕ → ℕ := fun n => dim (shift n)
  let Qwall := fun n => Q (shift n)
  let G : ActualHighOnlyOverlapMinimum.HighGapHistory_original_q root ((beta:ℝ)^2) c0 := {
    wall := Qwall
    root := root
    history := .root
    temperature := hshiftlim.eventually hWallT
    omission_zero := hs0.comp hshiftlim
    same_mass := Eventually.of_forall hSame
    wall_unit := hshiftlim.eventually hunit
    wall_target := hshiftlim.eventually htarget
    wall_weak := hweak.comp hshiftlim
    wall_cut := hsCut.comp hshiftlim
    first_radius := Eventually.of_forall hD
    first_error := Eventually.of_forall hE
    bare := Eventually.of_forall (fun n u => congrFun (hBare n) u)
    field := Eventually.of_forall (fun n u => congrFun (hField n) u)
    hT := zero_lt_one.trans hTemp
  }
  have Hbad : ∀ᶠ n in atTop,
      ¬(cl*(root n).xs ≤ (root n).alpha.val.val (root n).xs ∧
        (root n).alpha.val.val (root n).xs ≤ cu*(root n).xs) := by
    apply Eventually.of_forall
    intro n hn
    rcases hBad n with hlow | hhigh
    · exact (not_lt_of_ge hn.1) hlow
    · exact (not_lt_of_ge hn.2) hhigh
  exact Hfinite m cl cu 2 1 1 1 ((beta:ℝ)^2) c0 margin
    hm hmsmall hcl hcu hclcu le_rfl le_rfl zero_lt_one le_rfl
    hc0 hc01 hc01 le_rfl hbudget hmarginT hclBounds hcuBounds hclTemp hcuTemp
    dim1 (hdim.comp hshiftlim) root G rfl
    (hshiftlim.eventually heps) (hshiftlim.eventually hdSmall)
    (fun n => (hXs n).2) (Eventually.of_forall (fun n => (hXs n).1)) Hbad

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

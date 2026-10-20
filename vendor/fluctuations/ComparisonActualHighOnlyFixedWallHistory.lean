module

public import ComparisonActualHighOnlyWallHistoryContext
public import ComparisonActualHighOnlyHistoryWeakenConstants
public import ComparisonActualHighOnlyHistoryReindex
public import ComparisonActualHighOnlyWeakHistoryEndpointCost
public import ComparisonNativeActualGeneralBareEndpointCost
public import ComparisonActualHighWallWeakenBookkeepingConstants

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000
namespace ActualHighOnlyOverlapMinimum
variable {m cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ → ℕ}

structure ActualFixedWallHighOnlyHistory
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock) (T c0 : ℝ) where
  wall : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1)
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
    (wall n).data.E ((wall n).data.d^2) ≤ (wall n).xs
  wall_weak : Tendsto (fun n => (wall n).data.g (wall n).xs/(wall n).xs^2)
    atTop (𝓝 0)
  first_radius : ∀ᶠ n in atTop, (root n).context.d = actualChildRadius c0 (wall n).xs
  first_error : ∀ᶠ n in atTop, (root n).context.E = actualChildErrorBudget
    (dim n+1) (m/10000) c0 (wall n).data.d ((wall n).data.d^2) (wall n).xs
  bare : ∀ᶠ n in atTop, ∀ u, (root n).b u = (wall n).data.b (wall n).alpha u
  field : ∀ᶠ n in atTop, ∀ u, (root n).h u = (wall n).data.h (wall n).alpha u
  hT : 0 < T

namespace ActualFixedWallHighOnlyHistory
variable {M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
  m (m/10000) cl cu Az C0 Ct D Bclock}

def comp (G : ActualFixedWallHighOnlyHistory M T c0)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ActualFixedWallHighOnlyHistory (fun n => M (phi n)) T c0 where
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
  first_radius := hphi.tendsto_atTop.eventually G.first_radius
  first_error := hphi.tendsto_atTop.eventually G.first_error
  bare := hphi.tendsto_atTop.eventually G.bare
  field := hphi.tendsto_atTop.eventually G.field
  hT := G.hT

def weaken_constants (G : ActualFixedWallHighOnlyHistory M T c0)
    {cl' cu' Az' Ct' D' Bclock' : ℝ}
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    ActualFixedWallHighOnlyHistory
      (fun n => (M n).weakenConstants hcl hcu hAz hCt hD hB) T c0 where
  wall := fun n => (G.wall n).weakenBookkeepingConstants hcl hcu hAz hCt hD hB
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
  first_radius := G.first_radius
  first_error := G.first_error
  bare := G.bare
  field := G.field
  hT := G.hT

def append_child (G : ActualFixedWallHighOnlyHistory M T c0)
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
    ActualFixedWallHighOnlyHistory Q T c0 where
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
  first_radius := G.first_radius
  first_error := G.first_error
  bare := G.bare
  field := G.field
  hT := G.hT

def with_current (G : ActualFixedWallHighOnlyHistory M T c0)
    (Q : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (H : ActualWeakHighOnlyHistoryChain c0 G.root Q) :
    ActualFixedWallHighOnlyHistory Q T c0 where
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
  first_radius := G.first_radius
  first_error := G.first_error
  bare := G.bare
  field := G.field
  hT := G.hT

theorem exists_context (G : ActualFixedWallHighOnlyHistory M T c0)
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hdim : Tendsto dim atTop atTop)
    (hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0)) :
    Nonempty (HighOnlyActualComparableBandContext M T) :=
  G.history.exists_concrete_wall_comparable_context hm hmsmall hcl hAz hC0 hc0 hc01
    G.hT dim hdim G.wall G.root M G.temperature G.error G.radius G.omission G.same_mass
    (fun n => (G.wall n).xs) (fun n => (G.wall n).hxs) G.wall_unit G.wall_target
    (Eventually.of_forall (fun n => (G.wall n).hzxs)) G.wall_weak G.first_radius
    G.first_error G.bare G.field hxs

theorem wall_limits (G : ActualFixedWallHighOnlyHistory M T c0)
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

theorem root_endpoint_cost_tendsto_zero (G : ActualFixedWallHighOnlyHistory M T c0)
    (hmsmall : m ≤ (1:ℝ)/120) (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => comparisonEndpointL1Cost T (G.root n).b (G.root n).h)
      atTop (𝓝 0) := by
  obtain ⟨Hs, Hd⟩ := G.wall_limits hmsmall hdim
  have H := ActualHighWallData.endpoint_L1_cost_tendsto_zero
    G.wall G.temperature Hs Hd
  apply H.congr'
  filter_upwards [G.bare, G.field] with n hb hh
  have Hb : (G.root n).b = (G.wall n).data.b (G.wall n).alpha := funext hb
  have Hh : (G.root n).h = (G.wall n).data.h (G.wall n).alpha := funext hh
  rw [Hb, Hh]

theorem endpoint_cost_tendsto_zero (G : ActualFixedWallHighOnlyHistory M T c0)
    (hmsmall : m ≤ (1:ℝ)/120) (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0) :=
  G.history.endpoint_cost_tendsto_zero (G.root_endpoint_cost_tendsto_zero hmsmall hdim)

theorem same_omission (G : ActualFixedWallHighOnlyHistory M T c0) :
    ∀ᶠ n in atTop, (M n).data.s = (G.wall n).data.s := by
  filter_upwards [G.history.same_omission, G.same_mass] with n hn hr
  exact hn.trans hr

theorem omission_tendsto_zero (G : ActualFixedWallHighOnlyHistory M T c0)
    (hmsmall : m ≤ (1:ℝ)/120) (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => (M n).data.s) atTop (𝓝 0) :=
  (G.wall_limits hmsmall hdim).1.congr' (G.same_omission.mono (fun _ hn=>hn.symm))

theorem total_root (G : ActualFixedWallHighOnlyHistory M T c0) :
    ∀ᶠ n in atTop, (∀ u ∈ Icc (0:ℝ) 1, (M n).h u+(M n).b u ≤ T) ∧
      (M n).h 0 = 0 := by
  apply G.history.total_root
  filter_upwards [G.temperature, G.bare, G.field] with n hnT hb hh
  constructor
  · intro u hu
    rw [hb, hh, ←((G.wall n).data.clock_coe (G.wall n).alpha hu).1,
      ←((G.wall n).data.clock_coe (G.wall n).alpha hu).2]
    exact ((G.wall n).data.total_clock_le (G.wall n).alpha u hu).trans_eq hnT
  · rw [hh, ←((G.wall n).data.clock_coe (G.wall n).alpha (by norm_num)).2,
      (G.wall n).data.root_field_zero (G.wall n).alpha]
    rfl

theorem root_cutoff_gates (G : ActualFixedWallHighOnlyHistory M T c0)
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hdim : Tendsto dim atTop atTop) :
    Tendsto (fun n => (G.wall n).data.s/actualChildCutoff (dim n+1) (m/10000)
      c0 (G.wall n).data.d ((G.wall n).data.d^2) (G.wall n).xs) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, actualChildCutoff (dim n+1) (m/10000) c0
        (G.wall n).data.d ((G.wall n).data.d^2) (G.wall n).xs ≤
          comparisonLowerScale (G.root n).context.N
            (G.root n).context.E (G.root n).context.d) ∧
      (∀ᶠ n in atTop, (G.wall n).data.d^2 ≤ comparisonLowerScale
        (G.root n).context.N (G.root n).context.E (G.root n).context.d) := by
  have hdelta : 0 < m/10000 := by positivity
  have Hcut : ∀ᶠ n in atTop, actualChildCutoff (dim n+1) (m/10000) c0
      (G.wall n).data.d ((G.wall n).data.d^2) (G.wall n).xs ≤
        comparisonLowerScale (G.root n).context.N
          (G.root n).context.E (G.root n).context.d := by
    filter_upwards [G.first_radius, G.first_error] with n hnd hnE
    simp only [comparisonLowerScale, ActualHighOnlyComparisonData.N,
      hnd, hnE, actualChildCutoff]
    exact le_rfl
  have Hratio : Tendsto (fun n => (G.wall n).data.s/comparisonLowerScale
      (G.wall n).data.N (G.wall n).data.E (G.wall n).data.d) atTop (𝓝 0) := by
    apply ((concrete_wall_omission_ratio_tendsto_zero hm).comp
      ((tendsto_add_atTop_nat 1).comp hdim)).congr'
    filter_upwards [G.error, G.radius, G.omission] with n hnE hnd hns
    simp only [Function.comp_apply, hnE, hnd, hns, ActualHighWallData.N]
  have HS := actual_wall_omission_ratio_inherits_child_cutoff
    hm hdelta hC0 hc0 (by linarith) dim hdim G.wall
    (fun n => (G.wall n).xs) (fun n => (G.wall n).hxs)
    G.wall_target G.wall_weak Hratio
  have Hinherit := actual_wall_child_cutoff_inheritance
    hm hdelta hC0 hc0 (by linarith) dim hdim G.wall
    (fun n => (G.wall n).xs) (fun n => (G.wall n).hxs)
    G.wall_target G.wall_weak
  have Hfieldscale : ∀ᶠ n in atTop, (G.wall n).data.d^2 ≤ comparisonLowerScale
      (G.root n).context.N (G.root n).context.E (G.root n).context.d := by
    filter_upwards [G.error, G.radius, Hinherit, Hcut] with n hnE hnd hnIn hnCut
    have Hnum := NativeOverlapMinimum.concrete_wall_square_strength_le_lower_scale
      hmsmall (by omega : 0 < dim n+1)
    rw [←hnd, ←hnE] at Hnum
    exact Hnum.trans (hnIn.trans hnCut)
  exact ⟨HS, Hcut, Hfieldscale⟩

theorem root_field_budget (G : ActualFixedWallHighOnlyHistory M T c0)
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hdim : Tendsto dim atTop atTop) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ᶠ n in atTop, ∀ u ∈ Icc (0:ℝ) 1,
      (G.root n).h u ≤ Cf*(comparisonLowerScale
        (G.root n).context.N (G.root n).context.E (G.root n).context.d+u) := by
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [G.field, (G.root_cutoff_gates hm hmsmall hC0 hc0 hdim).2.2]
    with n hnh hn u hu
  rw [hnh, ←((G.wall n).data.clock_coe (G.wall n).alpha hu).2, one_mul]
  exact ((G.wall n).data.field_le_strength (G.wall n).alpha hu).trans
    (by linarith [hu.1])

theorem root_all_profile_pullback (G : ActualFixedWallHighOnlyHistory M T c0) :
    ∀ᶠ n in atTop, ∀ child : ActualHighOnlyComparisonData (dim n+1) (m/10000),
      ∀ alpha : child.Profile, child.s = (G.root n).data.s →
        NativePullbackClockRegularity alpha.val.val (G.root n).b (G.root n).h 0 1 := by
  filter_upwards [G.same_mass, G.bare, G.field] with n hns hnb hnh child alpha ha
  have hsame : child.s = (G.wall n).data.s := ha.trans hns
  have HB : (G.root n).b = (G.wall n).data.b (G.wall n).alpha := funext hnb
  have HH : (G.root n).h = (G.wall n).data.h (G.wall n).alpha := funext hnh
  rw [HB, HH]
  obtain ⟨Kb, Kh, Hb, Hh⟩ := (G.wall n).data.changed_clocks_mass_cut_branches
    (G.wall n).alpha (G.wall n).data.s 1 (G.wall n).data.hs.1.le
    (G.wall n).data.hs1 le_rfl (Or.inr le_rfl)
  have Ha := inverseIntegralConstraints_lipschitz child.hm child.hM alpha.property
  have Hmap : MapsTo alpha.val.val (Icc (0:ℝ) 1) (Icc (G.wall n).data.s 1) := by
    intro r hr
    refine ⟨?_, (alpha.val.property.1 r).2⟩
    have H := alpha.val.property.2 hr.1
    rw [alpha.property.1, hsame] at H
    exact H
  have Hbcomp := Hb.comp Ha Hmap
  have Hhcomp := Hh.comp Ha Hmap
  refine Or.inl ⟨Kb*⟨child.M 1, child.hM⟩, Kh*⟨child.M 1, child.hM⟩, ?_, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro r hr t ht
    rw [←((G.wall n).data.clock_coe (G.wall n).alpha (alpha.val.property.1 r)).1,
      ←((G.wall n).data.clock_coe (G.wall n).alpha (alpha.val.property.1 t)).1]
    exact Hbcomp.dist_le_mul r hr t ht
  · apply LipschitzOnWith.of_dist_le_mul
    intro r hr t ht
    rw [←((G.wall n).data.clock_coe (G.wall n).alpha (alpha.val.property.1 r)).2,
      ←((G.wall n).data.clock_coe (G.wall n).alpha (alpha.val.property.1 t)).2]
    exact Hhcomp.dist_le_mul r hr t ht

end ActualFixedWallHighOnlyHistory
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonActualHighOnlyRegularChildCost
public import ComparisonActualHighOnlySelectedBadScale
public import ComparisonActualHighWallMacroscopicHighOnlyChildFactory
public import ComparisonActualHighWallBarePullback
public import ComparisonNativeActualChildParameterGrowth

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 26000000

namespace ActualHighWallData
variable {n N : ℕ} {delta delta' : ℝ}

theorem changed_pullback_clock_regularity_high_only_profile
    (w : ActualHighWallData n delta) (wall : w.Profile)
    (a : ActualHighOnlyComparisonData N delta') (alpha : a.Profile)
    (hsame : a.s=w.s) :
    NativePullbackClockRegularity alpha.val.val (w.b wall) (w.h wall) 0 1 := by
  obtain ⟨Kb, Kh, Hb, Hh⟩ := w.changed_clocks_mass_cut_branches
    wall w.s 1 w.hs.1.le w.hs1 le_rfl (Or.inr le_rfl)
  have Ha := inverseIntegralConstraints_lipschitz a.hm a.hM alpha.property
  have Hmap : MapsTo alpha.val.val (Icc (0:ℝ) 1) (Icc w.s 1) := by
    intro r hr
    refine ⟨?_, (alpha.val.property.1 r).2⟩
    have H := alpha.val.property.2 hr.1
    rw [alpha.property.1, hsame] at H
    exact H
  have HB := Hb.comp Ha Hmap
  have HH := Hh.comp Ha Hmap
  refine Or.inl ⟨Kb*⟨a.M 1, a.hM⟩, Kh*⟨a.M 1, a.hM⟩, ?_, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro r hr t ht
    rw [←(w.clock_coe wall (alpha.val.property.1 r)).1,
      ←(w.clock_coe wall (alpha.val.property.1 t)).1]
    exact HB.dist_le_mul r hr t ht
  · apply LipschitzOnWith.of_dist_le_mul
    intro r hr t ht
    rw [←(w.clock_coe wall (alpha.val.property.1 r)).2,
      ←(w.clock_coe wall (alpha.val.property.1 t)).2]
    exact HH.dist_le_mul r hr t ht

end ActualHighWallData
namespace ActualHighWallOverlapMinimum

theorem actualHighOnlyChild_cost_eq_macro
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hc0 : 0 < c0) (hreserve : M.data.d^2+(c0*M.xs)^2≤M.data.epsilon) :
    (M.actualHighOnlyChild hc0 M.hxs hreserve).cost ((c0*M.xs)^2)=
      M.macroHighOnlyChildSweepCost hc0 := by
  rfl

theorem eventually_exists_selected_bad_fixed_wall_high_only_child
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl≤cu)
    (hAz : 2≤Az) (hCt : 1≤Ct) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀ hreserve : M.data.d^2+(c0*M.xs)^2≤M.data.epsilon,
      c0*M.xs≤1 → c0*M.xs≤D → M.data.s≤1/4 →
      M.data.s≤actualChildCutoff (n+1) delta c0 M.data.d (M.data.d^2) M.xs →
      comparisonConditionalScale M.data.N delta M.data.E (M.data.d^2)≤M.xs →
      laplaceComparisonStrength M.data.d (M.data.d^2) M.xs≤M.xs^2 →
      M.data.N^(20*delta)*actualChildErrorBudget (n+1) delta c0
        M.data.d (M.data.d^2) M.xs < M.macroHighOnlyChildSweepCost hc0 →
      ∃ Q : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.context.d=c0*M.xs ∧
        Q.context.E=actualChildErrorBudget (n+1) delta c0 M.data.d (M.data.d^2) M.xs ∧
        M.data.N^(delta/4)*M.data.E≤Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N delta Q.context.E Q.lam) 1 ∧
        (Q.alpha.val.val Q.xs<cl*Q.xs ∨ cu*Q.xs<Q.alpha.val.val Q.xs) ∧
        Q.data.s=M.data.s ∧ Q.b=M.data.b M.alpha ∧ Q.h=M.data.h M.alpha := by
  have hdim : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [ActualHighOnlyComparisonData.eventually_actual_high_only_regular_child_failure_selects_irregular
      (D:=D) (T:=Bclock) hm hdelta hroom hcl hcu hclcu hC0,
    hdim.eventually (eventually_actual_child_parameters_from_target hm hdelta
      (one_div_pos.mpr hC0) hc0 hmargin)] with n hnFailure hnParams
  intro M hreserve hchild1 hchildD hs4 hmass htarget hweak hfail
  let child := M.actualHighOnlyChild hc0 M.hxs hreserve
  have hlo : (1/C0)*M.data.N^(-(2:ℝ)/3+m)*M.data.d≤M.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : M.data.E≤M.data.d^2/Real.sqrt ((n+1:ℕ):ℝ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mpr
      (by simpa only [mul_comm] using M.hupper)
  have hp := hnParams M.data.d (M.data.d^2) M.data.E M.xs M.data.hd
    (sq_pos_of_pos M.data.hd) le_rfl M.data.hE M.hxs hlo hup htarget hweak
  have hchildLower : child.N^(-(2:ℝ)/3+m)*child.d≤C0*child.E := by
    have H := mul_le_mul_of_nonneg_left hp.1 hC0.le
    change ((n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*actualChildRadius c0 M.xs≤
      C0*actualChildErrorBudget (n+1) delta c0 M.data.d (M.data.d^2) M.xs
    simpa only [←mul_assoc,mul_one_div_cancel hC0.ne',one_mul] using H
  have hchildUpper : Real.sqrt child.N*child.E≤child.d^2 := by
    have H := (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mp hp.2.1
    change Real.sqrt M.data.N*actualChildErrorBudget (n+1) delta c0
      M.data.d (M.data.d^2) M.xs≤(actualChildRadius c0 M.xs)^2
    simpa only [mul_comm] using H
  have htotal : ∀ u∈Icc (0:ℝ) 1, child.h u+child.b u≤Bclock := by
    intro u hu
    change M.data.h M.alpha u+M.data.b M.alpha u≤Bclock
    rw [←(M.data.clock_coe M.alpha hu).1, ←(M.data.clock_coe M.alpha hu).2]
    exact (M.data.total_clock_le M.alpha u hu).trans M.hT
  have hclock : ∀ alpha : child.Profile,
      NativePullbackClockRegularity alpha.val.val child.b child.h 0 1 := by
    intro alpha
    exact M.data.changed_pullback_clock_regularity_high_only_profile M.alpha child alpha rfl
  have hmass' : child.s≤comparisonLowerScale child.N child.E child.d := hmass
  have hfail' : child.N^(20*delta)*child.E<child.cost (child.d^2) := by
    change M.data.N^(20*delta)*actualChildErrorBudget (n+1) delta c0
      M.data.d (M.data.d^2) M.xs <
        (M.actualHighOnlyChild hc0 M.hxs hreserve).cost ((c0*M.xs)^2)
    rw [M.actualHighOnlyChild_cost_eq_macro hc0 hreserve]
    exact hfail
  obtain ⟨lam, hlam, alpha, hattained, hbad⟩ := hnFailure child
    hchildD hchild1 hs4 hmass' hchildUpper hchildLower htotal hclock hfail'
  have hcl1 : cl≤1 := by
    simpa only [M.alpha.property.2.1,mul_one] using (M.regular 1 ⟨M.hz.2,le_rfl⟩).1
  have hcu1 : 1≤cu := by
    simpa only [M.alpha.property.2.1,mul_one] using (M.regular 1 ⟨M.hz.2,le_rfl⟩).2
  have hlam0 : 0<lam := (Real.rpow_pos_of_pos child.hN _).trans hlam.1
  obtain ⟨_, _, hminimum⟩ := child.exists_minimum ⟨hlam0.le, hlam.2.le⟩
  let optimizer : ActualHighOnlyComparisonMinimum child lam :=
    ⟨alpha, hattained, fun beta=>hattained.symm ▸ hminimum beta⟩
  obtain ⟨Q, hcontext, hQlam, hAlpha, hxs, hz, hbadQ⟩ :=
    child.exists_selected_bad_scale_minimum_of_attained optimizer
      hlam0 hlam.2.le hdelta.le hchildD hchildUpper hchildLower
      htotal hAz hCt hcl1 hcu1 hbad
  have hc : Q.context=child := hcontext
  refine ⟨Q, ?_, ?_, ?_, ?_, hbadQ, ?_, ?_, ?_⟩
  · rw [hc];rfl
  · rw [hc];rfl
  · rw [hc];exact hp.2.2.1
  · rw [hc, hQlam];exact hxs
  · rw [hcontext];rfl
  · change Q.data.b=M.data.b M.alpha
    rw [hcontext];rfl
  · change Q.data.h=M.data.h M.alpha
    rw [hcontext];rfl

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

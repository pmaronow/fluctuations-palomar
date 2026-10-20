module

public import ComparisonActualHighOnlyActualRegularConditionalDensity
public import ComparisonActualHighOnlySharpChildBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace ActualHighOnlyComparisonData

theorem eventually_actual_high_only_regular_child_cost_of_regular
    {m delta cl cu C0 D T:ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl:0<cl) (hcu:0<cu) (hclcu:cl≤cu) (hC0:0<C0):
    ∀ᶠn:ℕ in atTop,∀a:ActualHighOnlyComparisonData (n+1) delta,
      a.d≤D → a.d≤1 → a.s≤1/4 →
      a.s≤comparisonLowerScale a.N a.E a.d →
      Real.sqrt a.N*a.E≤a.d^2 → a.N^(-(2:ℝ)/3+m)*a.d≤C0*a.E →
      (∀u∈Icc (0:ℝ) 1,a.h u+a.b u≤T) →
      (∀alpha:a.Profile,NativePullbackClockRegularity alpha.val.val a.b a.h 0 1) →
      (∀lam∈Ioo (a.N^(-10:ℝ)) (a.d^2),∀alpha:a.Profile,
        a.objective lam alpha=a.minimum lam →
        ∀r∈Icc (min (comparisonConditionalScale a.N delta a.E lam) 1) 1,
          cl*r≤alpha.val.val r ∧ alpha.val.val r≤cu*r) →
      a.cost (a.d^2)≤a.N^(20*delta)*a.E:=by
  have hgamma:0<1/C0:=one_div_pos.mpr hC0
  have hdim:Tendsto (fun n:ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  filter_upwards [eventually_actual_regular_conditional_original_density_high_only
      (D:=D) (T:=T) hm hdelta hroom hcl hcu hclcu hC0,
    hdim.eventually (eventually_cost_le_of_original_density hm hdelta hgamma)]
    with n hnDensity hnCost
  intro a hdD hd1 hs4 hsL hupper hlower htotal hclock hregular
  have hN1:1≤a.N:=by exact_mod_cast a.hn
  have hlo:(1/C0)*a.N^(-(2:ℝ)/3+m)*a.d≤a.E:=by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup:a.E≤a.d^2/Real.sqrt a.N:=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.hN)).mpr
      (by simpa only [mul_comm] using hupper)
  apply hnCost a hd1 hlo hup
  intro lam hlam alpha hattained
  have hlam0:0<lam:=(Real.rpow_pos_of_pos a.hN _).trans hlam.1
  obtain ⟨beta,_,hminimum⟩:=a.exists_minimum ⟨hlam0.le,hlam.2.le⟩
  let optimizer:ActualHighOnlyComparisonMinimum a lam:=
    ⟨alpha,hattained,fun beta=>hattained.symm ▸ hminimum beta⟩
  have hmass:a.s≤comparisonConditionalScale a.N delta a.E lam:=
    hsL.trans (comparison_conditional_scale_ge_lower hN1 hdelta.le
      a.hE a.hd hlam0 hlam.2.le)
  exact hnDensity a lam optimizer hlam0 hlam.2.le hdD hd1 hupper hlower
    htotal (hregular lam hlam alpha hattained) hs4 hmass (hclock alpha)

theorem eventually_actual_high_only_regular_child_failure_selects_irregular
    {m delta cl cu C0 D T:ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl:0<cl) (hcu:0<cu) (hclcu:cl≤cu) (hC0:0<C0):
    ∀ᶠn:ℕ in atTop,∀a:ActualHighOnlyComparisonData (n+1) delta,
      a.d≤D → a.d≤1 → a.s≤1/4 →
      a.s≤comparisonLowerScale a.N a.E a.d →
      Real.sqrt a.N*a.E≤a.d^2 → a.N^(-(2:ℝ)/3+m)*a.d≤C0*a.E →
      (∀u∈Icc (0:ℝ) 1,a.h u+a.b u≤T) →
      (∀alpha:a.Profile,NativePullbackClockRegularity alpha.val.val a.b a.h 0 1) →
      a.N^(20*delta)*a.E<a.cost (a.d^2) →
      ∃lam∈Ioo (a.N^(-10:ℝ)) (a.d^2),∃alpha:a.Profile,
        a.objective lam alpha=a.minimum lam ∧
        ∃r∈Icc (min (comparisonConditionalScale a.N delta a.E lam) 1) 1,
          alpha.val.val r<cl*r ∨ cu*r<alpha.val.val r:=by
  filter_upwards [eventually_actual_high_only_regular_child_cost_of_regular
    (D:=D) (T:=T) hm hdelta hroom hcl hcu hclcu hC0] with n hn
  intro a hdD hd1 hs4 hsL hupper hlower htotal hclock hfail
  by_contra hno
  push Not at hno
  have hcost:=hn a hdD hd1 hs4 hsL hupper hlower htotal hclock (by
    intro lam hlam alpha hattained r hr
    exact hno lam hlam alpha hattained r hr)
  exact not_lt_of_ge hcost hfail

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization

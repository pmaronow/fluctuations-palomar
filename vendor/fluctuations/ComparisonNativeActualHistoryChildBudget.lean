module

public import ComparisonNativeActualHistoryConditionalDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000

def NativeChildBarrierParameters.toOverlapContext {n : ℕ} {delta : ℝ}
    (c : NativeChildBarrierParameters n delta) : NativeOverlapContext n delta where
  E := c.E
  d := c.d
  hn := c.hn
  hE := c.hE
  hd := c.hd

theorem eventually_actual_history_child_cost_of_regular
    {margin delta cl cu C0 T : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀(child : NativeChildBarrierParameters (n+1) delta) (b h : ℝ→ℝ) (L : ℝ),
      0 < L → L ≤ child.d^2 → child.d ≤ 1 → L ≤ b 0 →
      MonotoneOn b (Icc (0:ℝ) 1) → MonotoneOn h (Icc (0:ℝ) 1) → 0 ≤ h 0 →
      Real.sqrt child.N*child.E ≤ child.d^2 →
      child.N^(-(2:ℝ)/3+margin)*child.d ≤ C0*child.E →
      ∀(ts : List ComparisonHistoryTerm) (B H : ℝ),
      (∀u,b u=B-historyMatrixReduction ts u) →
      (∀u,h u=H+historyFieldAddition ts u) →
      (∀t∈ts,0 ≤ t.lam) → B+H ≤ T →
      (∀lam∈Ioo (child.N^(-10:ℝ)) L,∀alpha : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          (n+1) b h child.d lam alpha=
          variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
            (n+1) b h child.d lam →
        ∀r∈Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
          cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
        (n+1) b h child.d L ≤ child.N^(20*delta)*child.E := by
  have hgamma : 0 < 1/C0 := one_div_pos.mpr hC0
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hsR : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
  have hq := hsR.eventually ((tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop 2))
  filter_upwards [eventually_actual_history_sweep_density_of_regular (T:=T) hm hdelta hroom
    hcl hcu hclcu hC0,hs.eventually (eventually_native_actual_child_cost_of_density hm hdelta hgamma),hq]
    with n hndensity hncost hnq
  intro child b h L hL hLd hd1 hLb hb hh hh0 hupper hlower ts B H hbHist hhHist hlamHist htotal hregular
  have hL1 : L ≤ 1 := by have hd:=child.hd; nlinarith
  have hup : child.E ≤ child.d^2/Real.sqrt (n+1:ℕ) := by
    exact (le_div_iff₀ (Real.sqrt_pos.mpr child.hN)).mpr (by simpa only [mul_comm] using hupper)
  have hlo : (1/C0)*child.N^(-(2:ℝ)/3+margin)*child.d ≤ child.E := by
    have hh := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hh
  apply hncost child b h L hL hL1 hLb hb hh hh0 hlo hup hnq
  intro lam hlam alpha hattained
  have hlam0 : 0 < lam := (Real.rpow_pos_of_pos child.hN _).trans hlam.1
  exact hndensity child.toOverlapContext alpha b h lam hlam0 (hlam.2.le.trans hLd) hd1
    (hlam.2.le.trans hLb) hb hh hh0 hupper hlower hattained (hregular lam hlam alpha hattained)
    ts B H hbHist hhHist hlamHist htotal

theorem eventually_actual_history_child_failure_selects_irregular
    {margin delta cl cu C0 T : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀(child : NativeChildBarrierParameters (n+1) delta) (b h : ℝ→ℝ) (L : ℝ),
      0 < L → L ≤ child.d^2 → child.d ≤ 1 → L ≤ b 0 →
      MonotoneOn b (Icc (0:ℝ) 1) → MonotoneOn h (Icc (0:ℝ) 1) → 0 ≤ h 0 →
      Real.sqrt child.N*child.E ≤ child.d^2 →
      child.N^(-(2:ℝ)/3+margin)*child.d ≤ C0*child.E →
      ∀(ts : List ComparisonHistoryTerm) (B H : ℝ),
      (∀u,b u=B-historyMatrixReduction ts u) →
      (∀u,h u=H+historyFieldAddition ts u) →
      (∀t∈ts,0 ≤ t.lam) → B+H ≤ T →
      child.N^(20*delta)*child.E < variableEndpointComparisonSweepCost
        child.hc child.hk child.hkc child.hm child.hM (n+1) b h child.d L →
      ∃lam∈Ioo (child.N^(-10:ℝ)) L,∃alpha : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          (n+1) b h child.d lam alpha=
          variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
            (n+1) b h child.d lam ∧
        ∃r∈Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
          alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r := by
  filter_upwards [eventually_actual_history_child_cost_of_regular (T:=T) hm hdelta hroom
    hcl hcu hclcu hC0] with n hn
  intro child b h L hL hLd hd1 hLb hb hh hh0 hupper hlower ts B H hbHist hhHist hlamHist htotal hfail
  by_contra hno
  push Not at hno
  have hregular : ∀lam∈Ioo (child.N^(-10:ℝ)) L,∀alpha : child.Profile,
      variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
        (n+1) b h child.d lam alpha=
        variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
          (n+1) b h child.d lam →
      ∀r∈Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
        cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r := by
    intro lam hlam alpha hattained r hr
    exact hno lam hlam alpha hattained r hr
  exact not_lt_of_ge (hn child b h L hL hLd hd1 hLb hb hh hh0 hupper hlower
    ts B H hbHist hhHist hlamHist htotal hregular) hfail

end OAI.SKFluctuations.LaplaceWindowFormalization

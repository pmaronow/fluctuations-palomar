module

public import ComparisonNativeActualConditionalDensity
public import ComparisonNativeActualInheritedHistoryGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

namespace NativeOverlapMinimum

theorem eventually_actual_history_conditional_density
    {margin delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.context.d ≤ 1 →
      a.xs=comparisonConditionalScale a.context.N delta a.context.E a.lam →
      ∀(ts : List ComparisonHistoryTerm) (B H : ℝ),
      (∀u,a.b u=B-historyMatrixReduction ts u) →
      (∀u,a.h u=H+historyFieldAddition ts u) →
      nativeActualSweepDensity a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM
        (n+1) a.b a.h a.context.d a.lam a.alpha ≤ a.context.N^(10*delta)*a.context.E := by
  filter_upwards [eventually_actual_conditional_density hm hdelta hroom hcl hcu hclcu hAz hC0 hCt]
    with n hn
  intro a hd1 hxs ts B H hb hh
  obtain ⟨Kb,Kh,hKb,hKh⟩ := a.inherited_history_clock_lipschitz ts B H hb hh
  exact hn a hd1 hxs Kb Kh hKb hKh

end NativeOverlapMinimum

theorem eventually_actual_history_sweep_density_of_regular
    {margin delta cl cu C0 T : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀(c : NativeOverlapContext (n+1) delta) (alpha : c.Profile)
        (b h : ℝ→ℝ) (lam : ℝ),
      0 < lam → lam ≤ c.d^2 → c.d ≤ 1 → lam ≤ b 0 →
      MonotoneOn b (Icc (0:ℝ) 1) → MonotoneOn h (Icc (0:ℝ) 1) → 0 ≤ h 0 →
      Real.sqrt c.N*c.E ≤ c.d^2 → c.N^(-(2:ℝ)/3+margin)*c.d ≤ C0*c.E →
      variableEndpointComparisonSweepObjective c.hc c.hk c.hkc c.hm c.hM (n+1) b h c.d lam alpha=
        variableEndpointComparisonSweepMinimum c.hc c.hk c.hkc c.hm c.hM (n+1) b h c.d lam →
      (∀r∈Icc (min (comparisonConditionalScale c.N delta c.E lam) 1) 1,
        cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      ∀(ts : List ComparisonHistoryTerm) (B H : ℝ),
      (∀u,b u=B-historyMatrixReduction ts u) →
      (∀u,h u=H+historyFieldAddition ts u) →
      (∀t∈ts,0 ≤ t.lam) → B+H ≤ T →
      nativeActualSweepDensity c.hc c.hk c.hkc c.hm c.hM (n+1) b h c.d lam alpha ≤
        c.N^(10*delta)*c.E := by
  have hevent := NativeOverlapMinimum.eventually_actual_history_conditional_density
    (Az:=1) (Ct:=1) (D:=1) (Bclock:=T) hm hdelta hroom hcl hcu hclcu
    (by norm_num) hC0 (by norm_num)
  filter_upwards [hevent] with n hn
  intro c alpha b h lam hlam hld hd1 hlb hb hh hh0 hupper hlower hattained hregular
    ts B H hbHist hhHist hlamHist htotal
  have hminimum := c.minimum_of_sweep_attained alpha b h hlam.le hb hlb hh hh0 hattained
  have htotal' : ∀u∈Icc (0:ℝ) 1,h u+b u ≤ T := by
    intro u _
    rw [hbHist,hhHist]
    linarith [actual_history_field_le_reduction ts hlamHist u]
  let a := c.conditionalMinimum alpha b h hlam hld hdelta.le hb hlb hh hh0 hminimum hd1
    hupper hlower htotal' hregular
  exact hn a hd1 rfl ts B H hbHist hhHist

end OAI.SKFluctuations.LaplaceWindowFormalization

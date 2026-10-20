module

public import ActualInitialUpperBound
public import ConcreteHighWallInputs

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal

theorem actual_upperPressureLedger_of_comparison_and_wall_mean
    {beta Ci Cw m : ℝ} (hbeta : 1 < beta) (hCi : 0 < Ci) (hCw : 1 ≤ Cw)
    (hm : 0 < m) (hmmax : m < 1/300)
    (hinitial : ∀ᶠ n : ℕ in atTop, actualInitialUpperComparison (beta^2) Ci m n)
    (hhigh : ∀ᶠ n : ℕ in atTop, ∀ hp : ConcreteHighWallGeometry m n,
      ∀ epsilon ∈ Ioo (0:ℝ) (beta^2), upperInitialEpsilon m n ≤ epsilon →
        concreteHighWallPhysicalInputs (beta^2) Cw m n hp epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      pressureIncrement beta m n ≤ C*upperPressureLedger m n := by
  have hT : 1 < beta^2 := by nlinarith
  let p := fun n epsilon => physicalShellPressure n (beta^2) (wallHighMass m n) epsilon
  obtain ⟨hcostpos,hcost⟩ := concreteHighWallPhysicalCost_eventually hT hCw hm hmmax
  have hwall : ∀ᶠ n : ℕ in atTop, ∀ epsilon : ℝ,
      upperInitialEpsilon m n ≤ epsilon → epsilon < beta^2 →
        p n (wallStep (beta^2) epsilon)-p n epsilon ≤
          (highWallCostConstant (beta^2) Cw+1)*upperWallStepLedger m n := by
    filter_upwards [concreteHighWallGeometry_eventually hm hmmax,hhigh,hcost,
      eventually_ge_atTop (1:ℕ)] with n hp hinput hcn hn
    intro epsilon heps0 hepsT
    have heps : epsilon ∈ Ioo (0:ℝ) (beta^2) :=
      ⟨(upperInitialEpsilon_mem hT hmmax hn).1.trans_le heps0,hepsT⟩
    have hs := concreteHighWall_step_of_physical_inputs (by linarith : 0 ≤ Cw)
      n hp heps heps0 (hinput hp epsilon heps heps0)
    have hc := hcn epsilon heps heps0
    have he := highWallComparisonError_le_ledger hm.le hn
    dsimp only [p]
    nlinarith
  have hslope : ∀ᶠ n : ℕ in atTop, ∀ epsilon : ℝ,
      upperInitialEpsilon m n ≤ epsilon → epsilon ≤ beta^2 →
        p n (beta^2)-p n epsilon ≤
          (n:ℝ)^(-(1:ℝ)/6+5*m)/4*(beta^2-epsilon) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    intro epsilon heps0 hepsT
    have hs1 : wallHighMass m n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hn) (by linarith)
    exact physicalShellPressure_terminal_slope n (by omega) (wallHighMass_pos m (by omega))
      hs1 ⟨((upperInitialEpsilon_mem hT hmmax hn).1.trans_le heps0).le,hepsT⟩
  obtain ⟨C,hC,hpressure⟩ := eventually_upperPressureLedger_of_wall_cost p hT hm hmmax
    (by positivity : 0 ≤ Ci^2/2+1) (by linarith : 0 ≤ highWallCostConstant (beta^2) Cw+1)
    (actual_initial_upper_bound hT hCi hm hmmax hinitial) hwall hslope
  refine ⟨C,hC,?_⟩
  filter_upwards [hpressure,eventually_gt_atTop (0:ℕ)] with n hn hnp
  rw [pressureIncrement_eq_physicalShell_gap beta hmmax n hnp]
  simpa only [p,wallHighMass,laplaceScale] using hn

theorem actual_completedCenteredLogLaplace_upper_of_comparison_and_wall_mean
    {beta Ci Cw m : ℝ} (hbeta : 1 < beta) (hCi : 0 < Ci) (hCw : 1 ≤ Cw)
    (hm : 0 < m) (hmmax : m < 1/300)
    (hinitial : ∀ᶠ n : ℕ in atTop, actualInitialUpperComparison (beta^2) Ci m n)
    (hhigh : ∀ᶠ n : ℕ in atTop, ∀ hp : ConcreteHighWallGeometry m n,
      ∀ epsilon ∈ Ioo (0:ℝ) (beta^2), upperInitialEpsilon m n ≤ epsilon →
        concreteHighWallPhysicalInputs (beta^2) Cw m n hp epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      completedCenteredLogLaplace beta (laplaceScale m n) n ≤ C*(n:ℝ)^(100*m) := by
  obtain ⟨C,hC,hpressure⟩ := actual_upperPressureLedger_of_comparison_and_wall_mean
    hbeta hCi hCw hm hmmax hinitial hhigh
  apply eventually_upper_of_pressure_ledger
    (fun n => completedCenteredLogLaplace beta (laplaceScale m n) n)
    (pressureIncrement beta m) hm hC.le _ hpressure
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact completedCenteredLogLaplace_eq_pressureIncrement beta m hn

end OAI.SKFluctuations.LaplaceWindowFormalization

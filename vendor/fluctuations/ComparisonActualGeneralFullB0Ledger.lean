module

public import ComparisonSignedCavitySecondLowFullCenteredResourceReadout
public import ComparisonSignedCavitySecondLowInheritedCenteredOccupiedCReplacementBudgetAlong
public import ComparisonSignedCavitySecondLowActualHistoryFreshReplacementModulusAlong
public import ComparisonSignedCavitySecondLowInheritedWholeObservedSavedRate

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem actual_general_full_B0_abs_le_replacement_prices
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (initial residual occupied : ℝ)
    (Hfresh : |nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU P| ≤ initial+residual)
    (Hoccupied : |nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU P| ≤ occupied) :
    |nativeSecondLowFreshFullB0Source n q U b h K T s star P| ≤ initial+residual+occupied := by
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hchi : |chi^2|≤1:=by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg chi) (native_second_low_original_chi_abs_le_one ho U K) 2).trans_eq (by norm_num)
  have Hprice : |chi^2*nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU P|≤occupied:=by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right Hchi (abs_nonneg _)).trans ((one_mul _).le.trans Hoccupied)
  have Heq : nativeSecondLowFreshFullB0Source n q U b h K T s star P=
      nativeSecondLowFreshB0MinusCReplacementSource n q U b h K T s star hU P+
      chi^2*nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU P:=by
    dsimp only [nativeSecondLowFreshFullB0Source,nativeSecondLowFreshB0MinusCReplacementSource,chi]
    ring
  rw [Heq]
  exact (abs_add_le _ _).trans (add_le_add Hfresh Hprice)

end OAI.SKFluctuations.Cavity

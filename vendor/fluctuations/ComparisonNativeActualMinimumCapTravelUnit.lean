module

public import ComparisonNativeActualMinimumCapTravel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 3000000

theorem eventually_actual_minimum_cap_travel_lt_one
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.cavityCapTravel < 1 := by
  have hepsilon : 0 < 1/(|D|+1) := by positivity
  have htravel := (tendsto_add_atTop_nat 1).eventually
    (eventually_comparisonTravel_small (C:=C0) (D:=D) hC0 hroom hepsilon)
  filter_upwards [htravel] with n hn
  intro a
  have hs : comparisonLowerScale (n+1 : ℕ) a.context.E a.context.d ≤ a.context.d := by
    unfold comparisonLowerScale
    exact (div_le_iff₀ a.context.hd).mpr (by simpa only [pow_two] using a.hupper)
  have hc : a.cavityCapTravel ≤ (1/(|D|+1))*|D| :=
    (hn a.context.E a.context.d a.context.hE a.context.hd a.hdD a.hupper a.hlower).trans
      (mul_le_mul_of_nonneg_left (hs.trans (a.hdD.trans (le_abs_self D))) hepsilon.le)
  apply hc.trans_lt
  rw [one_div_mul_eq_div]
  exact (div_lt_one (by positivity : 0 < |D|+1)).mpr (by linarith)

end OAI.SKFluctuations.LaplaceWindowFormalization

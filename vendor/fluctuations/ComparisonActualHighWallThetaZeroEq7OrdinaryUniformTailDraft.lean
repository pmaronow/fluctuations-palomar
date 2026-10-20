module

public import ComparisonActualHighWallThetaZeroEq7OrdinaryPieceNormalizationDraft
public import ComparisonActualHighWallThetaZeroEq7OrdinaryCutoffDraft
public import ComparisonActualHighWallThetaZeroSelectedScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem eventually_eq7_low_post_real_numeric_gates_draft
    (C0 C qLow qPost eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℝ in atTop,
      1 ≤ N ∧ C0 ≤ N ∧ C ≤ N ∧ 1+16*C ≤ N ∧
      1 ≤ Real.log N ∧ Real.log N ≤ N^eps ∧
      72 ≤ N^3 ∧
      qLow^4*(1+16*C)^2*(16*C)^2 ≤ N ∧
      qPost^4*(1+16*C)^2*(16*C)^2 ≤ N := by
  have Hlog : ∀ᶠ N : ℝ in atTop, 1 ≤ Real.log N :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have HlogPow := comparison_eq7_ordinary_eventual_log_gate_draft heps
  have Hlow := comparison_eq7_ordinary_cutoff_numeric_gates_eventually_draft
    qLow (1+16*C) C
  have Hpost := comparison_eq7_ordinary_cutoff_numeric_gates_eventually_draft
    qPost (1+16*C) C
  filter_upwards [eventually_ge_atTop C0, eventually_ge_atTop C,
    eventually_ge_atTop (1+16*C), Hlog, HlogPow, Hlow, Hpost]
      with N hC0 hC hY hlog hlogPow hlow hpost
  exact ⟨hlow.1,hC0,hC,hY,hlog,hlogPow,hlow.2.1,
    hlow.2.2,hpost.2.2⟩

theorem eventually_eq7_low_post_original_q_numeric_gates_draft
    {m delta cl cu Az Ct D Bclock : ℝ}
    (C0 C qLow qPost eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock,
        1 ≤ Q.data.N ∧ C0 ≤ Q.data.N ∧ C ≤ Q.data.N ∧
        1+16*C ≤ Q.data.N ∧
        1 ≤ Real.log Q.data.N ∧
        Real.log Q.data.N ≤ Q.data.N^eps ∧
        72 ≤ Q.data.N^3 ∧
        qLow^4*(1+16*C)^2*(16*C)^2 ≤ Q.data.N ∧
        qPost^4*(1+16*C)^2*(16*C)^2 ≤ Q.data.N := by
  have HN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have H := HN.eventually
    (eventually_eq7_low_post_real_numeric_gates_draft
      C0 C qLow qPost eps heps)
  filter_upwards [H] with n hn
  intro Q
  simpa only [ActualHighWallData.N] using hn

end OAI.SKFluctuations.LaplaceWindowFormalization

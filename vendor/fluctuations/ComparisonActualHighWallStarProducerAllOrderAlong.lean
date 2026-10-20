module

public import ComparisonActualHighWallSlowWindowProducerAlong
public import ComparisonActualHighWallStarAllOrderAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem exists_actual_high_wall_calibrated_all_order_star_sequence_along
    {m delta cl cu Az C0 Ct D Bclock T0 L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT0 : 0 < T0) (hL : 0 < L)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (hT : ∀n,T0≤(M n).data.T) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
        (M n) ((M n).data.d) L Cs (w n)) ∧
      ∀p : ℕ,∃Craw : ℝ,0 < Craw ∧ ActualHighWallStarOrderSavingAlong p Craw
        (actualSlowWindowExponent m delta/64) dim M (fun n=>(M n).data.d) w := by
  obtain ⟨Cs,hCs,w,hw⟩:=ActualHighWallOverlapMinimum.exists_actual_high_wall_calibrated_slow_window_sequence_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hT0 hL dim hdim M (fun n=>(M n).data.d)
    (fun n=>by rw [hfixed n]) (fun _=>le_rfl) hWlim hsRatio hT
  refine ⟨Cs,hCs,w,hw,?_⟩
  intro p
  exact eventually_actual_high_wall_star_order_at_slow_window_along p hm hdelta hroom
    hcl hcu hAz hC0 hCt hL dim hdim M hfixed hWlim Cs hCs w hw

end OAI.SKFluctuations.LaplaceWindowFormalization

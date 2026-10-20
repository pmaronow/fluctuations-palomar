module

public import ComparisonActualHighWallSquarePairProducerAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter Set Hierarchy Cavity NativeOverlapMinimum
open scoped Topology

theorem actual_high_wall_square_pair_budgets_at_calibrated_star_along
    {m delta cl cu Az C0 Ct D Bclock L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hL : 0 < L) (Cmass : ℝ) (hCm : 0 ≤ Cmass)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n)) :
    ∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
      ActualHighWallSquareResourcePairBudgetOnRetainedMasterAlong degree A
        (actualSlowWindowExponent m delta/128) Cmass dim M w := by
  have hc:=actualSlowWindowExponent_pos hm hdelta hroom
  have Hc:=(actualSlowWindowExponent_bounds hm hdelta).2.2
  have hsite : actualSlowWindowExponent m delta/64 < (5:ℝ)/6+m:=by linarith
  have Hstar (p : ℕ):=eventually_actual_high_wall_star_order_at_slow_window_along
    p hm hdelta hroom hcl hcu hAz hC0 hCt hL dim hdim M hfixed hWlim Cs hCs w hw
  have H:=actual_high_wall_square_pair_budgets_from_all_order_star_along
    hm hdelta hroom hcl hcu hAz hC0 hCt Cmass hCm (by positivity) hsite
    dim hdim M hfixed hWlim w Hstar
  simpa only [show (actualSlowWindowExponent m delta/64)/2=
    actualSlowWindowExponent m delta/128 by ring] using H

end OAI.SKFluctuations.LaplaceWindowFormalization

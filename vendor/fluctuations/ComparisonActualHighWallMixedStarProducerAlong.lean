module

public import ComparisonActualHighWallStarProjectionPowersAlong
public import ComparisonActualHighWallStarProducerAllOrderAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

def actualHighWallProjectedStarSaving (m delta : ℝ) : ℝ:=actualSlowWindowExponent m delta/256

theorem actualHighWallProjectedStarSaving_pos {m delta : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m) :
    0< actualHighWallProjectedStarSaving m delta:=by
  unfold actualHighWallProjectedStarSaving
  exact div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)

theorem exists_actual_high_wall_mixed_projection_star_sequence_along
    {m delta cl cu Az C0 Ct D Bclock T0 L : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hT0 : 0< T0) (hL : 0< L) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (hT : ∀n,T0≤ (M n).data.T) :
    ∃Cs : ℝ,0< Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
        (M n) ((M n).data.d) L Cs (w n)) ∧
      (∀p : ℕ,ActualHighWallRestStarMomentOnEveryFinalNetAlong p
        (actualHighWallProjectedStarSaving m delta) M (fun n=>(M n).data.d) w) ∧
      ∀j k : ℕ,ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong j k
        (actualHighWallProjectedStarSaving m delta) M (fun n=>(M n).data.d) w := by
  let W:=fun n=>(M n).data.d
  let kappa:=actualSlowWindowExponent m delta/64
  have hkappa : 0< kappa:=by dsimp only [kappa];positivity [actualSlowWindowExponent_pos hm hdelta hroom]
  have hc1:=actualSlowWindowExponent_bounds hm hdelta
  have hetaBound:=(actualMassSavingExponent_bounds m delta).1
  have hkroom : kappa/2< (5:ℝ)/6+m:=by dsimp only [kappa];linarith [hc1.1]
  obtain ⟨Cs,hCs,w,hw,Hsource⟩:=exists_actual_high_wall_calibrated_all_order_star_sequence_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hT0 hL dim hdim M hfixed hWlim hsRatio hT
  have Hnative (p : ℕ) : ActualHighWallStarMomentOnEveryFinalNetAlong p (kappa/2) M W w:=by
    obtain ⟨Craw,_hCraw,H⟩:=Hsource p
    exact actual_high_wall_star_order_saving_on_every_final_net_along p hkappa dim hdim M W
      (fun n=>(M n).data.hd) w H
  have HE : (kappa/2)/2=actualHighWallProjectedStarSaving m delta:=by
    unfold kappa actualHighWallProjectedStarSaving;ring
  have Hrest (p : ℕ) : ActualHighWallRestStarMomentOnEveryFinalNetAlong p
      (actualHighWallProjectedStarSaving m delta) M W w:=by
    have HR:=actual_high_wall_star_every_final_net_to_rest_along p hC0 (by positivity : 0< kappa/2)
      hkroom dim hdim M W (fun n=>by dsimp only [W];rw [hfixed n]) hWlim w (Hnative p)
    rw [HE] at HR
    exact HR
  have Hpower (p : ℕ) : ActualHighWallStarProjectionPowerOnEveryFinalNetAlong p
      (actualHighWallProjectedStarSaving m delta) M W w:=
    actual_high_wall_rest_star_to_projection_powers_along p M W w (Hrest p)
  exact ⟨Cs,hCs,w,hw,Hrest,fun j k=>actual_high_wall_star_projection_powers_to_mixed_along
    j k M W (fun n=>(M n).data.hd.le) w Hpower⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonActualHighWallSlowWindowLaterHalfProducerAlong
public import ComparisonActualHighWallStrongSourceMassesAlong
public import ComparisonActualHighWallStrongSourceReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory Hierarchy LaplaceWindowFormalization NativeOverlapMinimum NativeStarBuffer
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem exists_actual_high_wall_strong_window_sources_along
    {m delta cl cu Az C0 Ct D Bclock T0 : ℝ}
    (Ctarget Cband Cx c Rmacro : ℝ)
    (htarget : 0 ≤ Ctarget) (hband : 0 ≤ Cband)
    (hCx : 0 < Cx) (hc : 0 < c) (hmacro : 0 < Rmacro)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hT0 : 0 < T0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (hT : ∀n,T0 ≤ (M n).data.T) :
    ∃L Cenv Ccut Cs : ℝ,0 < L ∧ 1 ≤ Cenv ∧ 0 < Ccut ∧ 0 < Cs ∧
      calibratedBandStart cu Az+4*L ≤ Cenv ∧
      ∃w : ℕ→ActualSlowWindowChoice,∀ᶠn in atTop,
        ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
          (M n) ((M n).data.d) L Cs (w n) ∧
        Ctarget*(M n).data.d < (w n).star.val ∧
        (w n).star.val ≤ Cenv*(M n).data.d ∧
        (∀r : ℝ,r ≤ Cband*(M n).data.d → r ≤ 1 →
          (M n).alpha.val.val r < (w n).star.val) ∧
        ∃source outer : PositiveMass,
          source.val=Ccut*(M n).data.d ∧
          outer.val=(Ccut+1)*(M n).data.d ∧
          ActualHighWallStrongSourceMasses (M n) Cenv Ccut Cx c Rmacro source outer := by
  let L:=Ctarget+cu*(Cband+Az)+1
  let a:=calibratedBandStart cu Az
  let Cenv:=max 1 (a+4*L)
  have hL : 0 < L:=by dsimp only [L];positivity
  have ha : 0 < a:=calibrated_band_start_pos hcu hAz
  have hmass : Ctarget ≤ calibratedBandStart cu Az+2*L:=by
    dsimp only [L,a] at *
    have H:=mul_nonneg hcu.le (add_nonneg hband hAz)
    linarith
  have hradius : cu*(Cband+Az) ≤ calibratedBandStart cu Az+2*L:=by
    dsimp only [L,a] at *
    have H:=mul_nonneg hcu.le (add_nonneg hband hAz)
    linarith
  have henv : 1 ≤ Cenv:=le_max_left _ _
  have hbandenv : calibratedBandStart cu Az+4*L ≤ Cenv:=le_max_right _ _
  obtain ⟨Cs,hCs,w,hw⟩:=
    ActualHighWallOverlapMinimum.exists_actual_high_wall_calibrated_slow_window_later_half_sequence_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hT0 hL dim hdim M
      (fun n=>(M n).data.d) (fun n=>(hfixed n).le) (fun _=>le_rfl) hdlim hsRatio hT
  obtain ⟨Ccut,hcut,Hsources⟩:=exists_actual_high_wall_strong_source_masses_along
    Cenv Cx c Rmacro (zero_le_one.trans henv) hCx hc hmacro hcl hcu hAz
    dim M hfixed hdlim
  refine ⟨L,Cenv,Ccut,Cs,hL,henv,hcut,hCs,hbandenv,w,?_⟩
  filter_upwards [hw,Hsources] with n hn hnsource
  have hstar:=ActualHighWallOverlapMinimum.calibrated_slow_window_later_half_star_after_target
    (M n) (M n).data.hd hmass (w n) hn
  have hupper:=(actual_high_wall_calibrated_star_mass_mem_band hn.1).2
  have hupper' : (w n).star.val ≤ Cenv*(M n).data.d:=hupper.trans
    (mul_le_mul_of_nonneg_right hbandenv (M n).data.hd.le)
  refine ⟨hn.1,hstar,hupper',?_,hnsource⟩
  intro r hr hr1
  exact ActualHighWallOverlapMinimum.calibrated_slow_window_later_half_covers_radius_band
    hcu.le hAz (M n) (M n).data.hd hband (hfixed n).le hr hr1 hradius (w n) hn

end OAI.SKFluctuations.Cavity

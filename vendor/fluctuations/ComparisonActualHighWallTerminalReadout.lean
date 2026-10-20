module

public import ComparisonActualHighWallTerminalRetainedAlong
public import ComparisonActualHighWallSquarePairAtWindowAlong
public import ComparisonActualHighWallRadiusRetag

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem ActualHighWallFourTerminalBudgetsOnGrid.initial_target
    {n depth : ℕ} {m delta cl cu Az C0 Ct D Bclock saving Cmass : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {u : PositiveMass} {as : List PositiveMass}
    (H : ActualHighWallFourTerminalBudgetsOnGrid depth saving Cmass M u as)
    (U i : ℕ) (hi : i ≤ retainedMassPrefixIndex u.val as)
    (hs : retainedMassPrefixIndex u.val as < U) (hU : U ≤ as.length)
    (hmass : partitionPoint 0 as i ≤ Cmass*M.data.d) :
    let st:=nativeActualInitialState (S:=Spin n×Bool) as i (retainedMassPrefixIndex u.val as)
      0 (hi.trans (hs.le.trans hU))
    |((actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth [st]).map
      (actualGeneralFourStateResponse M.bf M.hf U M.data.d)).sum| ≤
      2*(((n+1:ℕ):ℝ)^(-saving)*M.data.d^3) := by
  dsimp only
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i (retainedMassPrefixIndex u.val as)
    0 (hi.trans (hs.le.trans hU))
  have HG : NativeActualResourceGenerated i (retainedMassPrefixIndex u.val as) U
      [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have HL:=nativeActualInitialState_leaves_le (S:=Spin n×Bool) as i
    (retainedMassPrefixIndex u.val as) 0 (hi.trans (hs.le.trans hU))
  have HT:=H U i hi hs hU st [.initial] HG (Or.inr ⟨rfl,rfl⟩) hmass (HL.trans (by norm_num))
  simpa only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,mul_one] using HT

theorem ActualHighWallFourTerminalBudgetsOnGrid.constant_source_children
    {n depth : ℕ} {m delta cl cu Az C0 Ct D Bclock saving Cmass : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {u : PositiveMass} {as : List PositiveMass}
    (H : ActualHighWallFourTerminalBudgetsOnGrid depth saving Cmass M u as)
    (hCm : 0 ≤ Cmass) (ho : MassOrdered 0 as)
    (U : ℕ) (hs : retainedMassPrefixIndex u.val as < U) (hU : U ≤ as.length) :
    |((actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
      (actualGeneralConstantSourceChildren (n:=n) M.bf M.hf as
        (retainedMassPrefixIndex u.val as) U hs hU)).map
      (actualGeneralFourStateResponse M.bf M.hf U M.data.d)).sum| ≤
      12*(((n+1:ℕ):ℝ)^(-saving)*M.data.d^3) := by
  apply actual_general_constant_source_children_centered_terminal_abs_le
    M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)
    ho hs hU M.data.d depth (mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg M.data.hd.le _))
  intro Q hQ
  have HG:=actualGeneralConstantSourceChildren_valid M.bf M.hf hs hU Q hQ
  have HD:=actualGeneralConstantSourceChildren_generation M.bf M.hf hs hU Q hQ
  have HL:=actualGeneralConstantSourceChildren_leaves M.bf M.hf hs hU Q hQ
  apply H U 0 (Nat.zero_le _) hs hU Q [] HG (Or.inl ⟨rfl,HD⟩) _ HL
  simp only [partitionPoint,partitionValues_zero,id_eq]
  exact mul_nonneg hCm M.data.hd.le

theorem exists_actual_high_wall_four_cubic_terminal_at_calibrated_star_along
    {m delta cl cu Az C0 Ct D Bclock L T0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hL : 0 < L) (hT0 : 0 < T0) (Cmass : ℝ) (hCm : 0 ≤ Cmass)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hT : ∀n,T0 ≤ (M n).data.T)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n)) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold ≤ depth →
        ActualHighWallFourTerminalOnRetainedMasterAlong depth saving Cmass dim M w := by
  let cK:=3*T0*(starMassBandConstant cu Az/cu)/8
  have hc : 0 < starMassBandConstant cu Az/cu:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have hcK : 0 < cK:=by dsimp only [cK];positivity
  have Hclock : ∀ᶠn in atTop,cK*(M n).data.d ≤
      actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val:=by
    filter_upwards [hw] with n hn
    have HK:=(M n).calibrated_slow_window_clock_lower hn
    apply le_trans _ HK
    have HM:=mul_le_mul_of_nonneg_right (hT n)
      (show 0 ≤ 3*(starMassBandConstant cu Az/cu)/8*(M n).data.d by
        exact mul_nonneg (by positivity) (M n).data.hd.le)
    dsimp only [cK]
    nlinarith only [HM]
  have Hpair:=actual_high_wall_square_pair_budgets_at_calibrated_star_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hL Cmass hCm dim hdim M hfixed hWlim Cs hCs w hw
  exact exists_actual_high_wall_four_cubic_terminal_of_pair_budgets_along
    hm hC0 (by have H:=actualSlowWindowExponent_pos hm hdelta hroom;positivity)
    hcK dim hdim M hfixed hWlim w Hclock Hpair

end OAI.SKFluctuations.Cavity

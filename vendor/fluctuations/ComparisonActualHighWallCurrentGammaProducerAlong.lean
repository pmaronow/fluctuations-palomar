module

public import ComparisonActualHighWallCurrentCubicRowAlong
public import ComparisonActualHighWallMixedStarProducerAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
variable {dim : ℕ→ℕ}

theorem actual_high_wall_same_star_current_Gamma_cubic_rows_along
    {m delta eta saving cl cu Az C0 Ct D Bclock : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta) (hsaving : 0 ≤ saving)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k,ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∀a b d : ℕ,ActualHighWallCurrentProjectedCubicRowOnEveryFinalNetAlong a b d eta Cmass M W w := by
  intro a b d
  obtain ⟨Ai,hAi,As,hAs,Ap,hAp,HI,HS,HP⟩:=actual_high_wall_same_star_normalized_reset_bounds_along
    a b d Cmass hCm hsaving hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hdim M W hcanonical hWlim hfixed w Hmixed
  have hxW n : (M n).xs ≤ W n:=by rw [hcanonical,hfixed n]
  exact actual_high_wall_current_projected_cubic_row_from_reset_along
    (actual_high_wall_reset_incoming_cubic_row_from_normalized_along heta hAi.le hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hdim M W hxW hWlim hfixed HI)
    (actual_high_wall_reset_star_incoming_cubic_row_from_normalized_along heta hAs.le hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hdim M W hxW hWlim hfixed HS)
    (actual_high_wall_reset_power_cubic_row_from_normalized_along heta hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hdim M W hxW hWlim hfixed HP)

theorem exists_actual_high_wall_current_Gamma_cubic_star_sequence_along
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
      (∀j k : ℕ,ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong j k
        (actualHighWallProjectedStarSaving m delta) M (fun n=>(M n).data.d) w) ∧
      ∀Cmass : ℝ,1≤ Cmass→∀a b d : ℕ,
        ActualHighWallCurrentProjectedCubicRowOnEveryFinalNetAlong a b d
          (actualMassSavingExponent m delta/256) Cmass M (fun n=>(M n).data.d) w := by
  obtain ⟨Cs,hCs,w,hw,_Hrest,Hmixed⟩:=exists_actual_high_wall_mixed_projection_star_sequence_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hT0 hL dim hdim M hfixed hWlim hsRatio hT
  have heta : 0< actualMassSavingExponent m delta/256:=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have hgap : 2*(actualMassSavingExponent m delta/256)<6*m:=by
    have H:=(actualMassSavingExponent_bounds m delta).2.1
    nlinarith
  refine ⟨Cs,hCs,w,hw,Hmixed,?_⟩
  intro Cmass hCm
  exact actual_high_wall_same_star_current_Gamma_cubic_rows_along
    Cmass hCm heta (actualHighWallProjectedStarSaving_pos hm hdelta hroom).le
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hdim M (fun n=>(M n).data.d)
    (fun _=>rfl) hWlim hfixed w Hmixed

end OAI.SKFluctuations.LaplaceWindowFormalization

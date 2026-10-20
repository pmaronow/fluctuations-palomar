module

public import ComparisonActualHighWallResetPowerNormalizedRateAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000
variable {dim : ℕ→ℕ}

theorem actual_high_wall_same_star_normalized_reset_bounds_along
    {m delta eta saving cl cu Az C0 Ct D Bclock : ℝ}
    (a b d : ℕ) (Cmass : ℝ) (hCm : 1 ≤ Cmass) (hsaving : 0 ≤ saving)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k,ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∃Ai : ℝ,0 < Ai ∧∃As : ℝ,0 < As ∧∃Ap : ℝ,0 ≤ Ap ∧
      ActualHighWallNormalizedResetIncomingOnEveryFinalNetAlong a b d eta Cmass Ai Ap M W w ∧
      ActualHighWallNormalizedResetStarIncomingOnEveryFinalNetAlong a b d eta Cmass As Ap M W w ∧
      ActualHighWallNormalizedResetPowerOnEveryFinalNetAlong b d eta Cmass Ap M W w := by
  obtain ⟨Cp,hCp,Ch,hCh,HI⟩:=eventually_actual_high_wall_canonical_incoming_product_from_same_star_along
    hdim a 0 d Bclock Cmass (by linarith)
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hfixed w (Hmixed 0 d)
  obtain ⟨Cstar,hCstar,Chstar,hChstar,HS⟩:=eventually_actual_high_wall_canonical_star_incoming_product_from_same_star_along
    hdim a 0 d Bclock Cmass (by linarith)
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hfixed w (Hmixed 0 d)
  have HP j:=eventually_actual_high_wall_canonical_power_product_from_same_star_along
    hdim b j (d-1-j) Bclock Cmass (by linarith)
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hfixed w (Hmixed (2*j) (2*(d-1-j)))
  choose Cpower hCpower Cbase hCbase Hpower using HP
  have hC j : 0 ≤ Cpower j ∧ 0 ≤ Cbase j:=⟨(hCpower j).le,(hCbase j).le⟩
  have HX n : (M n).xs ≤ W n:=by rw [hcanonical,hfixed n]
  have Hin:=actual_high_wall_generated_reset_paired_incoming_from_canonical_along hCp.le hCh.le hC
    (actual_high_wall_canonical_paired_incoming_from_products_along HI Hpower)
  have Hstar:=actual_high_wall_generated_reset_paired_star_incoming_from_canonical_along hCstar.le hChstar.le hC
    (actual_high_wall_canonical_paired_star_incoming_from_products_along HS Hpower)
  have Hpow:=actual_high_wall_generated_reset_power_from_canonical_along hC Hpower
  refine ⟨Cp*Ch^a,by positivity,Cstar*Chstar^a*Real.sqrt (1+Cmass),by positivity,
    ∑j∈Finset.range d,Cpower j*(Cbase j)^b,?_,
    actual_high_wall_normalized_reset_incoming_from_actual_along hsaving hCm hCp.le hCh.le hC HX Hin,
    actual_high_wall_normalized_reset_star_incoming_from_actual_along hsaving hCm hCstar.le hChstar.le hC HX Hstar,
    actual_high_wall_normalized_reset_power_from_actual_along hsaving hCm hC HX Hpow⟩
  exact Finset.sum_nonneg fun j _=>mul_nonneg (hC j).1 (pow_nonneg (hC j).2 _)

end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeActualLocalTemperatureCouplingAlong
public import ComparisonNativeActualHistoryNearBareClocks
public import ComparisonNativeActualHistoryScalarEndpointLimits
public import ComparisonNativeActualSelectedBadHistoryInitialMismatchAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum

theorem inherited_local_temperature_scalar_quantile_eq_mixed_of_root
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (t : ℝ) (hroot : M.h 0=0) {u : ℝ} (hu : 0 ≤ u) :
    actualScalarClockQuantile t (n+1) M.bf M.hf u=
      actualMixedClock (n+1) M.bf M.hf u/t := by
  by_cases hu0:u=0
  · subst u
    simp only [actualScalarClockQuantile,le_refl,ite_true,actualMixedClock,
      M.inherited_zero_root_field hroot,NNReal.coe_zero,zero_add,
      orderedPathS,orderedPathPair_zero,mul_zero,zero_div]
  · exact actualScalarClockQuantile_on (n+1) M.bf M.hf (lt_of_le_of_ne hu (Ne.symm hu0))

theorem actual_selected_bad_history_local_temperature_initial_scalar_radius_coupling_along
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell)
    (hlocal : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |actualMixedClock (dim n+1) (M n).bf (M n).hf u/(T-epsilon)-(M n).R u|)/(W n)^2)
      atTop (𝓝 0) := by
  have hT:0 < T:=hlocal.trans_le (sub_le_self T hepsilon)
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity
    dim root M epsilon shell hb hh Hhistory
  have Htotal:=actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory
  have Hnear:=actual_selected_bad_shell_history_near_bare_clocks
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    epsilon shell hshell hb hh Hhistory W (Eventually.of_forall hxs) hWlim
  have Hcouple:=regular_initial_local_temperature_scalar_radius_coupling_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim Hclock hT hlocal
    (Htotal.mono fun _ hn=>hn.1) C 1 1 hC (by norm_num) (by norm_num)
    (Hnear C 1 hC.le (by norm_num))
  apply Hcouple.congr'
  filter_upwards [Htotal] with n hn
  have hCW:0 ≤ C*W n:=mul_nonneg hC.le ((M n).hxs.trans_le (hxs n)).le
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hCW] at hu
  dsimp only
  rw [(M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root (T-epsilon) hn.2 hu.1]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

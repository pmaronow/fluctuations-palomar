module

public import ComparisonNativeActualRadiusStripIntegral
public import ComparisonNativeActualHistoryRadiusStripGeometryAlong
public import ComparisonNativeCavityRadiusPolynomialEventualAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_radius_strip_thermal_polynomial_bound_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D T c0 c C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (epsilon shell : ℝ) (hshell : 0 < shell)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ∀ᶠn in atTop,
      (∫r in (M n).actualRadiusTargetStrip c C,(M n).cavityRadiusPointDefect r)/(M n).xs^3 ≤
        ((dim n+1:ℕ):ℝ)^(-min (delta/64) (1/16)) := by
  have Hg := ActualSelectedBadHistoryChain.eventually_radius_strip_geometry
    hcl hcu.le hAz hxs epsilon shell c C hshell hc hb hh Hhistory
  have Hpoly := actual_minimum_cavity_radius_band_eventually_polynomial_bound_along
    Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt
    (actual_radius_strip_constant_ge_one cl Az c C) hc dim hdim M
    (fun n=>(M n).xs) (fun n=>(M n).actualRadiusStripLower c)
    (fun n=>(M n).actualRadiusStripUpper c C) (Hg.mono (by
      intro n hn
      obtain ⟨ha,haz,hz,hxz,hzC,hmass,_hbranch,hLip⟩ := hn
      exact ⟨ha,haz,hz,le_rfl,hxz,hzC,hmass.ge,hLip⟩))
  filter_upwards [Hg,Hpoly] with n hn hp
  exact (div_le_div_of_nonneg_right
    ((M n).actual_radius_target_strip_integral_le c C hn.1.le hn.2.2.1)
    (pow_pos (M n).hxs 3).le).trans hp

theorem actual_selected_bad_history_radius_strip_thermal_tendsto_zero_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D T c0 c C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (epsilon shell : ℝ) (hshell : 0 < shell)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    Tendsto (fun n=>
      (∫r in (M n).actualRadiusTargetStrip c C,(M n).cavityRadiusPointDefect r)/(M n).xs^3)
      atTop (𝓝 0) := by
  have hp : 0 < min (delta/64) (1/16:ℝ) := lt_min (by positivity) (by norm_num)
  have Hpow : Tendsto (fun n=>((dim n+1:ℕ):ℝ)^(-min (delta/64) (1/16))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  apply squeeze_zero' _
    (actual_selected_bad_history_radius_strip_thermal_polynomial_bound_along
      Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hc dim hdim root M hxs
      epsilon shell hshell hb hh Hhistory) Hpow
  exact Eventually.of_forall (fun n=>div_nonneg
    ((M n).actual_radius_target_strip_integral_nonneg c C) (pow_pos (M n).hxs 3).le)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

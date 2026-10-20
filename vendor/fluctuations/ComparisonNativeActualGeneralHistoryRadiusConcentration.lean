module

public import ComparisonNativeCavityRadiusSingleCutPolynomial
public import ComparisonNativeActualRadiusStripIntegral
public import ComparisonNativeActualGeneralHistoryContext

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_radius_strip_thermal_polynomial_bound_along_weak_general
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D T c0 c C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0) :
    ∀ᶠn in atTop,
      (∫r in (M n).actualRadiusTargetStrip c C,(M n).cavityRadiusPointDefect r)/(M n).xs^3 ≤
        ((dim n+1:ℕ):ℝ)^(-min (delta/64) (1/16)) := by
  have hsmall : ∀ᶠn in atTop,c*(M n).xs ≤ 1 := by
    have H : Tendsto (fun n=>c*(M n).xs) atTop (𝓝 0) := by
      simpa only [mul_zero] using hxs.const_mul c
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have hbig : ∀ᶠn in atTop,actualRadiusStripConstant cl Az c C*(M n).xs ≤ 1 := by
    have H : Tendsto (fun n=>actualRadiusStripConstant cl Az c C*(M n).xs) atTop (𝓝 0) := by
      simpa only [mul_zero] using hxs.const_mul (actualRadiusStripConstant cl Az c C)
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hgeometry : ∀ᶠn in atTop,
      0 < (M n).actualRadiusStripLower c ∧
      (M n).actualRadiusStripLower c ≤ (M n).actualRadiusStripUpper c C ∧
      (M n).actualRadiusStripUpper c C ≤ 1 ∧
      (M n).xs ≤ (M n).xs ∧
      (M n).actualRadiusStripUpper c C ≤ actualRadiusStripConstant cl Az c C*(M n).xs ∧
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).actualRadiusStripLower c) ∧
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
    filter_upwards [hsmall,hbig,G.pullback] with n hn hn' hreg
    obtain ⟨ha,haz,hz,hxz,hsize,hmass,_hstrip⟩:=
      (M n).actual_radius_strip_geometry hcl hAz hc hn hn'
    exact ⟨ha,haz,hz,le_rfl,hsize,hmass.ge,hreg⟩
  have Hpoly := actual_minimum_cavity_radius_single_cut_polynomial_bound_along
    Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt
    (actual_radius_strip_constant_ge_one cl Az c C) hc dim hdim M
    (fun n=>(M n).xs) (fun n=>(M n).actualRadiusStripLower c)
    (fun n=>(M n).actualRadiusStripUpper c C) Hgeometry
  filter_upwards [Hgeometry,Hpoly] with n hn hp
  exact (div_le_div_of_nonneg_right
    ((M n).actual_radius_target_strip_integral_le c C hn.1.le hn.2.2.1)
    (pow_pos (M n).hxs 3).le).trans hp

theorem actual_selected_bad_history_radius_strip_thermal_tendsto_zero_along_weak_general
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D T c0 c C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0) :
    Tendsto (fun n=>(∫r in (M n).actualRadiusTargetStrip c C,
      (M n).cavityRadiusPointDefect r)/(M n).xs^3) atTop (𝓝 0) := by
  have hp : 0 < min (delta/64) (1/16:ℝ) := lt_min (by positivity) (by norm_num)
  have Hpow : Tendsto (fun n=>((dim n+1:ℕ):ℝ)^(-min (delta/64) (1/16))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  apply squeeze_zero' _
    (actual_selected_bad_history_radius_strip_thermal_polynomial_bound_along_weak_general
      Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hc dim hdim M hxs G) Hpow
  exact Eventually.of_forall (fun n=>div_nonneg
    ((M n).actual_radius_target_strip_integral_nonneg c C) (pow_pos (M n).hxs 3).le)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

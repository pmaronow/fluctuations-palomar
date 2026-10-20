module

public import ComparisonNativeActualCavityClockContext
public import ComparisonNativeActualRegularStrongInitialMassErrorAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 18000000

theorem actual_cavity_clock_context_full_thermal_density_tendsto_zero_of_working_scale_lower
    {m delta cl cu Az C0 Ct D Bclock T Cs w0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hw0 : 0 < w0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualCavityClockContext M T)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlower : ∀ᶠn in atTop,w0 ≤ (M n).canonicalDirectTestBandScale)
    (hWupper : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1) :
    Tendsto (fun n=>(∫u in (0:ℝ)..1,
      Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2)
      atTop (𝓝 0) := by
  let c:=2*cu*(Az+1)+1
  have hc : 0 < c := by dsimp [c];positivity
  have hcouter : 2*cu*(Az+1) ≤ c := by dsimp [c];linarith
  let Cmax:=1/(2*w0)+1
  have hCmax : 0 < Cmax := by dsimp [Cmax];positivity
  let B0:=actualIntermediateMassEffectiveScale w0 (1/2)
  have hB0 : 0 < B0 := actualIntermediateMassEffectiveScale_pos hw0 (by norm_num)
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  let eps:=fun n=>((dim n+1:ℕ):ℝ)^(-eta/2)
  have heps n : 0 ≤ eps n := by dsimp [eps];positivity
  have Heps : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps,neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (half_pos heta)).comp
        (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hinitial:=regular_minimum_initial_mass_error_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs)
    (fun _=>le_rfl) G.xs_zero G.pullback c hc
  have Hdyad:=hdim.eventually (eventually_actual_regular_strong_intermediate_mass_dyad
    (D:=D) (Cs:=Cs) Cmax Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter)
  have HX:=G.xs_zero.const_mul c |>.eventually
    (eventually_le_nhds (show c*(0:ℝ) < 1/2 by simp))
  let middle:=fun n=>Real.sqrt (Cmax*eps n*nativeIntermediateAccumulationConstant Cmax)
  let terminal:=fun n=>Real.sqrt (eps n/(4*B0^2))
  have Hmiddle : Tendsto middle atTop (𝓝 0) := by
    simpa only [middle,mul_zero,zero_mul,Real.sqrt_zero] using
      ((Heps.const_mul Cmax).mul_const (nativeIntermediateAccumulationConstant Cmax)).sqrt
  have Hterminal : Tendsto terminal atTop (𝓝 0) := by
    simpa only [terminal,zero_div,Real.sqrt_zero] using (Heps.div_const (4*B0^2)).sqrt
  have Hbound : ∀ᶠn in atTop,
      (∫u in (0:ℝ)..1,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2 ≤
      (∫u in 0..c*(M n).xs,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2+
        middle n+terminal n := by
    filter_upwards [Hdyad,hsmall,hWlower,hWupper,HX,G.pullback] with n hnDyad hnSmall hnLo hnUp hnX hnClock
    let W:=(M n).canonicalDirectTestBandScale
    let x:=(M n).xs
    let f:=fun u=>orderedPathB (dim n+1) (M n).bf (M n).hf u-
      (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2
    let C:=1/(2*W)
    have hW : 0 < W := (M n).canonical_direct_test_band_pos
    have hx : 0 < x := (M n).hxs
    have hC : 0 < C := by dsimp [C];positivity
    have hCbound : C ≤ Cmax := by
      have H:=one_div_le_one_div_of_le (by positivity : 0 < 2*w0)
        (mul_le_mul_of_nonneg_left hnLo (by norm_num : (0:ℝ) ≤ 2))
      dsimp only [C,Cmax]
      linarith
    have hhalf : C*W=1/2 := by dsimp [C];field_simp
    have hhalfMax : (1/2:ℝ) ≤ Cmax*W := by
      rw [←hhalf]
      exact mul_le_mul_of_nonneg_right hCbound hW.le
    have hfi : IntervalIntegrable f volume 0 1 := native_comparison_thermal_intervalIntegrable (M n)
    have hf0 u (hu : u∈Icc (0:ℝ) 1) : 0 ≤ f u := (M n).actual_thermal_nonneg_on_unit hu
    have hdyad v (hv : 0 < v) (hv2 : 2*v ≤ 1) (hvc : c*x ≤ v) (hvC : v ≤ C*W) :
        (∫u in v..2*v,f u) ≤ eps n*(x^4*v/(actualIntermediateMassEffectiveScale W v)^2) := by
      have H:=hnDyad (M n) hnClock hnSmall hnUp v hv hv2 hvc
        (hvC.trans (mul_le_mul_of_nonneg_right hCbound hW.le))
      have H' : (∫u in v..2*v,f u)/(x^4*v/(actualIntermediateMassEffectiveScale W v)^2) ≤ eps n := by
        simpa only [x,W,f,eps,eta,NativeOverlapContext.N,neg_div] using H
      exact (div_le_iff₀ (by
        have HB:=actualIntermediateMassEffectiveScale_pos hW hv
        positivity : 0 < x^4*v/(actualIntermediateMassEffectiveScale W v)^2)).mp H'
    have Hfirst:=native_initial_plus_intermediate_error_ratio_le hc hC hx hW (heps n)
      (by dsimp [x];linarith) (by rw [mul_assoc,hhalf];norm_num) hfi hf0 hdyad
    rw [hhalf] at Hfirst
    have Hconstant : C*nativeIntermediateAccumulationConstant C ≤
        Cmax*nativeIntermediateAccumulationConstant Cmax := by
      have Hmax:=max_le_max_left (1:ℝ) hCbound
      have Hcoef : 0 ≤ nativeIntermediateDyadicRatio/(nativeIntermediateDyadicRatio-1) :=
        (div_pos nativeIntermediateDyadicRatio_pos (sub_pos.mpr nativeIntermediateDyadicRatio_one_lt)).le
      have Hacc:=mul_le_mul_of_nonneg_left Hmax Hcoef
      change nativeIntermediateAccumulationConstant C ≤ nativeIntermediateAccumulationConstant Cmax at Hacc
      exact mul_le_mul hCbound Hacc (nativeIntermediateAccumulationConstant_pos C).le hCmax.le
    have HmiddleBound : Real.sqrt (C*eps n*nativeIntermediateAccumulationConstant C) ≤ middle n := by
      apply Real.sqrt_le_sqrt
      have H:=mul_le_mul_of_nonneg_right Hconstant (heps n)
      nlinarith only [H]
    have Htail:=hnDyad (M n) hnClock hnSmall hnUp (1/2) (by norm_num) (by norm_num) hnX hhalfMax
    have HBeff : B0 ≤ actualIntermediateMassEffectiveScale W (1/2) := by
      apply (pow_le_pow_iff_left₀ hB0.le (actualIntermediateMassEffectiveScale_pos hW (by norm_num)).le
        (by norm_num : (3:ℕ) ≠ 0)).mp
      rw [actualIntermediateMassEffectiveScale_cube hw0.le (by norm_num),
        actualIntermediateMassEffectiveScale_cube hW.le (by norm_num)]
      nlinarith [pow_le_pow_left₀ hw0.le hnLo 2]
    have HBsq:=pow_le_pow_left₀ hB0.le HBeff 2
    have HthermalTail : (∫u in (1/2:ℝ)..1,f u) ≤ eps n*(x^4/(2*B0^2)) := by
      have HB:=actualIntermediateMassEffectiveScale_pos hW (by norm_num : (0:ℝ)<1/2)
      have H:=(div_le_iff₀ (by positivity : 0 < x^4*(1/2)/(actualIntermediateMassEffectiveScale W (1/2))^2)).mp Htail
      norm_num only at H
      have H' : (∫u in (1/2:ℝ)..1,f u) ≤
          eps n*(x^4*(1/2)/(actualIntermediateMassEffectiveScale W (1/2))^2) := by
        simpa only [x,W,f,eps,eta,NativeOverlapContext.N,neg_div] using H
      apply H'.trans
      apply mul_le_mul_of_nonneg_left _ (heps n)
      have Hdiv:=div_le_div_of_nonneg_left (by positivity : 0 ≤ x^4*(1/2))
        (sq_pos_of_pos hB0) HBsq
      convert Hdiv using 1; ring
    have HtailInt : IntervalIntegrable f volume (1/2:ℝ) 1 := hfi.mono_set (by
      rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (by norm_num) le_rfl)
    have HCS:=interval_integral_sqrt_sq_le_length (by norm_num : (1/2:ℝ) ≤ 1) HtailInt
      (fun u hu=>hf0 u ⟨(by norm_num : (0:ℝ) ≤ 1/2).trans hu.1,hu.2⟩)
    have Hlast : (∫u in (1/2:ℝ)..1,Real.sqrt (f u))/x^2 ≤ terminal n := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow]
      apply (div_le_iff₀ (pow_pos (pow_pos hx 2) 2)).mpr
      have H:=HCS.trans (mul_le_mul_of_nonneg_left HthermalTail (by norm_num : (0:ℝ) ≤ 1-1/2))
      convert H using 1; field_simp; ring
    have hsi:=native_intervalIntegrable_sqrt_of_intervalIntegrable hfi
    have hi0 : IntervalIntegrable (fun u=>Real.sqrt (f u)) volume 0 (1/2) := hsi.mono_set (by
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl (by norm_num))
    have hi1 : IntervalIntegrable (fun u=>Real.sqrt (f u)) volume (1/2) 1 := hsi.mono_set (by
      rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (by norm_num) le_rfl)
    rw [←intervalIntegral.integral_add_adjacent_intervals hi0 hi1,add_div]
    exact add_le_add (Hfirst.trans (add_le_add le_rfl HmiddleBound)) Hlast
  have Hlimit:=Hinitial.add Hmiddle |>.add Hterminal
  simp only [add_zero] at Hlimit
  simpa only [add_zero] using squeeze_zero'
    (Eventually.of_forall (fun n=>div_nonneg
      (intervalIntegral.integral_nonneg zero_le_one (fun _ _=>Real.sqrt_nonneg _)) (sq_nonneg _)))
    Hbound Hlimit

end OAI.SKFluctuations.LaplaceWindowFormalization

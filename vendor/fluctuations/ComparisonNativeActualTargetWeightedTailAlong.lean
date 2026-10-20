module

public import ComparisonNativeActualShellTargetHighTail
public import ComparisonNativeActualRegularStrongInitialMassErrorAlong

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum

theorem regular_target_weighted_high_l1_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hW1 : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1)
    (u : ℕ → ℝ) (hu : ∀ᶠn in atTop,u n∈Icc (0:ℝ) 1) :
    Tendsto (fun n=>(M n).canonicalDirectTestBandScale*
      (∫s in u n..1,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf s-
        (orderedPathS (dim n+1) (M n).bf (M n).hf s)^2))/(x n)^2)
      atTop (𝓝 0) := by
  let c := 2*cu*(Az+1)+1
  have hc : 0 < c := by dsimp [c]; positivity
  have hcouter : 2*cu*(Az+1) ≤ c := by dsimp [c]; linarith
  have Hinitial := regular_minimum_initial_mass_error_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M x hxs hxlim hclock (2*c) (by positivity)
  let eta := actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hpow : Tendsto (fun n=>((dim n+1:ℕ):ℝ)^(-eta/8)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (by positivity : 0 < eta/8)).comp
        ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)
  have Htotal := Hinitial.add Hpow
  simp only [add_zero] at Htotal
  have Hfinite := hdim.eventually (eventually_actual_regular_target_tail_with_initial_modulus
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter)
  have Hcut := (hxlim.const_mul (2*c)).eventually
    (eventually_le_nhds (show 2*c*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Htotal
  · filter_upwards [hu] with n hnu
    exact div_nonneg (mul_nonneg (M n).canonical_direct_test_band_pos.le
      (intervalIntegral.integral_nonneg hnu.2 (fun _ _=>Real.sqrt_nonneg _))) (sq_nonneg _)
  · filter_upwards [Hfinite,hclock,hsmall,hW1,Hcut,hu] with n hn hcN hsN h1N hcutN huN
    have hx : 0 < x n := (M n).hxs.trans_le (hxs n)
    have hW := (M n).canonical_direct_test_band_pos
    have HI := hn (M n) hcN hsN h1N (x n) (hxs n) hcutN (u n) huN
    let I := ∫s in 0..2*c*x n,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf s-
      (orderedPathS (dim n+1) (M n).bf (M n).hf s)^2)
    let A := (M n).context.N^(-(actualMassSavingExponent m delta/8))
    have hI : 0 ≤ I := intervalIntegral.integral_nonneg (by positivity) (fun _ _=>Real.sqrt_nonneg _)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have Hsquare : (M n).xs^2 ≤ (x n)^2 := by nlinarith [(M n).hxs,hxs n]
    have HIW : (M n).canonicalDirectTestBandScale*I ≤ I :=
      (mul_le_mul_of_nonneg_right h1N hI).trans_eq (one_mul I)
    have Hscale : (M n).canonicalDirectTestBandScale*
        (I+A*((M n).xs^2/(M n).canonicalDirectTestBandScale)) ≤ I+A*(x n)^2 := by
      calc
        _ = (M n).canonicalDirectTestBandScale*I+A*(M n).xs^2 := by
          field_simp
        _ ≤ _ := add_le_add HIW (mul_le_mul_of_nonneg_left Hsquare hA)
    have Hprod := (mul_le_mul_of_nonneg_left HI hW.le).trans Hscale
    have Hnorm := div_le_div_of_nonneg_right Hprod (sq_nonneg (x n))
    have Heq : (I+A*(x n)^2)/(x n)^2=I/(x n)^2+((dim n+1:ℕ):ℝ)^(-eta/8) := by
      dsimp only [A,NativeOverlapContext.N,eta]
      rw [neg_div]
      field_simp
    rw [Heq] at Hnorm
    exact Hnorm

theorem shell_history_target_weighted_high_l1_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T epsilon shell : ℕ → ℝ) (ts : ℕ → List ComparisonHistoryTerm)
    (hb : ∀n u,(M n).b u=historyMatrixClock (T n) (epsilon n) (shell n) (ts n) u)
    (hh : ∀n u,(M n).h u=historyFieldClock (ts n) u)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hW1 : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1)
    (u : ℕ → ℝ) (hu : ∀ᶠn in atTop,u n∈Icc (0:ℝ) 1) :
    Tendsto (fun n=>(M n).canonicalDirectTestBandScale*
      (∫s in u n..1,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf s-
        (orderedPathS (dim n+1) (M n).bf (M n).hf s)^2))/(x n)^2)
      atTop (𝓝 0) := by
  apply regular_target_weighted_high_l1_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M x hxs hxlim _ hsmall hW1 u hu
  exact Eventually.of_forall (fun n=>NativePullbackClockRegularity.of_shell_history
    (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha
    (T n) (epsilon n) (shell n) (ts n) (M n).b (M n).h (hb n) (hh n) le_rfl zero_le_one le_rfl)

theorem regular_target_to_working_band_l1_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n)
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (C : ℝ) (hC : 0 < C) (u v : ℕ → ℝ)
    (huv : ∀ᶠn in atTop,0 ≤ u n ∧ u n ≤ v n ∧ v n ≤ min (C*(M n).canonicalDirectTestBandScale) 1) :
    Tendsto (fun n=>(∫s in u n..v n,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf s-
        (orderedPathS (dim n+1) (M n).bf (M n).hf s)^2))/(x n)^2)
      atTop (𝓝 0) := by
  have Htotal := regular_minimum_strong_initial_mass_error_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M hsmall hWlim hclock C hC
  apply squeeze_zero' _ _ Htotal
  · filter_upwards [huv] with n hn
    exact div_nonneg (intervalIntegral.integral_nonneg hn.2.1 (fun _ _=>Real.sqrt_nonneg _))
      (sq_nonneg _)
  · filter_upwards [huv] with n hn
    have htop : 0 ≤ min (C*(M n).canonicalDirectTestBandScale) 1 :=
      le_min (mul_pos hC (M n).canonical_direct_test_band_pos).le zero_le_one
    have HI := (native_intervalIntegrable_sqrt_of_intervalIntegrable
      (native_comparison_thermal_intervalIntegrable (M n))).mono_set (by
        rw [uIcc_of_le htop,uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl (min_le_right _ _))
    have Hmono := intervalIntegral.integral_mono_interval hn.1 hn.2.1 hn.2.2
      (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) HI
    have hx : 0 < x n := (M n).hxs.trans_le (hxs n)
    have Hsquare : (M n).xs^2 ≤ (x n)^2 := by nlinarith [(M n).hxs,hxs n]
    exact (div_le_div_of_nonneg_right Hmono (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left
        (intervalIntegral.integral_nonneg htop (fun _ _=>Real.sqrt_nonneg _))
        (pow_pos (M n).hxs 2) Hsquare)

theorem shell_history_target_to_working_band_l1_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T epsilon shell : ℕ → ℝ) (ts : ℕ → List ComparisonHistoryTerm)
    (hb : ∀n u,(M n).b u=historyMatrixClock (T n) (epsilon n) (shell n) (ts n) u)
    (hh : ∀n u,(M n).h u=historyFieldClock (ts n) u)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n)
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (C : ℝ) (hC : 0 < C) (u v : ℕ → ℝ)
    (huv : ∀ᶠn in atTop,0 ≤ u n ∧ u n ≤ v n ∧ v n ≤ min (C*(M n).canonicalDirectTestBandScale) 1) :
    Tendsto (fun n=>(∫s in u n..v n,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf s-
        (orderedPathS (dim n+1) (M n).bf (M n).hf s)^2))/(x n)^2)
      atTop (𝓝 0) := by
  apply regular_target_to_working_band_l1_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M x hxs _ hsmall hWlim C hC u v huv
  exact Eventually.of_forall (fun n=>NativePullbackClockRegularity.of_shell_history
    (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha
    (T n) (epsilon n) (shell n) (ts n) (M n).b (M n).h (hb n) (hh n) le_rfl zero_le_one le_rfl)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

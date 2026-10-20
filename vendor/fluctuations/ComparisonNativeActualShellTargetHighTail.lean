module

public import ComparisonNativeActualRegularTargetHighTail
public import ComparisonNativeActualShellHistoryThermalBounds
public import ComparisonNativeActualRegularInitialMassErrorAlong

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_shell_history_target_high_l1_tail
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,M.b u=historyMatrixClock T epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
        ∀u : ℝ, 2*c*M.xs ≤ u → u ≤ 1 →
          (∫s in u..1,Real.sqrt (orderedPathB (n+1) M.bf M.hf s-
            (orderedPathS (n+1) M.bf M.hf s)^2)) ≤
            M.context.N^(-(actualMassSavingExponent m delta/8))*
              (M.xs^2/M.canonicalDirectTestBandScale) := by
  filter_upwards [eventually_actual_regular_target_high_l1_tail (D:=D) Bclock
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter] with n hn
  intro M T epsilon shell ts hb hh
  exact hn M (NativePullbackClockRegularity.of_shell_history
    M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha
    T epsilon shell ts M.b M.h hb hh le_rfl zero_le_one le_rfl)

theorem eventually_actual_shell_history_target_tail_with_initial_modulus
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,M.b u=historyMatrixClock T epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
        ∀x : ℝ, M.xs ≤ x → 2*c*x ≤ 1 → ∀u∈Icc (0:ℝ) 1,
          (∫s in u..1,Real.sqrt (orderedPathB (n+1) M.bf M.hf s-
            (orderedPathS (n+1) M.bf M.hf s)^2)) ≤
          (∫s in 0..2*c*x,Real.sqrt (orderedPathB (n+1) M.bf M.hf s-
            (orderedPathS (n+1) M.bf M.hf s)^2))+
            M.context.N^(-(actualMassSavingExponent m delta/8))*
              (M.xs^2/M.canonicalDirectTestBandScale) := by
  filter_upwards [eventually_actual_regular_target_tail_with_initial_modulus (D:=D) Bclock
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter] with n hn
  intro M T epsilon shell ts hb hh
  exact hn M (NativePullbackClockRegularity.of_shell_history
    M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha
    T epsilon shell ts M.b M.h hb hh le_rfl zero_le_one le_rfl)

namespace NativeOverlapMinimum

theorem regular_target_high_l1_ratio_tendsto_zero_of_working_scale_lower_along
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
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlo : ∀ᶠn in atTop,w0 ≤ (M n).canonicalDirectTestBandScale)
    (u : ℕ → ℝ) (hu : ∀ᶠn in atTop,u n∈Icc (0:ℝ) 1) :
    Tendsto (fun n=>
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
  have Htotal := Hinitial.add (Hpow.div_const w0)
  simp only [zero_div,add_zero] at Htotal
  have Hfinite := hdim.eventually (eventually_actual_regular_target_tail_with_initial_modulus
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter)
  have Hcut := (hxlim.const_mul (2*c)).eventually
    (eventually_le_nhds (show 2*c*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Htotal
  · filter_upwards [hu] with n hnu
    exact div_nonneg (intervalIntegral.integral_nonneg hnu.2 (fun _ _=>Real.sqrt_nonneg _))
      (sq_nonneg _)
  · filter_upwards [Hfinite,hclock,hsmall,hW1,hWlo,Hcut,hu] with n hn hcN hsN h1N hloN hcutN huN
    have hx : 0 < x n := (M n).hxs.trans_le (hxs n)
    have HI := hn (M n) hcN hsN h1N (x n) (hxs n) hcutN (u n) huN
    have Hnorm := div_le_div_of_nonneg_right HI (sq_nonneg (x n))
    rw [add_div] at Hnorm
    have Hsquare : (M n).xs^2 ≤ (x n)^2 := by nlinarith [(M n).hxs,hxs n]
    have Hquot : (M n).xs^2/(M n).canonicalDirectTestBandScale ≤ (x n)^2/w0 :=
      (div_le_div_of_nonneg_right Hsquare (M n).canonical_direct_test_band_pos.le).trans
        (div_le_div_of_nonneg_left (sq_nonneg _) hw0 hloN)
    have Hp : 0 ≤ (M n).context.N^(-(actualMassSavingExponent m delta/8)) := by positivity
    have Hsave := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Hquot Hp) (sq_nonneg (x n))
    have Heq : (M n).context.N^(-(actualMassSavingExponent m delta/8))*
        ((x n)^2/w0)/(x n)^2 = ((dim n+1:ℕ):ℝ)^(-eta/8)/w0 := by
      dsimp only [NativeOverlapContext.N,eta]
      rw [neg_div]
      field_simp
    rw [Heq] at Hsave
    exact Hnorm.trans (add_le_add le_rfl Hsave)

theorem shell_history_target_high_l1_ratio_tendsto_zero_of_working_scale_lower_along
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
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlo : ∀ᶠn in atTop,w0 ≤ (M n).canonicalDirectTestBandScale)
    (u : ℕ → ℝ) (hu : ∀ᶠn in atTop,u n∈Icc (0:ℝ) 1) :
    Tendsto (fun n=>
      (∫s in u n..1,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf s-
        (orderedPathS (dim n+1) (M n).bf (M n).hf s)^2))/(x n)^2)
      atTop (𝓝 0) := by
  apply regular_target_high_l1_ratio_tendsto_zero_of_working_scale_lower_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M x hxs hxlim _
    hsmall hW1 w0 hw0 hWlo u hu
  exact Eventually.of_forall (fun n=>NativePullbackClockRegularity.of_shell_history
    (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha
    (T n) (epsilon n) (shell n) (ts n) (M n).b (M n).h (hb n) (hh n) le_rfl zero_le_one le_rfl)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeActualMinimumCapTravel
public import ComparisonScalarWeightedCapTravel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000

def actualWeightedCapTravelRate (delta : ℝ) (dim : ℕ→ℕ) (n : ℕ) : ℝ :=
  2*Real.log ((dim n+1:ℕ):ℝ)/((dim n+1:ℕ):ℝ)^delta

theorem actual_weighted_cap_travel_rate_nonneg (delta : ℝ) (dim : ℕ→ℕ) (n : ℕ) :
    0 ≤ actualWeightedCapTravelRate delta dim n := by
  have hN : (1:ℝ) ≤ ((dim n+1:ℕ):ℝ):=by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hN))
    (Real.rpow_nonneg (zero_le_one.trans hN) _)

theorem actual_weighted_cap_travel_rate_tendsto_zero_along
    {delta : ℝ} (hdelta : 0 < delta) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    Tendsto (actualWeightedCapTravelRate delta dim) atTop (𝓝 0) :=
  comparison_weighted_cap_log_rate_tendsto _ hdelta
    ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_error_parameter_le_one_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∀ᶠn in atTop,(M n).context.E ≤ 1 := by
  have HN : Tendsto (fun n=>(M n).context.N) atTop atTop:=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim
  have Hsqrt:=Real.tendsto_sqrt_atTop.comp HN
  filter_upwards [Hsqrt.eventually (eventually_ge_atTop (D^2))] with n hn
  have hd2 : (M n).context.d^2 ≤ D^2:=pow_le_pow_left₀ (M n).context.hd.le (M n).hdD 2
  have hsqrt : 0 < Real.sqrt (M n).context.N:=Real.sqrt_pos.mpr (M n).context.hN
  apply (mul_le_mul_iff_right₀ hsqrt).mp
  simpa only [mul_one,Function.comp_def,NativeOverlapContext.N] using
    (M n).hupper.trans (hd2.trans hn)

theorem eventually_actual_cap_log_loss_le_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∀ᶠn in atTop,Real.log ((1+(M n).context.U)/(M n).context.U)/(M n).context.N^delta ≤
      actualWeightedCapTravelRate delta dim n := by
  have HN : Tendsto (fun n=>(M n).context.N) atTop atTop:=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim
  filter_upwards [eventually_actual_error_parameter_le_one_along dim hdim M,
    HN.eventually (eventually_ge_atTop 2)] with n hE1 hN2
  have H:=comparison_native_cap_log_le hN2 (M n).context.hE hE1
  exact div_le_div_of_nonneg_right H (Real.rpow_nonneg (M n).context.hN.le _)

theorem eventually_actual_weighted_cap_travel_normalized_le_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∀ᶠn in atTop,∀r : ℝ,
      laplaceComparisonStrength (M n).context.d (M n).lam r*(M n).cavityCapTravel/(M n).xs^3 ≤
        actualWeightedCapTravelRate delta dim n := by
  filter_upwards [eventually_actual_cap_log_loss_le_along dim hdim M] with n hn
  intro r
  exact (comparison_scalar_native_cap_calibration (M n).context.hN (M n).context.hE
    (M n).context.hd (M n).hlam.le (M n).hld (M n).hxs (M n).hscale r).trans hn

theorem actual_weighted_cap_travel_saving_along
    (hdelta : 0 < delta) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀r : ℝ,
        laplaceComparisonStrength (M n).context.d (M n).lam r*(M n).cavityCapTravel/(M n).xs^3 ≤ eta n :=
  ⟨actualWeightedCapTravelRate delta dim,actual_weighted_cap_travel_rate_nonneg delta dim,
    actual_weighted_cap_travel_rate_tendsto_zero_along hdelta dim hdim,
    eventually_actual_weighted_cap_travel_normalized_le_along dim hdim M⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

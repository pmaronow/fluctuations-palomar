module

public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQAllCapMismatch
public import SKProof.Port.ComparisonActualOriginalQContactGeometry
public import ComparisonNativeActualInitialMassChargesAlong
public import ComparisonNativeActualWeightedCapTravelAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_mass_small_ratio
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0<C0) :
    a.data.U/a.xs ≤ C0^3*a.data.N^(-3*m) := by
  have hupper : a.data.E ≤ a.data.d^2/Real.sqrt a.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.data.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have hlower : (1/C0)*a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ a.data.E := by
    have H : (a.data.N^(-(2:ℝ)/3+m)*a.data.d)/C0 ≤ a.data.E:=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have H:=comparison_radius_small_mass_ratio a.data.hN (one_div_pos.mpr hC0)
    a.data.hd hlower hupper a.hscale
  simpa only [one_div_div,one_pow,div_pow,div_one,ActualHighWallData.U,ActualHighWallData.N] using H

theorem actual_cap_travel_ratio_tendsto_zero_along
    (hC0 : 0<C0) (hroom : 0<3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) :
    Tendsto (fun n=>(M n).cavityCapTravel/W n) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [] with n
    exact hb.trans_le (div_nonneg (M n).cavityCapTravel_nonneg
      ((M n).hxs.trans_le (hxs n)).le)
  · intro e he
    filter_upwards [((tendsto_add_atTop_nat 1).comp hdim).eventually (eventually_actual_cap_travel_small_original_q (D:=D)
      (epsilon:=e/2) hC0 hroom (half_pos he))] with n hn
    have hw:=(M n).hxs.trans_le (hxs n)
    have H:=((hn (M n)).1).trans (mul_le_mul_of_nonneg_left (hxs n) (half_pos he).le)
    exact ((div_le_iff₀ hw).mpr H).trans_lt (by linarith)

theorem actual_floor_mass_ratio_tendsto_zero_along
    (hC0 : 0<C0) (hroom : 0<3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) :
    Tendsto (fun n=>((M n).data.N^(-delta)*(M n).data.U)/W n) atTop (𝓝 0) := by
  have Hpow : Tendsto (fun n : ℕ=>((dim n+1:ℕ):ℝ)^(-(3*m+delta))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hroom).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)
  have Hlim:=Hpow.const_mul (C0^3)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n=>by
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg (M n).data.hN.le _)
      (M n).data.hU.le) hw.le) _ Hlim
  intro n
  have HU:=((div_le_div_of_nonneg_left (M n).data.hU.le (M n).hxs (hxs n)).trans
    ((M n).canonical_mass_small_ratio hC0))
  have H:=mul_le_mul_of_nonneg_left HU
    (Real.rpow_nonneg (M n).data.hN.le (-delta))
  rw [←mul_assoc,mul_comm ((M n).data.N^(-delta)) (C0^3),mul_assoc,
    ←Real.rpow_add (M n).data.hN] at H
  have he : -delta+-3*m=-(3*m+delta) := by ring
  rw [he] at H
  simpa only [mul_div_assoc,ActualHighWallData.N] using H

theorem eventually_actual_error_parameter_le_one_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∀ᶠn in atTop,(M n).data.E ≤ 1 := by
  have HN : Tendsto (fun n=>(M n).data.N) atTop atTop:=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim
  have Hsqrt:=Real.tendsto_sqrt_atTop.comp HN
  filter_upwards [Hsqrt.eventually (eventually_ge_atTop (D^2))] with n hn
  have hd2 : (M n).data.d^2 ≤ D^2:=pow_le_pow_left₀ (M n).data.hd.le (M n).hdD 2
  have hsqrt : 0 < Real.sqrt (M n).data.N:=Real.sqrt_pos.mpr (M n).data.hN
  apply (mul_le_mul_iff_right₀ hsqrt).mp
  simpa only [mul_one,Function.comp_def,ActualHighWallData.N] using
    (M n).hupper.trans (hd2.trans hn)

theorem eventually_actual_cap_log_loss_le_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    ∀ᶠn in atTop,Real.log ((1+(M n).data.U)/(M n).data.U)/(M n).data.N^delta ≤
      actualWeightedCapTravelRate delta dim n := by
  have HN : Tendsto (fun n=>(M n).data.N) atTop atTop:=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim
  filter_upwards [eventually_actual_error_parameter_le_one_along dim hdim M,
    HN.eventually (eventually_ge_atTop 2)] with n hE1 hN2
  have H:=comparison_native_cap_log_le hN2 (M n).data.hE hE1
  exact div_le_div_of_nonneg_right H (Real.rpow_nonneg (M n).data.hN.le _)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeActualInitialMassMismatch

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 7000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_cap_travel_ratio_tendsto_zero_along
    (hC0 : 0<C0) (hroom : 0<3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) :
    Tendsto (fun n=>(M n).cavityCapTravel/W n) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [] with n
    exact hb.trans_le (div_nonneg (M n).cavityCapTravel_nonneg
      ((M n).hxs.trans_le (hxs n)).le)
  · intro e he
    filter_upwards [hdim.eventually (eventually_actual_minimum_cap_travel_small (D:=D)
      (epsilon:=e/2) hC0 hroom (half_pos he))] with n hn
    have hw:=(M n).hxs.trans_le (hxs n)
    have H:=((hn (M n)).1).trans (mul_le_mul_of_nonneg_left (hxs n) (half_pos he).le)
    exact ((div_le_iff₀ hw).mpr H).trans_lt (by linarith)

theorem actual_floor_mass_ratio_tendsto_zero_along
    (hC0 : 0<C0) (hroom : 0<3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) :
    Tendsto (fun n=>((M n).context.N^(-delta)*(M n).context.U)/W n) atTop (𝓝 0) := by
  have Hpow : Tendsto (fun n : ℕ=>((dim n+1:ℕ):ℝ)^(-(3*m+delta))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hroom).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)
  have Hlim:=Hpow.const_mul (C0^3)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n=>by
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg (M n).context.hN.le _)
      (M n).context.hU.le) hw.le) _ Hlim
  intro n
  have HU:=((div_le_div_of_nonneg_left (M n).context.hU.le (M n).hxs (hxs n)).trans
    ((M n).canonical_mass_small_ratio hC0))
  have H:=mul_le_mul_of_nonneg_left HU
    (Real.rpow_nonneg (M n).context.hN.le (-delta))
  rw [←mul_assoc,mul_comm ((M n).context.N^(-delta)) (C0^3),mul_assoc,
    ←Real.rpow_add (M n).context.hN] at H
  have he : -delta+-3*m=-(3*m+delta) := by ring
  rw [he] at H
  simpa only [mul_div_assoc,NativeOverlapContext.N] using H

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

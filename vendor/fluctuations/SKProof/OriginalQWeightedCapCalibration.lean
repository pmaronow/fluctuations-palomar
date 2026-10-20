module

public import ComparisonActualHighWallThetaZeroCapTravelCore
public import ComparisonScalarWeightedCapTravel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ}

theorem rmin_le_native_cap_length_original_q (a : ActualHighWallData n delta) :
    a.rmin ≤ comparisonConstraintLength a.N a.E a.d/(2*a.N^delta) := by
  let U := comparisonSmallMass a.N a.E
  let L := comparisonConstraintLength a.N a.E a.d
  have hrecip : 1/a.M a.s ≤ (L/a.N^delta)*(1/(a.s+U)) :=
    (comparisonCap_first_term (δ := delta) a.hN a.hU a.hL a.hE a.hd.le a.hs.1.le).2
  have hfrac : U/(a.s+U) ≤ 1 :=
    (div_le_one (add_pos_of_nonneg_of_pos a.hs.1.le a.hU)).mpr
      (le_add_of_nonneg_left a.hs.1.le)
  have hLscale : 0 ≤ L/(2*a.N^delta) := by
    exact div_nonneg a.hL.le (by positivity)
  calc
    a.rmin = (U/2)*(1/a.M a.s) := by
      change U/(2*a.M a.s) = _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (U/2)*((L/a.N^delta)*(1/(a.s+U))) :=
      mul_le_mul_of_nonneg_left hrecip (div_nonneg a.hU.le (by norm_num))
    _ = (L/(2*a.N^delta))*(U/(a.s+U)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ L/(2*a.N^delta) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac hLscale

end ActualHighWallData

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem lambda_original_radius_cubic_calibration_original_q :
    Q.lam*Q.data.rmin/Q.xs^3 ≤ 1/(2*Q.data.N^delta) := by
  let L := comparisonConstraintLength Q.data.N Q.data.E Q.data.d
  let a := comparisonLowerScale Q.data.N Q.data.E Q.data.d
  have ha : 0 ≤ a := (comparisonLowerScale_pos Q.data.hN Q.data.hE Q.data.hd).le
  have hbudget : Q.lam*L ≤ Q.xs^3 := by
    calc
      Q.lam*L ≤ Q.data.d^2*L := mul_le_mul_of_nonneg_right Q.hld Q.data.hL.le
      _ = L*Q.data.d^2 := mul_comm _ _
      _ ≤ a^3 := comparison_native_constraint_cubic_room Q.data.hd
      _ ≤ Q.xs^3 := pow_le_pow_left₀ ha Q.hscale 3
  have hratio : Q.lam*L/Q.xs^3 ≤ 1 :=
    (div_le_one (pow_pos Q.hxs 3)).mpr hbudget
  calc
    Q.lam*Q.data.rmin/Q.xs^3 ≤ Q.lam*(L/(2*Q.data.N^delta))/Q.xs^3 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left Q.data.rmin_le_native_cap_length_original_q Q.hlam.le)
        (pow_nonneg Q.hxs.le 3)
    _ = (Q.lam*L/Q.xs^3)/(2*Q.data.N^delta) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ 1/(2*Q.data.N^delta) :=
      div_le_div_of_nonneg_right hratio (by positivity)

theorem lambda_original_cap_travel_cubic_calibration_original_q :
    Q.lam*Q.cavityCapTravel/Q.xs^3 ≤
      Real.log ((1+comparisonSmallMass Q.data.N Q.data.E)/
        comparisonSmallMass Q.data.N Q.data.E)/Q.data.N^delta := by
  simpa only [cavityCapTravel] using
    comparison_weighted_cap_travel_calibration
      (delta := delta) (e := Q.lam) (d := Q.data.d)
      Q.data.hN Q.data.hU Q.data.hL.le
      (comparisonLowerScale_pos Q.data.hN Q.data.hE Q.data.hd).le
      Q.hxs Q.hscale Q.hld (comparison_native_constraint_cubic_room Q.data.hd)

theorem lambda_original_cap_and_origin_cubic_calibration_original_q :
    Q.lam*(Q.data.rmin+Q.cavityCapTravel)/Q.xs^3 ≤
      (Real.log ((1+comparisonSmallMass Q.data.N Q.data.E)/
        comparisonSmallMass Q.data.N Q.data.E)+(1/2:ℝ))/Q.data.N^delta := by
  calc
    Q.lam*(Q.data.rmin+Q.cavityCapTravel)/Q.xs^3 =
        Q.lam*Q.cavityCapTravel/Q.xs^3+Q.lam*Q.data.rmin/Q.xs^3 := by ring
    _ ≤ Real.log ((1+comparisonSmallMass Q.data.N Q.data.E)/
          comparisonSmallMass Q.data.N Q.data.E)/Q.data.N^delta+
          1/(2*Q.data.N^delta) :=
      add_le_add Q.lambda_original_cap_travel_cubic_calibration_original_q
        Q.lambda_original_radius_cubic_calibration_original_q
    _ = (Real.log ((1+comparisonSmallMass Q.data.N Q.data.E)/
          comparisonSmallMass Q.data.N Q.data.E)+(1/2:ℝ))/Q.data.N^delta := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem original_energy_times_size_le_sqrt_original_q :
    Q.data.N*Q.data.E ≤ Real.sqrt Q.data.N := by
  have hdSq : Q.data.d^2 ≤ 1 :=
    pow_le_one₀ Q.data.hd.le Q.data.hd1
  have HE : Real.sqrt Q.data.N*Q.data.E ≤ 1 := Q.hupper.trans hdSq
  calc
    Q.data.N*Q.data.E = (Real.sqrt Q.data.N)^2*Q.data.E := by
      rw [Real.sq_sqrt Q.data.hN.le]
    _ = Real.sqrt Q.data.N*(Real.sqrt Q.data.N*Q.data.E) := by ring
    _ ≤ Real.sqrt Q.data.N*1 :=
      mul_le_mul_of_nonneg_left HE (Real.sqrt_nonneg _)
    _ = Real.sqrt Q.data.N := mul_one _

theorem original_native_cap_log_le_original_q (hN : 2 ≤ Q.data.N) :
    Real.log ((1+comparisonSmallMass Q.data.N Q.data.E)/
      comparisonSmallMass Q.data.N Q.data.E) ≤ 2*Real.log Q.data.N := by
  have hNsq : Q.data.N ≤ Q.data.N^2 := by nlinarith only [hN]
  have hsqrt : Real.sqrt Q.data.N ≤ Q.data.N := by
    simpa only [Real.sqrt_sq Q.data.hN.le] using Real.sqrt_le_sqrt hNsq
  have hNE : Q.data.N*Q.data.E ≤ Q.data.N :=
    Q.original_energy_times_size_le_sqrt_original_q.trans hsqrt
  have heq : (1+comparisonSmallMass Q.data.N Q.data.E)/
      comparisonSmallMass Q.data.N Q.data.E = 1+Q.data.N*Q.data.E := by
    unfold comparisonSmallMass
    field_simp [Q.data.hN.ne',Q.data.hE.ne']
    ring
  have hpos : 0 < 1+Q.data.N*Q.data.E :=
    add_pos zero_lt_one (mul_pos Q.data.hN Q.data.hE)
  have hle : 1+Q.data.N*Q.data.E ≤ Q.data.N^2 := by
    nlinarith only [hNE,hN]
  rw [heq]
  calc
    Real.log (1+Q.data.N*Q.data.E) ≤ Real.log (Q.data.N^2) :=
      Real.log_le_log hpos hle
    _ = 2*Real.log Q.data.N := by rw [Real.log_pow]; norm_num

end ActualThetaZeroOverlapMinimum

theorem actual_theta_zero_weighted_cap_and_origin_tendsto_zero_along_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hdelta : 0 < delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum
      (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    Tendsto (fun n =>
      (Q n).lam*((Q n).data.rmin+(Q n).cavityCapTravel)/(Q n).xs^3)
      atTop (𝓝 0) := by
  let Ns : ℕ → ℝ := fun n => ((dim n+1:ℕ):ℝ)
  have hNs : Tendsto Ns atTop atTop := by
    simpa only [Ns,Function.comp_def] using
      tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have hlog : Tendsto (fun n => 2*Real.log (Ns n)/(Ns n)^delta)
      atTop (𝓝 0) := comparison_weighted_cap_log_rate_tendsto Ns hdelta hNs
  have hpower : Tendsto (fun n => (1/2:ℝ)*(Ns n)^(-delta))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (((tendsto_rpow_neg_atTop hdelta).comp hNs).const_mul (1/2:ℝ))
  have hupper : Tendsto
      (fun n => 2*Real.log (Ns n)/(Ns n)^delta+(1/2:ℝ)*(Ns n)^(-delta))
      atTop (𝓝 0) := by
    simpa only [zero_add] using hlog.add hpower
  have htravel (n : ℕ) : 0 ≤ (Q n).cavityCapTravel := by
    dsimp only [ActualThetaZeroOverlapMinimum.cavityCapTravel]
    exact mul_nonneg
      (div_nonneg (Q n).data.hL.le (Real.rpow_nonneg (Q n).data.hN.le delta))
      (Real.log_nonneg ((le_div_iff₀ (Q n).data.hU).mpr (by linarith)))
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    div_nonneg (mul_nonneg (Q n).hlam.le
      (add_nonneg (Q n).data.hrbounds.1.le (htravel n)))
      (pow_nonneg (Q n).hxs.le 3))) ?_ hupper
  filter_upwards [hNs.eventually (eventually_ge_atTop (2:ℝ))] with n hn
  calc
    (Q n).lam*((Q n).data.rmin+(Q n).cavityCapTravel)/(Q n).xs^3 ≤
        (Real.log ((1+comparisonSmallMass (Q n).data.N (Q n).data.E)/
          comparisonSmallMass (Q n).data.N (Q n).data.E)+(1/2:ℝ))/(Ns n)^delta :=
      (Q n).lambda_original_cap_and_origin_cubic_calibration_original_q
    _ ≤ (2*Real.log (Ns n)+(1/2:ℝ))/(Ns n)^delta :=
      div_le_div_of_nonneg_right
        (add_le_add ((Q n).original_native_cap_log_le_original_q hn) le_rfl)
        (Real.rpow_nonneg (Q n).data.hN.le delta)
    _ = 2*Real.log (Ns n)/(Ns n)^delta+(1/2:ℝ)*(Ns n)^(-delta) := by
      rw [add_div,Real.rpow_neg (show 0 ≤ Ns n from (Q n).data.hN.le)]
      ring

end OAI.SKFluctuations.LaplaceWindowFormalization

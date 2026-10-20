module

public import ComparisonNativeBroadPhysicalError
public import ComparisonNativeLogarithmicLoss

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 8000000

def nativeBroadTracePolynomial (A K R S : ℝ) : ℝ :=
  5184*A*K*R*S+(66+64*S+65536*(1+S)^2)*216*A*K*R^2

theorem native_broad_trace_coefficient_log_bound
    {N A A0 K R L S : ℝ} (hlog : 1 ≤ Real.log N)
    (hA : 0 ≤ A) (hA0 : 0 ≤ A0) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (hAA : A ≤ A0*Real.log N)
    (hLS : L ≤ S*Real.log N) :
    nativeBroadPhysicalTraceCoefficient N A K R L ≤
      nativeBroadTracePolynomial A0 K R S*(Real.log N)^5 := by
  let x := Real.log N
  have hx : 1 ≤ x := hlog
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hx2 : 1 ≤ x^2 := by nlinarith
  have hx12 : x ≤ x^2 := by nlinarith
  have hx45 : x^4 ≤ x^5 := by nlinarith [mul_nonneg (pow_nonneg hx0 4) (sub_nonneg.mpr hx)]
  have hbracket : 66+64*L+65536*(1+L)^2 ≤ (66+64*S+65536*(1+S)^2)*x^2 := by
    have hlin : L ≤ S*x^2 := hLS.trans (mul_le_mul_of_nonneg_left hx12 hS)
    have hone : 1+L ≤ (1+S)*x := by nlinarith
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+L) hone 2
    nlinarith
  have hfirst : 5184*A*K*R*x^2*L ≤ (5184*A0*K*R*S)*x^5 := by
    have ht : 5184*A*K*R*x^2*L ≤ 5184*(A0*x)*K*R*x^2*(S*x) := by gcongr
    have hp := mul_le_mul_of_nonneg_left hx45 (show 0 ≤ 5184*A0*K*R*S by positivity)
    nlinarith
  have hsecond : (66+64*L+65536*(1+L)^2)*216*A*K*R^2*x^2 ≤
      ((66+64*S+65536*(1+S)^2)*216*A0*K*R^2)*x^5 := by
    have ht : (66+64*L+65536*(1+L)^2)*216*A*K*R^2*x^2 ≤
        ((66+64*S+65536*(1+S)^2)*x^2)*216*(A0*x)*K*R^2*x^2 := by gcongr
    nlinarith
  unfold nativeBroadPhysicalTraceCoefficient nativeBroadTracePolynomial
  exact by change _ ≤ _ at hfirst hsecond; dsimp [x] at *; nlinarith

theorem native_broad_trace_coefficient_eventually
    {delta Ko K R S : ℝ} (hdelta : 0 < delta) (_hKo : 0 ≤ Ko)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    ∀ᶠN : ℝ in atTop, ∀U Ko' L k : ℝ,
      0 < U → U ≤ 1 → 1/N ≤ U → 0 ≤ Ko' → Ko' ≤ Ko →
      0 ≤ L → L ≤ S*Real.log N → 0 ≤ k → k ≤ K*N^delta →
      3*nativeBroadPhysicalTraceCoefficient N
        (Ko'^2+1+50*Real.log ((1+U)/U)) k R L ≤ N^(2*delta) := by
  let A0 := Ko^2+101
  let C := nativeBroadTracePolynomial A0 K R S
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hC : 0 ≤ C := by dsimp [C,nativeBroadTracePolynomial]; positivity
  have hp := comparison_log_loss_eventually (C:=3*C) (p:=5) (by positivity) hdelta
  filter_upwards [hp,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with N hcoef hN hlog
  intro U Ko' L k hU hU1 hUlo hKo' hKoBound hL hLS hk hkBound
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hx : 0 < Real.log N := zero_lt_one.trans_le hlog
  have hsmallLog := comparison_capLogFactor_le (delta:=0) hN hlog hU hU1 hUlo
  simp only [Real.rpow_zero,div_one] at hsmallLog
  have hlogU : Real.log ((1+U)/U) ≤ 2*Real.log N := by nlinarith
  have hlogU0 : 0 ≤ Real.log ((1+U)/U) :=
    (Real.log_pos ((lt_div_iff₀ hU).mpr (by linarith))).le
  have hKK := pow_le_pow_left₀ hKo' hKoBound 2
  have hAA : Ko'^2+1+50*Real.log ((1+U)/U) ≤ A0*Real.log N := by
    have hh := mul_le_mul_of_nonneg_right hlog (show 0 ≤ Ko^2+1 by positivity)
    dsimp [A0]
    nlinarith
  have hA : 0 ≤ Ko'^2+1+50*Real.log ((1+U)/U) := by positivity
  have hb := native_broad_trace_coefficient_log_bound hlog hA hA0 hK hR hL hS hAA hLS
  have hmono : nativeBroadPhysicalTraceCoefficient N (Ko'^2+1+50*Real.log ((1+U)/U)) k R L ≤
      nativeBroadPhysicalTraceCoefficient N (Ko'^2+1+50*Real.log ((1+U)/U)) (K*N^delta) R L := by
    unfold nativeBroadPhysicalTraceCoefficient
    gcongr
  have he : nativeBroadPhysicalTraceCoefficient N (Ko'^2+1+50*Real.log ((1+U)/U)) (K*N^delta) R L =
      N^delta*nativeBroadPhysicalTraceCoefficient N (Ko'^2+1+50*Real.log ((1+U)/U)) K R L := by
    unfold nativeBroadPhysicalTraceCoefficient
    ring
  rw [he] at hmono
  have hh := mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hNp delta).le
  have hfinal := mul_le_mul_of_nonneg_left hcoef (Real.rpow_pos_of_pos hNp delta).le
  simp only [Real.rpow_ofNat] at hfinal
  have hpow : N^delta*N^delta=N^(2*delta) := by rw [←Real.rpow_add hNp]; congr 1; ring
  rw [hpow] at hfinal
  change _ ≤ C*(Real.log N)^5 at hb
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeInnerError
public import ComparisonConditionalOptimizedSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7200000

def nativeBinScalePolynomial (A B S R : ℝ) : ℝ :=
  185+128*S+48*A*S*R+(66+64*S+65536*(1+S)^2)*B*R^2

theorem nativeBinScalePolynomial_nonneg {A B S R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S) (hR : 0 ≤ R) :
    0 ≤ nativeBinScalePolynomial A B S R := by
  unfold nativeBinScalePolynomial
  positivity

theorem nativeBinScaleLoss_le_log_polynomial {x L AS AC v rho A B S R : ℝ}
    (hx : 1 ≤ x) (hL : 0 ≤ L) (hAS : 0 ≤ AS) (hAC : 0 ≤ AC)
    (hv : 0 ≤ v) (hrho : 0 < rho)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hside : L ≤ S*x) (hsidevar : AS ≤ A*x^2) (hcov : AC ≤ B*x^2)
    (hratio : v/rho ≤ R) :
    nativeBinScaleLoss L AS AC v rho ≤ nativeBinScalePolynomial A B S R*x^4 := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hx2 : 1 ≤ x^2 := by nlinarith
  have hx12 : x ≤ x^2 := by nlinarith
  have hx24 : x^2 ≤ x^4 := by nlinarith [sq_nonneg (x^2-1)]
  have hx14 : x ≤ x^4 := hx12.trans hx24
  have hx34 : x^3 ≤ x^4 := by nlinarith [mul_nonneg (show 0 ≤ x^2 by positivity) (sub_nonneg.mpr hx12)]
  have hr0 : 0 ≤ v/rho := div_nonneg hv hrho.le
  have hside4 : 128*L ≤ (128*S)*x^4 := by
    have hh := mul_le_mul_of_nonneg_left hx14 hS
    nlinarith
  have hconst : (185:ℝ) ≤ 185*x^4 := by nlinarith [hx2.trans hx24]
  have hsideprod : 48*AS*L*(v/rho) ≤ (48*A*S*R)*x^4 := by
    have hh : 48*AS*L*(v/rho) ≤ 48*(A*x^2)*(S*x)*R := by gcongr
    have hp := mul_le_mul_of_nonneg_left hx34 (show 0 ≤ 48*A*S*R by positivity)
    nlinarith
  have hbracket : 66+64*L+65536*(1+L)^2 ≤ (66+64*S+65536*(1+S)^2)*x^2 := by
    have hlin : L ≤ S*x^2 := hside.trans (mul_le_mul_of_nonneg_left hx12 hS)
    have hone : 1+L ≤ (1+S)*x := by nlinarith
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+L) hone 2
    nlinarith
  have hcovprod : (66+64*L+65536*(1+L)^2)*AC*(v/rho)^2 ≤
      ((66+64*S+65536*(1+S)^2)*B*R^2)*x^4 := by
    have hh : (66+64*L+65536*(1+L)^2)*AC*(v/rho)^2 ≤
        ((66+64*S+65536*(1+S)^2)*x^2)*(B*x^2)*R^2 := by gcongr
    nlinarith
  unfold nativeBinScaleLoss nativeBinScalePolynomial
  nlinarith

theorem nativeBinScaleLoss_eventually {Ko S R eps : ℝ}
    (hKo : 0 ≤ Ko) (hS : 0 ≤ S) (hR : 0 ≤ R) (heps : 0 < eps) :
    ∀ᶠ N : ℝ in atTop, ∀ m : NativeBandModel, m.N=N → m.Ko ≤ Ko →
      m.Lside ≤ S*Real.log N → m.bandMass/m.rho ≤ R →
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho ≤ N^eps := by
  have hp := comparison_log_loss_eventually (p:=4)
    (nativeBinScalePolynomial_nonneg (A:=108*Ko^2) (B:=54*Ko^2)
      (by positivity) (by positivity) hS hR) heps
  filter_upwards [hp] with N hN
  intro m hNeq hKo' hside hratio
  have hK := pow_le_pow_left₀ (zero_le_one.trans m.hKo) hKo' 2
  have hAS : m.AS ≤ (108*Ko^2)*(Real.log N)^2 := by
    unfold NativeBandModel.AS
    rw [hNeq]
    gcongr
  have hAC : m.AC ≤ (54*Ko^2)*(Real.log N)^2 := by
    unfold NativeBandModel.AC
    rw [hNeq]
    gcongr
  have hb := nativeBinScaleLoss_le_log_polynomial (hNeq ▸ m.hlog) m.hLside
    m.AS_nonneg m.AC_nonneg m.hbandMass.le m.rho_pos (by positivity) (by positivity)
    hS hR hside hAS hAC hratio
  exact hb.trans (by simpa only [Real.rpow_natCast,Real.rpow_ofNat] using hN)

theorem comparison_capLogFactor_le {N delta U : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hU : 0 < U)
    (hU1 : U ≤ 1) (hlower : 1/N ≤ U) :
    9*Real.log N*Real.log ((1+U)/U)/N^delta ≤ 18*(Real.log N)^2/N^delta := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hinv : 1/U ≤ N := by
    have hh := (div_le_iff₀ hNp).mp hlower
    exact (div_le_iff₀ hU).mpr (by nlinarith)
  have harg : (1+U)/U ≤ 2*N := by
    have hid : (1+U)/U=1/U+1 := by field_simp
    rw [hid]
    linarith
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh
    exact hh
  have hlg := Real.log_le_log (div_pos (by linarith) hU) harg
  rw [Real.log_mul (by norm_num) hNp.ne'] at hlg
  have hbound : Real.log ((1+U)/U) ≤ 2*Real.log N := by linarith
  have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 9*Real.log N by linarith)
  exact div_le_div_of_nonneg_right (by nlinarith) (Real.rpow_pos_of_pos hNp delta).le

theorem comparison_capLogFactor_eventually {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ N : ℝ in atTop, ∀ U : ℝ, 0 < U → U ≤ 1 → 1/N ≤ U →
      9*Real.log N*Real.log ((1+U)/U)/N^delta ≤ 1 := by
  have hp := comparison_log_loss_eventually (C:=18) (p:=2) (by norm_num) hdelta
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [hp,hlog,eventually_ge_atTop (1:ℝ)] with N hpow hl hN
  intro U hU hU1 hlow
  have hb := comparison_capLogFactor_le (delta:=delta) hN hl hU hU1 hlow
  exact hb.trans ((div_le_one (Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _)).mpr
    (by simpa only [Real.rpow_natCast,Real.rpow_ofNat] using hpow))

end OAI.SKFluctuations.LaplaceWindowFormalization

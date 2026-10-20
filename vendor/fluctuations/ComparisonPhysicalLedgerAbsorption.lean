module

public import ComparisonNativeLogarithmicLoss
public import ComparisonOuterPhysicalLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7200000

def comparisonInnerFixedCoefficient (Q C : ℝ) : ℝ :=
  2*(Q^2*C)^((2:ℝ)/3)+3+C+(2*Q)^4*C^2

theorem comparison_inner_core_power_bound {N delta E Q C J eps : ℝ}
    (hN : 1 ≤ N) (hdelta : 0 ≤ delta) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hJ1 : J ≤ 1) (heps : eps ≤ delta) :
    comparisonInnerPhysicalCore N delta E Q C J eps ≤
      comparisonInnerFixedCoefficient Q C*N^(3*delta)*E := by
  have hp1 := Real.rpow_le_rpow_of_exponent_le hN (show 4*delta/3 ≤ 3*delta by linarith)
  have hp2 := Real.rpow_le_rpow_of_exponent_le hN (show delta ≤ 3*delta by linarith)
  have hp3 := Real.rpow_le_rpow_of_exponent_le hN (show 2*delta ≤ 3*delta by linarith)
  have hp4 := Real.rpow_le_rpow_of_exponent_le hN (show 2*delta+eps ≤ 3*delta by linarith)
  have h1 : 2*(Q^2*C)^((2:ℝ)/3)*N^(4*delta/3)*E ≤
      2*(Q^2*C)^((2:ℝ)/3)*N^(3*delta)*E := by gcongr
  have h2 : 3*N^delta*E ≤ 3*N^(3*delta)*E := by gcongr
  have h3 : J^2*C*N^(2*delta)*E ≤ C*N^(3*delta)*E := by
    have hJ2 : J^2 ≤ 1 := by nlinarith
    have hh : J^2*C*N^(2*delta)*E ≤ 1*C*N^(3*delta)*E := by gcongr
    simpa using hh
  have h4 : (2*Q)^4*J*C^2*N^(2*delta+eps)*E ≤ (2*Q)^4*C^2*N^(3*delta)*E := by
    have hh : (2*Q)^4*J*C^2*N^(2*delta+eps)*E ≤ (2*Q)^4*1*C^2*N^(3*delta)*E := by gcongr
    simpa using hh
  unfold comparisonInnerPhysicalCore comparisonInnerFixedCoefficient
  nlinarith

theorem comparison_inner_error_core_eventually {delta Q C : ℝ}
    (hdelta : 0 < delta) (hC : 0 ≤ C) :
    ∀ᶠ N : ℝ in atTop, ∀ E F J eps : ℝ, 0 ≤ E → 0 ≤ F → F ≤ N^delta →
      0 ≤ J → J ≤ 1 → eps ≤ delta →
      3*F*comparisonInnerPhysicalCore N delta E Q C J eps+16*J^2*C*N^(2*delta)*E ≤ N^(5*delta)*E := by
  let c := comparisonInnerFixedCoefficient Q C
  have hc : 0 ≤ c := by dsimp [c,comparisonInnerFixedCoefficient];positivity
  have ht := comparison_log_loss_eventually (C:=3*c+16*C) (p:=0) (by positivity) hdelta
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with N hcoef hN
  intro E F J eps hE hF hFN hJ hJ1 heps
  simp only [Real.rpow_zero,mul_one] at hcoef
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hi := comparison_inner_core_power_bound (Q:=Q) hN hdelta.le hE hC hJ hJ1 heps
  have h0core : 0 ≤ comparisonInnerPhysicalCore N delta E Q C J eps := by
    unfold comparisonInnerPhysicalCore
    positivity
  have h1 := mul_le_mul (mul_le_mul_of_nonneg_left hFN (by norm_num : (0:ℝ) ≤ 3)) hi h0core
    (show 0 ≤ 3*N^delta by positivity)
  have hJ2 : J^2 ≤ 1 := by nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hN (show 2*delta ≤ 4*delta by linarith)
  have h2 : 16*J^2*C*N^(2*delta)*E ≤ 16*C*N^(4*delta)*E := by
    have hh : 16*J^2*C*N^(2*delta)*E ≤ 16*1*C*N^(4*delta)*E := by gcongr
    simpa using hh
  have he1 : 3*N^delta*(c*N^(3*delta)*E)=3*c*N^(4*delta)*E := by
    calc
      _=3*c*(N^delta*N^(3*delta))*E := by ring
      _=_ := by rw [←Real.rpow_add hNp];congr 2;ring
  change 3*F*comparisonInnerPhysicalCore N delta E Q C J eps ≤ 3*N^delta*(c*N^(3*delta)*E) at h1
  rw [he1] at h1
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Real.rpow_pos_of_pos hNp (4*delta)).le) hE
  have he2 : N^delta*N^(4*delta)*E=N^(5*delta)*E := by rw [←Real.rpow_add hNp];congr 2;ring
  rw [he2] at h3
  nlinarith

def comparisonOuterFixedCoefficient (gamma Q C K J L : ℝ) : ℝ :=
  2*(K*(Q^2*C))^((2:ℝ)/3)*(1/gamma)*L^((1:ℝ)/3)+3*K+
    J^2*L+(2*Q)^4*C*J*L

theorem comparison_outer_core_log_bound {N delta margin gamma E Q C K J L eps : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hdelta : 0 ≤ delta)
    (hmargin : 0 ≤ margin) (hgamma : 0 < gamma) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hJ : 0 ≤ J) (hL : 0 ≤ L) (heps : eps ≤ delta) :
    comparisonOuterPhysicalCore N delta margin gamma E Q C K (J*Real.log N) (J*Real.log N) (L*Real.log N) eps ≤
      comparisonOuterFixedCoefficient gamma Q C K J L*(Real.log N)^3*E := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hx0 : 0 ≤ Real.log N := zero_le_one.trans hlog
  have hp1 : N^(-margin) ≤ 1 := by simpa using Real.rpow_le_rpow_of_exponent_le hN (neg_nonpos.mpr hmargin)
  have hp2 : N^(-delta) ≤ 1 := by simpa using Real.rpow_le_rpow_of_exponent_le hN (neg_nonpos.mpr hdelta)
  have hp3 : N^(eps-delta) ≤ 1 := by simpa using Real.rpow_le_rpow_of_exponent_le hN (sub_nonpos.mpr heps)
  have hroot : (Real.log N)^((1:ℝ)/3) ≤ Real.log N := by
    simpa using Real.rpow_le_rpow_of_exponent_le hlog (show (1:ℝ)/3 ≤ 1 by norm_num)
  have hx1 : (1:ℝ) ≤ (Real.log N)^3 := by nlinarith [sq_nonneg (Real.log N-1)]
  have hx13 : Real.log N ≤ (Real.log N)^3 := by nlinarith [sq_nonneg (Real.log N-1)]
  have hx23 : (Real.log N)^2 ≤ (Real.log N)^3 := by nlinarith [mul_nonneg (sq_nonneg (Real.log N)) (sub_nonneg.mpr hlog)]
  have h1 : 2*(K*(Q^2*C))^((2:ℝ)/3)*(1/gamma)*N^(-margin)*(L*Real.log N)^((1:ℝ)/3)*E ≤
      (2*(K*(Q^2*C))^((2:ℝ)/3)*(1/gamma)*L^((1:ℝ)/3))*(Real.log N)^3*E := by
    rw [Real.mul_rpow hL hx0]
    have hh : 2*(K*(Q^2*C))^((2:ℝ)/3)*(1/gamma)*N^(-margin)*(L^((1:ℝ)/3)*(Real.log N)^((1:ℝ)/3))*E ≤
      2*(K*(Q^2*C))^((2:ℝ)/3)*(1/gamma)*1*(L^((1:ℝ)/3)*(Real.log N)^3)*E := by gcongr;exact hroot.trans hx13
    nlinarith
  have h2 : 3*K*E ≤ 3*K*(Real.log N)^3*E := by
    have hh := mul_le_mul_of_nonneg_left hx1 (show 0 ≤ 3*K*E by positivity)
    nlinarith
  have h3 : (J*Real.log N)*(J*Real.log N)*(L*Real.log N)*N^(-delta)*E ≤ J^2*L*(Real.log N)^3*E := by
    have hh := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ (J*Real.log N)*(J*Real.log N)*(L*Real.log N) by positivity)
    have ht := mul_le_mul_of_nonneg_right hh hE
    nlinarith
  have h4 : (2*Q)^4*C*(J*Real.log N)*(L*Real.log N)*N^(eps-delta)*E ≤ (2*Q)^4*C*J*L*(Real.log N)^3*E := by
    have hh : (2*Q)^4*C*(J*Real.log N)*(L*Real.log N)*N^(eps-delta)*E ≤
        (2*Q)^4*C*(J*Real.log N)*(L*Real.log N)*1*E := by gcongr
    have ht := mul_le_mul_of_nonneg_left hx23 (show 0 ≤ (2*Q)^4*C*J*L*E by positivity)
    nlinarith
  unfold comparisonOuterPhysicalCore comparisonOuterFixedCoefficient
  nlinarith

theorem comparison_outer_error_core_eventually {delta margin gamma Q C K J L : ℝ}
    (hdelta : 0 < delta) (hmargin : 0 ≤ margin) (hgamma : 0 < gamma)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hJ : 0 ≤ J) (hL : 0 ≤ L) :
    ∀ᶠ N : ℝ in atTop, ∀ E F eps : ℝ, 0 ≤ E → 0 ≤ F → F ≤ N^delta → eps ≤ delta →
      (3*F+16)*comparisonOuterPhysicalCore N delta margin gamma E Q C K
        (J*Real.log N) (J*Real.log N) (L*Real.log N) eps ≤ N^(3*delta)*E := by
  let c := comparisonOuterFixedCoefficient gamma Q C K J L
  have hc : 0 ≤ c := by dsimp [c,comparisonOuterFixedCoefficient];positivity
  have ht := comparison_log_loss_eventually (C:=19*c) (p:=3) (by positivity) hdelta
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [ht,hlog,eventually_ge_atTop (1:ℝ)] with N hcoef hl hN
  intro E F eps hE hF hFN heps
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hNd : 1 ≤ N^delta := Real.one_le_rpow hN hdelta.le
  have hi := comparison_outer_core_log_bound (Q:=Q) hN hl hdelta.le hmargin hgamma hE hC hK hJ hL heps
  have h0core : 0 ≤ comparisonOuterPhysicalCore N delta margin gamma E Q C K
      (J*Real.log N) (J*Real.log N) (L*Real.log N) eps := by
    unfold comparisonOuterPhysicalCore
    have hlog0 : 0 ≤ Real.log N := by linarith
    positivity
  have hfac : 3*F+16 ≤ 19*N^delta := by linarith
  have hh := mul_le_mul hfac hi h0core (by positivity : 0 ≤ 19*N^delta)
  have hco : 19*c*(Real.log N)^3 ≤ N^delta := by
    simpa only [Real.rpow_ofNat] using hcoef
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hco (Real.rpow_pos_of_pos hNp delta).le) hE
  have heq : N^delta*N^delta=N^(2*delta) := by rw [←Real.rpow_add hNp];congr 1;ring
  rw [heq] at hm
  have hp := Real.rpow_le_rpow_of_exponent_le hN (show 2*delta ≤ 3*delta by linarith)
  have hpE := mul_le_mul_of_nonneg_right hp hE
  change (3*F+16)*_ ≤ 19*N^delta*(c*(Real.log N)^3*E) at hh
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization

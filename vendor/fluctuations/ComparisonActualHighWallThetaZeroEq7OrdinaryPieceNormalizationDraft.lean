module

public import ComparisonActualHighWallThetaZeroEq7ExactBudgetNormalizationDraft
public import ComparisonConditionalOptimizedSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem comparison_eq7_ordinary_eventual_log_gate_draft
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℝ in atTop, Real.log N ≤ N^eps := by
  have H := comparison_log_loss_eventually
    (C := (1:ℝ)) (p := (1:ℝ)) (eps := eps) (by norm_num) heps
  filter_upwards [H] with N hN
  simpa only [one_mul, Real.rpow_one] using hN

theorem comparison_eq7_ordinary_piece_from_atoms_draft
    {N delta eps E lam L F M a b c r z Cbin C Y K q : ℝ}
    (hN : 1 ≤ N) (hE : 0 < E) (hdelta : 0 ≤ delta)
    (heps : 0 < eps) (hL : 1 ≤ L) (hLpow : L ≤ N^eps)
    (hF0 : 0 ≤ F) (hCbin : 0 ≤ Cbin)
    (hC : 0 ≤ C) (hY : 0 ≤ Y) (hK : 1 ≤ K)
    (hq : 1 ≤ q)
    (hF : F ≤ Cbin*L^4)
    (ha : lam*M*a ≤
      2*(q^2*Y*K)^((2:ℝ)/3)*N^(4*delta/3)*E)
    (hb : lam*M*b ≤ 3*K*N^delta*E)
    (hc : lam*M*c ≤
      (663552*L^2*N^(-2*delta)+32*C*N^(2*delta))*E)
    (hr : lam*M*r ≤
      (2*q)^4*(2304*Y*L+16*C*Y*N^(2*delta))*N^eps*E)
    (hz : lam*z ≤ E) :
    lam*(F*M*(a+b+c+r)+z) ≤
      (Cbin*(2*(q^2*Y*K)^((2:ℝ)/3)+3*K+663552+32*C+
        (2*q)^4*(2304*Y+16*C*Y))+1)*
      L^5*N^(2*delta+eps)*E := by
  let X := N^(2*delta+eps)*E
  let Ka := 2*(q^2*Y*K)^((2:ℝ)/3)
  let Kb := 3*K
  let Kc := 663552+32*C
  let Kr := (2*q)^4*(2304*Y+16*C*Y)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hKa : 0 ≤ Ka := by dsimp [Ka]; positivity
  have hKb : 0 ≤ Kb := by dsimp [Kb]; positivity
  have hKc : 0 ≤ Kc := by dsimp [Kc]; positivity
  have hKr : 0 ≤ Kr := by dsimp [Kr]; positivity
  have hPowerNoLog (t : ℝ) (ht : t ≤ 2*delta+eps) :
      N^t*E ≤ X := by
    have Hp := Real.rpow_le_rpow_of_exponent_le hN ht
    have HE := mul_le_mul_of_nonneg_right Hp hE.le
    dsimp only [X]
    exact HE
  have hPower (t : ℝ) (ht : t ≤ 2*delta+eps) :
      N^t*E ≤ L*X := by
    have HL := mul_le_mul_of_nonneg_right hL hX
    nlinarith only [hPowerNoLog t ht,HL]
  have hlogLocal : L^2*N^(-2*delta)*E ≤ L*X := by
    have H1 := mul_le_mul_of_nonneg_right hLpow
      (Real.rpow_nonneg hNp.le (-2*delta))
    have H2 : N^eps*N^(-2*delta) = N^(eps-2*delta) := by
      rw [←Real.rpow_add hNp]
      congr 1
      ring
    rw [H2] at H1
    have H3 := Real.rpow_le_rpow_of_exponent_le hN
      (show eps-2*delta ≤ 2*delta+eps by linarith only [hdelta])
    have H4 := mul_le_mul_of_nonneg_left (H1.trans H3)
      (show 0 ≤ L*E by positivity)
    dsimp only [X]
    nlinarith only [H4]
  have ha' : lam*M*a ≤ Ka*L*X := by
    have H := mul_le_mul_of_nonneg_left
      (hPower (4*delta/3) (by linarith only [hdelta,heps])) hKa
    dsimp only [Ka] at H ⊢
    nlinarith only [ha,H]
  have hb' : lam*M*b ≤ Kb*L*X := by
    have H := mul_le_mul_of_nonneg_left
      (hPower delta (by linarith only [hdelta,heps])) hKb
    dsimp only [Kb] at H ⊢
    nlinarith only [hb,H]
  have hc' : lam*M*c ≤ Kc*L*X := by
    have Hlocal := mul_le_mul_of_nonneg_left hlogLocal
      (by norm_num : (0:ℝ) ≤ 663552)
    have Hradius := mul_le_mul_of_nonneg_left
      (hPower (2*delta) (by linarith only [heps]))
      (show 0 ≤ 32*C by positivity)
    dsimp only [Kc] at *
    nlinarith only [hc,Hlocal,Hradius]
  have hr' : lam*M*r ≤ Kr*L*X := by
    have Hlocal := mul_le_mul_of_nonneg_left
      (hPowerNoLog eps (by linarith only [hdelta]))
      (show 0 ≤ (2*q)^4*2304*Y*L by positivity)
    have hpow : N^(2*delta)*N^eps = N^(2*delta+eps) :=
      (Real.rpow_add hNp (2*delta) eps).symm
    have Hradius :
        (2*q)^4*16*C*Y*N^(2*delta)*N^eps*E ≤
          (2*q)^4*16*C*Y*L*X := by
      have HL := mul_le_mul_of_nonneg_right hL hX
      have H := mul_le_mul_of_nonneg_left HL
        (show 0 ≤ (2*q)^4*16*C*Y by positivity)
      have Heq :
          (2*q)^4*16*C*Y*N^(2*delta)*N^eps*E =
            ((2*q)^4*16*C*Y)*X := by
        dsimp only [X]
        rw [show (2*q)^4*16*C*Y*N^(2*delta)*N^eps*E =
          ((2*q)^4*16*C*Y)*(N^(2*delta)*N^eps)*E by ring,
          hpow]
        ring
      rw [Heq]
      nlinarith only [H]
    dsimp only [Kr] at *
    nlinarith only [hr,Hlocal,Hradius]
  have hz' : lam*z ≤ L^5*X := by
    have H0 := hPower 0 (by linarith only [hdelta,heps])
    have H0' : E ≤ L*X := by
      simpa only [Real.rpow_zero,one_mul] using H0
    have HL4 : 1 ≤ L^4 := by
      simpa using (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hL 4)
    have HL5 := mul_le_mul_of_nonneg_left HL4 hL0
    have HX := mul_le_mul_of_nonneg_right
      (show L ≤ L^5 by nlinarith only [HL5]) hX
    exact hz.trans (H0'.trans HX)
  have H := comparison_eq7_ordinary_literal_components_draft
    hL hX hF0 hCbin hKa hKb hKc hKr (by norm_num : (0:ℝ) ≤ 1)
    hF ha' hb' hc' hr' (by simpa only [one_mul] using hz')
  dsimp only [Ka,Kb,Kc,Kr,X] at H
  convert H using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

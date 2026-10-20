module

public import ComparisonNativeActualMinimumMassBudgets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000

theorem native_mass_two_thirds_homogeneity {x z : ℝ} (hx : 0 < x) (hz : 0 ≤ z) :
    (z*x^3)^((2:ℝ)/3)=x^2*z^((2:ℝ)/3) := by
  rw [Real.mul_rpow hz (pow_nonneg hx.le _),←Real.rpow_natCast x 3,
    ←Real.rpow_mul hx.le]
  norm_num
  ring

theorem native_mass_conditional_ledger_homogeneity
    (B : ℕ) (x v cut eta V T R L : ℝ) :
    nativeConditionalLedgerBudget B (x*v) (x^3*cut) (x*eta) (x^3*V) (x^3*T) (x^2*R) L =
      x^3*nativeConditionalLedgerBudget B v cut eta V T R L := by
  unfold nativeConditionalLedgerBudget
  ring

theorem native_mass_reverse_homogeneity {ell : ℕ} (hell : 2 < ell)
    {x d y Q : ℝ} (hx : 0 < x) (hd : 0 ≤ d) (hy : 0 ≤ y) :
    (x*d)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*Q)^(2*ell)*(x*y)^ell)^(1/((ell:ℝ)-1)) =
      x^2*(d^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) := by
  have he : (1:ℝ) < ell := by exact_mod_cast (by omega : 1 < ell)
  have hden : (ell:ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  have hc : 0 ≤ (2*Q)^(2*ell)*y^ell :=
    mul_nonneg (by rw [Nat.mul_comm 2 ell,pow_mul]; exact sq_nonneg _) (pow_nonneg hy _)
  rw [Real.mul_rpow hx.le hd,mul_pow x y ell,
    show (2*Q)^(2*ell)*(x^ell*y^ell)=x^ell*((2*Q)^(2*ell)*y^ell) by ring,
    Real.mul_rpow (pow_nonneg hx.le _) hc]
  have hpow : (x^ell)^(1/((ell:ℝ)-1))=x^((ell:ℝ)*(1/((ell:ℝ)-1))) := by
    rw [←Real.rpow_natCast x ell,←Real.rpow_mul hx.le]
  rw [hpow]
  have heq : ((ell:ℝ)-2)/((ell:ℝ)-1)+(ell:ℝ)*(1/((ell:ℝ)-1))=2 := by
    field_simp [hden]
    ring
  calc
    _ = (x^(((ell:ℝ)-2)/((ell:ℝ)-1))*x^((ell:ℝ)*(1/((ell:ℝ)-1))))*
      (d^(((ell:ℝ)-2)/((ell:ℝ)-1))*((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) := by ring
    _ = _ := by rw [←Real.rpow_add hx,heq,Real.rpow_two]

theorem native_mass_reverse_normalized {ell : ℕ} (hell : 2 < ell)
    {x D y Q : ℝ} (hx : 0 < x) (hD : 0 ≤ D) (hy : 0 ≤ y) :
    (D^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1)))/x^2 =
      (D/x)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*Q)^(2*ell)*(y/x)^ell)^(1/((ell:ℝ)-1)) := by
  have hh := native_mass_reverse_homogeneity (Q:=Q) hell hx
    (div_nonneg hD hx.le) (div_nonneg hy hx.le)
  rw [mul_div_cancel₀ _ hx.ne',mul_div_cancel₀ _ hx.ne'] at hh
  rw [hh,mul_div_cancel_left₀ _ (pow_ne_zero _ hx.ne')]

private theorem native_bin_loss_log_scaling
    {L A C r t : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A) (hC : 0 ≤ C) (hr : 0 ≤ r) (ht : 1 ≤ t) :
    nativeBinScaleLoss (L*t) (A*t^2) (C*t^2) r 1 ≤
      nativeBinScaleLoss L A C r 1*t^4 := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have h2 : 1 ≤ t^2 := one_le_pow₀ ht
  have h4 : 1 ≤ t^4 := one_le_pow₀ ht
  have ht2 : t ≤ t^2 := by nlinarith
  have ht4 : t ≤ t^4 := ht2.trans (by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr h2)])
  have h34 : t^3 ≤ t^4 := by
    have hh := mul_le_mul_of_nonneg_left ht (pow_nonneg ht0 3)
    nlinarith
  have hlin : 1+L*t ≤ (1+L)*t := by nlinarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1+L*t) hlin 2
  have hco : 66+64*L*t+65536*(1+L*t)^2 ≤ (66+64*L+65536*(1+L)^2)*t^2 := by
    have hfirst := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 66)
    have hsecond := mul_le_mul_of_nonneg_left ht2 (by positivity : 0 ≤ 64*L)
    rw [mul_pow] at hs
    nlinarith
  have hmean : 2*(76+64*L*t) ≤ 2*(76+64*L)*t^4 := by
    have hfirst := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 76)
    have hsecond := mul_le_mul_of_nonneg_left ht4 (by positivity : 0 ≤ 64*L)
    nlinarith
  have hside := mul_le_mul_of_nonneg_left h34 (by positivity : 0 ≤ 48*A*L*r)
  have hcov := mul_le_mul_of_nonneg_right hco (by positivity : 0 ≤ C*t^2*r^2)
  unfold nativeBinScaleLoss
  simp only [div_one]
  nlinarith

def nativeMassBinLossConstant (Ccut : ℝ) : ℝ :=
  nativeBinScaleLoss Ccut (108*32^2) (54*32^2) 64 1

theorem native_mass_binScaleLoss_log_bound {Ccut t v : ℝ}
    (hC : 0 ≤ Ccut) (ht : 1 ≤ t) (hv : 0 < v) :
    nativeBinScaleLoss (Ccut*t) (108*32^2*t^2) (54*32^2*t^2) (16*v) (v/4) ≤
      nativeMassBinLossConstant Ccut*t^4 := by
  have hr : (16*v)/(v/4)=(64:ℝ) := by field_simp; norm_num
  have hl : nativeBinScaleLoss (Ccut*t) (108*32^2*t^2) (54*32^2*t^2) (16*v) (v/4) =
      nativeBinScaleLoss (Ccut*t) (108*32^2*t^2) (54*32^2*t^2) 64 1 := by
    unfold nativeBinScaleLoss
    rw [hr]
    simp only [div_one]
  rw [hl]
  exact native_bin_loss_log_scaling hC (by norm_num) (by norm_num) (by norm_num) ht

theorem native_mass_binScaleLoss_constant_nonneg {Ccut : ℝ} (hC : 0 ≤ Ccut) :
    0 ≤ nativeMassBinLossConstant Ccut := by
  unfold nativeMassBinLossConstant nativeBinScaleLoss
  positivity

end OAI.SKFluctuations.LaplaceWindowFormalization

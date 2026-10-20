module

public import ComparisonActualHighWallHighMassDiameter
public import ComparisonNativeActualHighMassMesh

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 30000000
set_option linter.unusedVariables false
theorem actual_high_bin_loss_log_scaling
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

def actualHighMassBinLossConstant (Ccut width : ℝ) : ℝ :=
  nativeBinScaleLoss Ccut (108*(2*width)^2) (54*(2*width)^2) (4*width) 1

theorem actual_high_mass_bin_loss_constant_nonneg {Ccut width : ℝ}
    (hCcut : 0 ≤ Ccut) (hwidth : 0 ≤ width) :
    0 ≤ actualHighMassBinLossConstant Ccut width := by
  unfold actualHighMassBinLossConstant nativeBinScaleLoss
  positivity

theorem actual_high_mass_binScaleLoss_log_bound {Ccut t width v : ℝ}
    (hCcut : 0 ≤ Ccut) (ht : 1 ≤ t) (hwidth : 0 ≤ width) (hv : 0 < v) :
    nativeBinScaleLoss (Ccut*t) (108*(2*width)^2*t^2) (54*(2*width)^2*t^2)
      (width*v) (v/4) ≤ actualHighMassBinLossConstant Ccut width*t^4 := by
  have hr : (width*v)/(v/4)=4*width := by field_simp
  have hl : nativeBinScaleLoss (Ccut*t) (108*(2*width)^2*t^2) (54*(2*width)^2*t^2)
      (width*v) (v/4)=
    nativeBinScaleLoss (Ccut*t) (108*(2*width)^2*t^2) (54*(2*width)^2*t^2) (4*width) 1 := by
    unfold nativeBinScaleLoss
    rw [hr]
    simp only [div_one]
  rw [hl]
  exact actual_high_bin_loss_log_scaling hCcut (by positivity) (by positivity) (by positivity) ht

theorem actual_high_mass_ordinary_normalization {x W width v P y Q diam rev F cut : ℝ}
    (hx : 0 < x) (hW : 0 < W) (hv : 0 < v) :
    (F*(width*v)*(2*((Q^2*y)/(P*(width*v)^2))^((2:ℝ)/3)+
        3/(P*(width*v)^2)+diam^2+rev)+
      18*(((Q^2*y)^2*P*(width*v)^2)^((1:ℝ)/3)+2)*cut)/(x^4*v/W^2)=
    width*F*(2*(((Q^2*y)/(P*(width*v)^2))^((2:ℝ)/3)*(W^2/x^4))+
        3*((W^2/x^4)/(P*(width*v)^2))+diam^2*(W^2/x^4)+rev*(W^2/x^4))+
      (18*(((Q^2*y)^2*P*(width*v)^2)^((1:ℝ)/3)+2)*cut)*(W^2/(x^4*v)) := by
  field_simp

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def highMassOrdinaryBudgetAtDiameter
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Ccut width cut v diam : ℝ) : ℝ :=
  nativeBinScaleLoss (Ccut*Real.log a.data.N) (108*(2*width)^2*(Real.log a.data.N)^2)
    (54*(2*width)^2*(Real.log a.data.N)^2) (width*v) (v/4)*(width*v)*
    (2*((Q^2*a.highMassHeight width v)/(a.highMassPower width v*(width*v)^2))^((2:ℝ)/3)+
      3/(a.highMassPower width v*(width*v)^2)+diam^2+a.highMassReverse ell Q width v diam)+
    18*(((Q^2*a.highMassHeight width v)^2*a.highMassPower width v*(width*v)^2)^((1:ℝ)/3)+2)*cut

theorem highMassPower_le
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (width v : ℝ) :
    a.highMassPower width v ≤ a.data.N*D^2 := by
  apply mul_le_mul_of_nonneg_left _ a.data.hN.le
  exact (laplaceComparisonStrength_le a.data.d (sq_nonneg a.data.d) _).trans
    (pow_le_pow_left₀ a.data.hd.le a.hdD 2)
theorem high_mass_inverse_four_coarse
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N) :
    1/a.xs^4 ≤ C0^4*a.data.N^4 := by
  have H:=a.high_mass_inverse_power hC0 4
  simp only [Nat.cast_ofNat,show (4:ℝ)/6=(2:ℝ)/3 by norm_num] at H
  have HH:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg a.data.hN.le ((2:ℝ)/3))
  have HE : a.data.N^((2:ℝ)/3)*(1/(a.data.N^((2:ℝ)/3)*a.xs^4))=1/a.xs^4:=by
    field_simp
  have HR : a.data.N^((2:ℝ)/3)*(C0^4*a.data.N^(-(4:ℝ)*m))=
      C0^4*a.data.N^((2:ℝ)/3-4*m):=by
    rw [show a.data.N^((2:ℝ)/3)*(C0^4*a.data.N^(-(4:ℝ)*m))=
      C0^4*(a.data.N^((2:ℝ)/3)*a.data.N^(-4*m)) by ring_nf,←Real.rpow_add a.data.hN]
    rw [show (2:ℝ)/3 + -(4:ℝ)*m=(2:ℝ)/3-4*m by ring_nf]
  rw [HE,HR] at HH
  apply HH.trans
  have Hpow:=Real.rpow_le_rpow_of_exponent_le hN (show (2:ℝ)/3-4*m ≤ 4 by linarith)
  simpa only [Real.rpow_ofNat] using mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 4)

theorem high_mass_normalization_weight_le
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N)
    {c v : ℝ} (hc : 0 < c) (hW1 : a.data.d ≤ 1)
    (hv : 0 < v) (hvlo : c*a.data.d ≤ v) :
    a.data.d^2/(a.xs^4*v) ≤ (C0^4/c)*a.data.N^4 := by
  have hW:=a.data.hd
  have hxs:=a.hxs
  have Hvar : a.data.d^2/v ≤ 1/c:=by
    apply (div_le_div_iff₀ hv hc).mpr
    have HS : a.data.d^2 ≤ a.data.d:=by nlinarith
    have H:=mul_le_mul_of_nonneg_left HS hc.le
    nlinarith only [H,hvlo]
  have Hinv:=a.high_mass_inverse_four_coarse hm hC0 hN
  have H:=mul_le_mul Hvar Hinv (by positivity : 0 ≤ 1/a.xs^4) (one_div_pos.mpr hc).le
  convert H using 1 <;> ring_nf

theorem high_mass_ordinary_cut_le
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N)
    {Q width c v cut : ℝ} (hwidth : 0 ≤ width) (hxsD : a.xs ≤ a.data.d) (hc : 0 < c) (hW1 : a.data.d ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1) (hvlo : c*a.data.d ≤ v)
    (hcut : 0 ≤ cut) :
    (18*(((Q^2*a.highMassHeight width v)^2*a.highMassPower width v*(width*v)^2)^((1:ℝ)/3)+2)*cut)*
      (a.data.d^2/(a.xs^4*v)) ≤
      (18*((4*width^2)*Q^4*D^2+3)*C0^4/c)*a.data.N^5*cut := by
  have hxs:=a.hxs
  have hW:=a.data.hd
  have hxs1:=hxsD.trans hW1
  have HY : 0 ≤ a.highMassHeight width v:=by unfold highMassHeight;positivity
  have HY2 : a.highMassHeight width v ≤ 2:=by
    unfold highMassHeight
    linarith [min_le_right (width*v) 1]
  have Hpower:=a.highMassPower_le width v
  have hP:=a.highMassPower_pos width v
  have HX : (Q^2*a.highMassHeight width v)^2*a.highMassPower width v*(width*v)^2 ≤
      (4*width^2)*Q^4*D^2*a.data.N:=by
    have Hy:=pow_le_pow_left₀ HY HY2 2
    have Hv:=pow_le_pow_left₀ hv.le hv1 2
    have H:=mul_le_mul (mul_le_mul_of_nonneg_left Hpower (show 0 ≤ Q^4*(a.highMassHeight width v)^2 by positivity))
      Hv (sq_nonneg v) (show 0 ≤ Q^4*(a.highMassHeight width v)^2*(a.data.N*D^2) by positivity)
    have HH:=mul_le_mul_of_nonneg_left Hy (show 0 ≤ Q^4*(a.data.N*D^2) by positivity)
    have HHH:=mul_le_mul_of_nonneg_left H (show 0 ≤ width^2 by positivity)
    nlinarith only [HH,HHH]
  have HX0 : 0 ≤ (Q^2*a.highMassHeight width v)^2*a.highMassPower width v*(width*v)^2:=by positivity
  have Hroot:=mass_root_third_le_linear (A:=(4*width^2)*Q^4*D^2+1) (N:=a.data.N) HX0
    (by nlinarith [mul_nonneg (show 0 ≤ Q^4 by positivity) (sq_nonneg D)])
    hN (by nlinarith only [HX,a.data.hN.le])
  have Hraw : 18*(((Q^2*a.highMassHeight width v)^2*a.highMassPower width v*(width*v)^2)^((1:ℝ)/3)+2)*cut ≤
      (18*((4*width^2)*Q^4*D^2+3))*a.data.N*cut:=by
    have Hb : ((Q^2*a.highMassHeight width v)^2*a.highMassPower width v*(width*v)^2)^((1:ℝ)/3)+2 ≤
        ((4*width^2)*Q^4*D^2+3)*a.data.N:=by nlinarith only [Hroot,hN]
    have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hb
      (by norm_num : (0:ℝ) ≤ 18)) hcut
    convert H using 1; ring_nf
  have Hweight:=a.high_mass_normalization_weight_le hm hC0 hN hc hW1 hv hvlo
  have H:=mul_le_mul Hraw Hweight (by positivity : 0 ≤ a.data.d^2/(a.xs^4*v))
    (show 0 ≤ (18*((4*width^2)*Q^4*D^2+3))*a.data.N*cut by positivity)
  convert H using 1; ring_nf

theorem high_mass_ordinary_budget_normalized_le
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Ccut width : ℝ) (hwidth : 0 ≤ width) (hCcut : 0 ≤ Ccut)
    (hlog : 1 ≤ Real.log a.data.N) {v diam cut : ℝ}
    (hv : 0 < v) (hdiam : 0 ≤ diam) :
    a.highMassOrdinaryBudgetAtDiameter ell Q Ccut width cut v diam/
        (a.xs^4*v/a.data.d^2) ≤
      (width*actualHighMassBinLossConstant Ccut width)*(Real.log a.data.N)^4*
        (2*(((Q^2*a.highMassHeight width v)/(a.highMassPower width v*(width*v)^2))^((2:ℝ)/3)*
              (a.data.d^2/a.xs^4))+
          3*((a.data.d^2/a.xs^4)/(a.highMassPower width v*(width*v)^2))+
          diam^2*(a.data.d^2/a.xs^4)+
          a.highMassReverse ell Q width v diam*(a.data.d^2/a.xs^4))+
      (18*(((Q^2*a.highMassHeight width v)^2*a.highMassPower width v*(width*v)^2)^((1:ℝ)/3)+2)*cut)*
        (a.data.d^2/(a.xs^4*v)) := by
  have Hnorm:=actual_high_mass_ordinary_normalization (width:=width) (P:=a.highMassPower width v)
    (y:=a.highMassHeight width v) (Q:=Q) (diam:=diam)
    (rev:=a.highMassReverse ell Q width v diam)
    (F:=nativeBinScaleLoss (Ccut*Real.log a.data.N) (108*(2*width)^2*(Real.log a.data.N)^2)
      (54*(2*width)^2*(Real.log a.data.N)^2) (width*v) (v/4)) (cut:=cut)
    a.hxs a.data.hd hv
  unfold highMassOrdinaryBudgetAtDiameter
  rw [Hnorm]
  have HF:=actual_high_mass_binScaleLoss_log_bound hCcut hlog hwidth hv
  have hP:=a.highMassPower_pos width v
  have hxs:=a.hxs
  have hW:=a.data.hd
  have hy : 0 ≤ a.highMassHeight width v:=by unfold highMassHeight;positivity
  have hEven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hR : 0 ≤ a.highMassReverse ell Q width v diam:=by
    unfold highMassReverse
    exact mul_nonneg (Real.rpow_nonneg hdiam _)
      (Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg hy ell)) _)
  have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HF hwidth)
    (show 0 ≤ 2*(((Q^2*a.highMassHeight width v)/(a.highMassPower width v*(width*v)^2))^((2:ℝ)/3)*
        (a.data.d^2/a.xs^4))+
      3*((a.data.d^2/a.xs^4)/(a.highMassPower width v*(width*v)^2))+
      diam^2*(a.data.d^2/a.xs^4)+
      a.highMassReverse ell Q width v diam*(a.data.d^2/a.xs^4) by positivity)
  nlinarith only [H]

theorem eventually_high_mass_ordinary_budget_of_reverse_rate
    {m delta cl cu Az C0 Ct D Bclock width c Cdiam : ℝ}
    (ell : ℕ) (_hell : 2 < ell) (Q : ℝ)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) (hwidth : 16 ≤ width) (hc : 0 < c) (hCdiam : 0 < Cdiam)
    (hreverse : ∀ᶠ n : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ a.data.d →
        ∀v : ℝ,0 < v → v ≤ 1 → c*a.data.d ≤ v →
          a.highMassReverse ell Q width v (a.highMassDiameter Cdiam v)*
            (a.data.d^2/a.xs^4) ≤
              a.data.N^(-(32*actualMassSavingExponent m delta))) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ a.data.d →
        ∀v : ℝ,0 < v → v ≤ 1 → c*a.data.d ≤ v →
          a.highMassOrdinaryBudgetAtDiameter ell Q 10 width
            (a.data.N^(-(10:ℝ))) v (a.highMassDiameter Cdiam v)/
              (a.xs^4*v/a.data.d^2) ≤
                a.data.N^(-actualMassSavingExponent m delta) := by
  let eta:=actualMassSavingExponent m delta
  let Cbin:=actualHighMassBinLossConstant 10 width
  let Cerr:=18*((4*width^2)*Q^4*D^2+3)*C0^4/c
  have hEta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  have Heta:=actualMassSavingExponent_bounds m delta
  have hBin : 0 ≤ Cbin:=actual_high_mass_bin_loss_constant_nonneg (by norm_num) (by linarith)
  have Hnoise:=eventually_high_mass_noise_polynomial
    (cu:=cu) (Ct:=Ct) (D:=D) (Bclock:=Bclock) Q width c hwidth hc hm hdelta hcl hAz hC0
  have Hdiam:=eventually_actual_high_wall_high_mass_diameter_square_polynomial_le
    (cl:=cl) (cu:=cu) (Az:=Az) (D:=D) (Bclock:=Bclock)
    hm hdelta hCt hC0 hc hCdiam.le
  have Hcut:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=5) (s:=32*eta) (by dsimp [eta];nlinarith [Heta.1]) 0 Cerr)
  have Habs:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=32*eta) (s:=eta) (by linarith) 4 (7*width*Cbin+1))
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  filter_upwards [Hnoise,Hdiam,hreverse,Hcut,Habs,Hlog] with n hnNoise hnDiam hnReverse hnCut hnAbs hnLog
  intro a hxsD v hv hv1 hvlo
  have hW1 := a.data.hd1
  have hN : 1 ≤ a.data.N:=by dsimp [ActualHighWallData.N];exact_mod_cast Nat.succ_pos n
  have hxs:=a.hxs
  have hW:=a.data.hd
  have hxs1:=hxsD.trans hW1
  have hlog : 1 ≤ Real.log a.data.N:=hnLog
  have hdiam:=a.highMassDiameter_pos hCdiam (by linarith) hv
  have Hn:=hnNoise a hxsD v hvlo
  have Hd:=hnDiam a hxsD v hvlo
  have Hr:=hnReverse a hxsD v hv hv1 hvlo
  have Hbudget:=a.high_mass_ordinary_budget_normalized_le ell Q 10 width (by linarith) (by norm_num)
    hlog (cut:=a.data.N^(-(10:ℝ))) hv hdiam.le
  have Hmesh:=a.high_mass_ordinary_cut_le hm hC0 hN (by linarith : 0 ≤ width) hxsD hc hW1 hv hv1 hvlo
    (Real.rpow_nonneg a.data.hN.le (-(10:ℝ))) (Q:=Q)
  have HEcut : (18*((4*width^2)*Q^4*D^2+3)*C0^4/c)*a.data.N^5*a.data.N^(-(10:ℝ))=
      Cerr*a.data.N^(-(5:ℝ)):=by
    change Cerr*a.data.N^5*a.data.N^(-(10:ℝ))=Cerr*a.data.N^(-(5:ℝ))
    rw [←Real.rpow_natCast a.data.N 5,mul_assoc,←Real.rpow_add a.data.hN]
    norm_num
  rw [HEcut] at Hmesh
  have HcutFinal:=Hmesh.trans (by simpa only [pow_zero,mul_one] using hnCut)
  have Hsum : 2*(((Q^2*a.highMassHeight width v)/(a.highMassPower width v*(width*v)^2))^((2:ℝ)/3)*
      (a.data.d^2/a.xs^4))+
      3*((a.data.d^2/a.xs^4)/(a.highMassPower width v*(width*v)^2))+
      (a.highMassDiameter Cdiam v)^2*(a.data.d^2/a.xs^4)+
      a.highMassReverse ell Q width v (a.highMassDiameter Cdiam v)*
        (a.data.d^2/a.xs^4) ≤ 7*a.data.N^(-(32*eta)):=by
    nlinarith only [Hn.1,Hn.2,Hd,Hr]
  have HsumMul:=mul_le_mul_of_nonneg_left Hsum
    (show 0 ≤ width*Cbin*(Real.log a.data.N)^4 by positivity)
  have Hmain : a.highMassOrdinaryBudgetAtDiameter ell Q 10 width
      (a.data.N^(-(10:ℝ))) v (a.highMassDiameter Cdiam v)/
        (a.xs^4*v/a.data.d^2) ≤
        7*width*Cbin*(Real.log a.data.N)^4*a.data.N^(-(32*eta))+a.data.N^(-(32*eta)):=by
    nlinarith only [Hbudget,HsumMul,HcutFinal]
  have HlogPow : 1 ≤ (Real.log a.data.N)^4:=one_le_pow₀ hlog
  have Hlast:=mul_le_mul_of_nonneg_right HlogPow (Real.rpow_nonneg a.data.hN.le (-(32*eta)))
  have Htotal : a.highMassOrdinaryBudgetAtDiameter ell Q 10 width
      (a.data.N^(-(10:ℝ))) v (a.highMassDiameter Cdiam v)/
        (a.xs^4*v/a.data.d^2) ≤
        (7*width*Cbin+1)*(Real.log a.data.N)^4*a.data.N^(-(32*eta)):=by
    nlinarith only [Hmain,Hlast]
  exact Htotal.trans hnAbs

theorem exists_high_mass_ordinary_polynomial_order
    {m delta cl cu Az C0 Ct D Bclock width c Cdiam : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) (hD : 0 < D)
    (hwidth : 16 ≤ width) (hc : 0 < c) (hCdiam : 0 < Cdiam) :
    ∃ell : ℕ, 2 < ell ∧ ∀Q : ℝ, 1 ≤ Q →
      ∀ᶠ n : ℕ in atTop,
        ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
          a.xs ≤ a.data.d → ∀v : ℝ, 0 < v → v ≤ 1 → c*a.data.d ≤ v →
            a.highMassOrdinaryBudgetAtDiameter ell Q 10 width (a.data.N^(-(10:ℝ))) v
              (a.highMassDiameter Cdiam v)/(a.xs^4*v/a.data.d^2) ≤
                a.data.N^(-actualMassSavingExponent m delta) := by
  obtain ⟨ell,hell,Hreverse⟩ := exists_high_mass_reverse_polynomial_order
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (Bclock:=Bclock) hm hdelta hC0 hD
    (by linarith : 0 ≤ width) hc hCdiam
  refine ⟨ell,hell,?_⟩
  intro Q hQ
  exact eventually_high_mass_ordinary_budget_of_reverse_rate ell hell Q hm hdelta hcl hAz
    hCt hC0 hwidth hc hCdiam (Hreverse Q hQ)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

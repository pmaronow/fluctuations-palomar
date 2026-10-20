module

public import ComparisonNativeActualMassBudgetScale
public import ComparisonNativeMassBudgetHomogeneity

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def nativeMassReverseConstant (ell : ℕ) (Q Cy : ℝ) : ℝ :=
  ((2*Q)^(2*ell)*Cy^ell)^(1/((ell:ℝ)-1))

def nativeMassOrdinaryEnvelope (ell : ℕ) (Q Cv Cnoise t d : ℝ) : ℝ :=
  2*(Q^2*(1+16*Cv)*Cnoise)^((2:ℝ)/3)*t^((4:ℝ)/3)+
    3*Cnoise*t^2+d^2+nativeMassReverseConstant ell Q (1+16*Cv)*
      d^(((ell:ℝ)-2)/((ell:ℝ)-1))

theorem mass_reverse_normalized_le {ell : ℕ} (hell : 2<ell)
    {x D y Q Cy : ℝ} (hx : 0<x) (hD : 0 ≤ D) (hy : 0 ≤ y) (_hCy : 0 ≤ Cy)
    (hsize : y ≤ Cy*x) :
    (D^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1)))/x^2 ≤
      nativeMassReverseConstant ell Q Cy*(D/x)^(((ell:ℝ)-2)/((ell:ℝ)-1)) := by
  rw [native_mass_reverse_normalized hell hx hD hy]
  have hyx : y/x ≤ Cy:=(div_le_iff₀ hx).mpr (by simpa only [mul_comm] using hsize)
  have he : (1:ℝ)<ell:=by exact_mod_cast (by omega : 1<ell)
  have H:=pow_le_pow_left₀ (div_nonneg hy hx.le) hyx ell
  have Hmul:=mul_le_mul_of_nonneg_left H (show 0 ≤ (2*Q)^(2*ell) by
    rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _)
  have HC : 0 ≤ (2*Q)^(2*ell)*(y/x)^ell := by
    apply mul_nonneg
    · rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
    · exact pow_nonneg (div_nonneg hy hx.le) _
  have Hpow:=Real.rpow_le_rpow HC Hmul (by positivity : 0 ≤ 1/((ell:ℝ)-1))
  have HH:=mul_le_mul_of_nonneg_left Hpow
    (Real.rpow_nonneg (div_nonneg hD hx.le) (((ell:ℝ)-2)/((ell:ℝ)-1)))
  simpa only [nativeMassReverseConstant,mul_comm] using HH

theorem mass_ordinary_cubic_normalization
    {x P B y D R F Q cut : ℝ} (hx : 0<x) (hP : 0<P) (hB : 0<B) (hy : 0 ≤ y) :
    (F*B*(2*((Q^2*y)/(P*B^2))^((2:ℝ)/3)+3/(P*B^2)+D^2+R)+
      18*(((Q^2*y)^2*P*B^2)^((1:ℝ)/3)+2)*cut)/x^3 =
      F*(B/x)*(2*(Q^2*(y/x)*(1/(P*B^2*x^2)))^((2:ℝ)/3)+
        3*(1/(P*B^2*x^2))+(D/x)^2+R/x^2)+
        18*(((Q^2*y)^2*P*B^2)^((1:ℝ)/3)+2)*cut/x^3 := by
  have Hnum : Q^2*(y/x)*(1/(P*B^2*x^2))*x^3=(Q^2*y)/(P*B^2) := by field_simp
  have Hpow:=native_mass_two_thirds_homogeneity hx
    (show 0 ≤ Q^2*(y/x)*(1/(P*B^2*x^2)) by positivity)
  rw [Hnum] at Hpow
  rw [Hpow]
  field_simp

theorem mass_noise_two_thirds_le {Q Cy Cnoise t y tau : ℝ}
    (hCy : 0 ≤ Cy) (hCn : 0 ≤ Cnoise) (ht : 0 ≤ t) (hy : 0 ≤ y) (htau : 0 ≤ tau)
    (hyb : y ≤ Cy) (htb : tau ≤ Cnoise*t^2) :
    (Q^2*y*tau)^((2:ℝ)/3) ≤ (Q^2*Cy*Cnoise)^((2:ℝ)/3)*t^((4:ℝ)/3) := by
  have H : Q^2*y*tau ≤ (Q^2*Cy*Cnoise)*t^2 := by
    have Hmul:=mul_le_mul (mul_le_mul_of_nonneg_left hyb (sq_nonneg Q)) htb htau
      (mul_nonneg (sq_nonneg Q) hCy)
    simpa only [mul_assoc] using Hmul
  have Hpow:=Real.rpow_le_rpow (by positivity) H (by norm_num : (0:ℝ) ≤ 2/3)
  apply Hpow.trans_eq
  rw [Real.mul_rpow (by positivity) (sq_nonneg _),←Real.rpow_natCast t 2,←Real.rpow_mul ht]
  norm_num

theorem mass_root_third_le_linear {z A N : ℝ} (hz : 0 ≤ z) (hA : 1 ≤ A) (hN : 1 ≤ N)
    (hbound : z ≤ A*N) : z^((1:ℝ)/3) ≤ A*N := by
  have hAN : 1 ≤ A*N := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hN)]
  calc
    _ ≤ (A*N)^((1:ℝ)/3) := Real.rpow_le_rpow hz hbound (by norm_num)
    _ ≤ (A*N)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hAN (by norm_num)
    _ = _ := Real.rpow_one _

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_mass_diameter_nonneg
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (_hlog : 0 ≤ Real.log a.context.N) : 0 ≤ a.canonicalMassDiameter := by
  unfold canonicalMassDiameter cavityCapTravel
  have Hlog : 0 ≤ Real.log ((1+a.context.U)/a.context.U):=
    Real.log_nonneg ((one_le_div a.context.hU).mpr (by linarith))
  have hL:=a.context.hL.le
  have hN:=a.context.hN.le
  positivity

theorem canonical_mass_cut_error_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) (hm : 0 < m) (hN : 1 ≤ a.context.N) (hxs1 : a.xs ≤ 1)
    {v Q cut : ℝ} (hv : 0<v) (hv1 : v ≤ 1) (hcut : 0 ≤ cut) :
    18*((((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3))+2)*cut/a.xs^3 ≤
      (18*(3+1024*Q^4*D^2)*C0^3)*a.context.N^4*cut := by
  have hx:=a.hxs
  have hP:=(a.canonical_mass_power_pos v).le
  have Hy0 : 0 ≤ a.canonicalMassHeight v:=by unfold canonicalMassHeight;positivity
  have Hy : a.canonicalMassHeight v ≤ 2 := by
    unfold canonicalMassHeight
    have H:=min_le_right (16*v) (1:ℝ)
    linarith
  have HB : (16*v)^2 ≤ (16:ℝ)^2:=pow_le_pow_left₀ (by positivity) (by linarith) 2
  have HY : (Q^2*a.canonicalMassHeight v)^2 ≤ (2*Q^2)^2:=
    pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg (sq_nonneg Q) (sub_nonneg.mpr Hy)]) 2
  have HP:=a.canonical_mass_power_le v
  have Hinside : (Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2 ≤
      (1+1024*Q^4*D^2)*a.context.N := by
    have H1:=mul_le_mul HY HP (a.canonical_mass_power_pos v).le (sq_nonneg _)
    have H2:=mul_le_mul H1 HB (sq_nonneg _) (by positivity : 0 ≤ (2*Q^2)^2*(a.context.N*D^2))
    nlinarith [H2,a.context.hN]
  have Hroot:=mass_root_third_le_linear (by positivity)
    (show 1 ≤ 1+1024*Q^4*D^2 by nlinarith [show 0 ≤ 1024*Q^4*D^2 by positivity]) hN Hinside
  have Hcoeff :
      18*((((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3))+2) ≤
      18*(3+1024*Q^4*D^2)*a.context.N := by nlinarith
  have Hinv:=a.canonical_mass_inverse_cube_le hC0 hm hN
  have Hmul:=mul_le_mul Hcoeff Hinv (by positivity : 0 ≤ 1/a.xs^3)
    (by positivity : 0 ≤ 18*(3+1024*Q^4*D^2)*a.context.N)
  have Hcut:=mul_le_mul_of_nonneg_right Hmul hcut
  convert Hcut using 1 <;> ring

theorem canonical_ordinary_mass_budget_normalized_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (hell : 2<ell) (Q Ccut c Cv : ℝ)
    (hCcut : 0 ≤ Ccut) (hc : 0<c) (hCv : 0 ≤ Cv)
    (hm : 0 < m) (hcl : 0<cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0<C0)
    (hxs1 : a.xs ≤ 1) (hN : 1 ≤ a.context.N) (hlog : 1 ≤ Real.log a.context.N)
    {v cut : ℝ} (hv : 0<v) (hv1 : v ≤ 1) (hvlo : c*a.xs ≤ v)
    (hvhi : v ≤ Cv*a.xs) (hcut : 0 ≤ cut) :
    a.canonicalOrdinaryMassBudget ell Q (Ccut*Real.log a.context.N) cut v/a.xs^3 ≤
      nativeMassBinLossConstant Ccut*(Real.log a.context.N)^4*(16*Cv)*
        nativeMassOrdinaryEnvelope ell Q Cv
          (actualMassStrengthConstant Az cl Ct Cv/(256*c^2))
          (a.context.U/a.xs) (a.canonicalMassDiameter/a.xs)+
      (18*(3+1024*Q^4*D^2)*C0^3)*a.context.N^4*cut := by
  let x:=a.xs
  let y:=a.canonicalMassHeight v
  let P:=a.canonicalMassPower v
  let B:=16*v
  let Dm:=a.canonicalMassDiameter
  let R:=a.canonicalMassReverse ell Q v
  let F:=nativeBinScaleLoss (Ccut*Real.log a.context.N)
    (108*32^2*(Real.log a.context.N)^2) (54*32^2*(Real.log a.context.N)^2) B (v/4)
  let tau:=1/(P*B^2*x^2)
  let Cn:=actualMassStrengthConstant Az cl Ct Cv/(256*c^2)
  let t:=a.context.U/x
  let d:=Dm/x
  have hx : 0<x:=a.hxs
  have hP : 0<P:=a.canonical_mass_power_pos v
  have hB : 0<B:=by dsimp [B];positivity
  have hy : 0 ≤ y:=by dsimp [y,canonicalMassHeight];positivity
  have hd : 0 ≤ Dm:=a.canonical_mass_diameter_nonneg (by linarith)
  have ht : 0 ≤ t:=div_nonneg a.context.hU.le hx.le
  have hCy : 0 ≤ 1+16*Cv:=by positivity
  have hCn : 0 ≤ Cn:=by
    dsimp [Cn,actualMassStrengthConstant,actualMassEndpointConstant]
    positivity
  have hF : 0 ≤ F:=by
    dsimp [F,nativeBinScaleLoss]
    positivity
  have htau : 0 ≤ tau:=by dsimp [tau];positivity
  have Hy:=a.canonical_mass_height_le hCv hvhi
  have Hyx : y/x ≤ 1+16*Cv:=(div_le_iff₀ hx).mpr (by simpa only [mul_comm] using Hy)
  have Htau : tau ≤ Cn*t^2:=mass_normalized_noise_le hP hx a.context.hU hv
    (show 0 ≤ actualMassStrengthConstant Az cl Ct Cv by
      unfold actualMassStrengthConstant actualMassEndpointConstant;positivity)
    hc (a.canonical_mass_power_size hcl hAz hCt hxs1 hv hCv hvhi) hvlo
  have Hfirst:=mass_noise_two_thirds_le (Q:=Q) hCy hCn ht (div_nonneg hy hx.le) htau Hyx Htau
  have Hrev : R/x^2 ≤ nativeMassReverseConstant ell Q (1+16*Cv)*d^(((ell:ℝ)-2)/((ell:ℝ)-1)) :=
    mass_reverse_normalized_le hell hx hd hy hCy Hy
  have Hinside : 2*(Q^2*(y/x)*tau)^((2:ℝ)/3)+3*tau+d^2+R/x^2 ≤
      nativeMassOrdinaryEnvelope ell Q Cv Cn t d := by
    dsimp [nativeMassOrdinaryEnvelope]
    nlinarith [Hfirst,Htau,Hrev]
  have Hinside0 : 0 ≤ 2*(Q^2*(y/x)*tau)^((2:ℝ)/3)+3*tau+d^2+R/x^2 := by
    have hEven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
    have hR : 0 ≤ R:=by dsimp [R,canonicalMassReverse];positivity
    positivity
  have Hnorm:=mass_ordinary_cubic_normalization (x:=x) (P:=P) (B:=B) (y:=y)
    (D:=Dm) (R:=R) (F:=F) (Q:=Q) (cut:=cut) hx hP hB hy
  have HF:=native_mass_binScaleLoss_log_bound hCcut hlog hv
  have HBx : B/x ≤ 16*Cv:=(div_le_iff₀ hx).mpr (by dsimp [B];nlinarith)
  have Houter:=mul_le_mul
    (mul_le_mul HF HBx (div_nonneg hB.le hx.le)
      (show 0 ≤ nativeMassBinLossConstant Ccut*(Real.log a.context.N)^4 by
        exact mul_nonneg (native_mass_binScaleLoss_constant_nonneg hCcut) (pow_nonneg (by linarith) _)))
    Hinside Hinside0 (mul_nonneg
      (mul_nonneg (native_mass_binScaleLoss_constant_nonneg hCcut) (pow_nonneg (by linarith) _))
      (mul_nonneg (by norm_num) hCv))
  have Hcut:=a.canonical_mass_cut_error_le (Q:=Q) hC0 hm hN hxs1 hv hv1 hcut
  change a.canonicalOrdinaryMassBudget ell Q (Ccut*Real.log a.context.N) cut v/x^3 ≤ _
  change (F*B*(2*((Q^2*y)/(P*B^2))^((2:ℝ)/3)+3/(P*B^2)+Dm^2+R)+
    18*(((Q^2*y)^2*P*B^2)^((1:ℝ)/3)+2)*cut)/x^3 ≤ _
  rw [Hnorm]
  exact add_le_add Houter Hcut

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

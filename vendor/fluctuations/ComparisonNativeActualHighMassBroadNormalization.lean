module

public import ComparisonNativeActualHighMassSharpScale
public import ComparisonNativeActualLocalDiameterBudgetMonotonicity

@[expose] public section

noncomputable section
set_option maxHeartbeats 11000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def nativeHighMassBroadFiniteConstant (Ccut : ℝ) : ℝ :=
  20736*Ccut+3456*(66+64*Ccut+65536*(1+Ccut)^2)+4*(76+64*Ccut)+128

theorem native_high_mass_broad_finite_constant_nonneg {Ccut : ℝ} (hCcut : 0 ≤ Ccut) :
    0 ≤ nativeHighMassBroadFiniteConstant Ccut := by
  unfold nativeHighMassBroadFiniteConstant
  positivity

theorem mass_high_broad_exact_normalization {x W v width cut D V T R L : ℝ}
    (hx : 0 < x) (hW : 0 < W) (hv : 0 < v) :
    nativeConditionalLedgerBudget 1 width cut D V T R L/(x^4*v/W^2)=
      48*(V*W^2/(x^4*v))+(76+64*L)*(width/v)*(D^2*W^2/x^4)+
        32*(width/v)*(R*W^2/x^4)+(66+64*L+65536*(1+L)^2)*(T*W^2/(x^4*v))+
        16*cut*W^2/(x^4*v) := by
  unfold nativeConditionalLedgerBudget
  norm_num
  field_simp

theorem mass_high_broad_variance_normalization {x W P v loss l wlog : ℝ}
    (hx : 0 < x) (hP : 0 < P) (hv : 0 < v) :
    (108*loss*l^2/(P*(v/4))*wlog)*W^2/(x^4*v)=
      432*loss*(W^2/(P*v^2*x^4))*l^2*wlog := by
  field_simp
  ring

theorem mass_high_broad_covariance_normalization {x W P v width loss l : ℝ}
    (hx : 0 < x) (hP : 0 < P) (hv : 0 < v) :
    (54*loss*l^2*width/(P*(v/4)^2))*W^2/(x^4*v)=
      864*loss*(W^2/(P*v^2*x^4))*l^2*(width/v) := by
  field_simp
  ring

theorem mass_high_broad_finite_normalized_le
    {x W P v width cut diameter R loss l Ccut : ℝ}
    (hx : 0 < x) (hW : 0 < W) (hP : 0 < P) (hv : 0 < v)
    (hwidth : 0 ≤ width) (hwidthhi : width ≤ 4*v)
    (_hdiameter : 0 ≤ diameter) (hR : 0 ≤ R) (hloss : 0 ≤ loss)
    (hl : 1 ≤ l) (hCcut : 0 ≤ Ccut) (hwlog : Real.log (width/cut) ≤ Ccut*l) :
    nativeConditionalLedgerBudget 1 width cut diameter
      (108*loss*l^2/(P*(v/4))*Real.log (width/cut))
      (54*loss*l^2*width/(P*(v/4)^2)) R (Ccut*l)/(x^4*v/W^2) ≤
      nativeHighMassBroadFiniteConstant Ccut*l^5*
        (loss*(W^2/(P*v^2*x^4))/l+diameter^2*W^2/x^4+R*W^2/x^4)+
        16*cut*W^2/(x^4*v) := by
  let tau := W^2/(P*v^2*x^4)
  let dn := diameter^2*W^2/x^4
  let rn := R*W^2/x^4
  let TC := 66+64*Ccut+65536*(1+Ccut)^2
  let EC := 4*(76+64*Ccut)
  let VC := 20736*Ccut
  let CC := 3456*TC
  let V := 108*loss*l^2/(P*(v/4))*Real.log (width/cut)
  let T := 54*loss*l^2*width/(P*(v/4)^2)
  have hl0 : 0 ≤ l := zero_le_one.trans hl
  have hlp : 0 < l := zero_lt_one.trans_le hl
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hd : 0 ≤ dn := by dsimp [dn]; positivity
  have hr : 0 ≤ rn := by dsimp [rn]; positivity
  have hwv : width/v ≤ 4 := (div_le_iff₀ hv).mpr (by simpa only [mul_comm] using hwidthhi)
  have hTC : 0 ≤ TC := by dsimp [TC]; positivity
  have hEC : 0 ≤ EC := by dsimp [EC]; positivity
  have hVC : 0 ≤ VC := by dsimp [VC]; positivity
  have hCC : 0 ≤ CC := by dsimp [CC]; positivity
  have HV : V*W^2/(x^4*v) ≤ (432*Ccut)*loss*tau*l^3 := by
    rw [mass_high_broad_variance_normalization hx hP hv]
    have HH := mul_le_mul_of_nonneg_left hwlog (show 0 ≤ 432*loss*tau*l^2 by positivity)
    convert HH using 1
    ring
  have HT : T*W^2/(x^4*v) ≤ 3456*loss*tau*l^2 := by
    rw [mass_high_broad_covariance_normalization hx hP hv]
    have HH := mul_le_mul_of_nonneg_left hwv (show 0 ≤ 864*loss*tau*l^2 by positivity)
    convert HH using 1
    ring
  have HC : 66+64*(Ccut*l)+65536*(1+Ccut*l)^2 ≤ TC*l^2 := by
    have HH : 1+Ccut*l ≤ (1+Ccut)*l := by nlinarith
    have HS := pow_le_pow_left₀ (by positivity) HH 2
    have HL : l ≤ l^2 := le_self_pow₀ hl (by omega)
    have H1 : 1 ≤ l^2 := one_le_pow₀ hl
    dsimp [TC]
    nlinarith only [HS,HL,H1,mul_le_mul_of_nonneg_left HL (show 0 ≤ 64*Ccut by positivity)]
  have HVT : 48*(V*W^2/(x^4*v)) ≤ VC*l^4*(loss*tau) := by
    have HL : l^3 ≤ l^4 := pow_le_pow_right₀ hl (by omega)
    have HH := mul_le_mul_of_nonneg_left HV (show 0 ≤ (48:ℝ) by norm_num)
    have HP := mul_le_mul_of_nonneg_left HL (show 0 ≤ VC*loss*tau by positivity)
    dsimp [VC] at HP ⊢
    nlinarith only [HH,HP]
  have HCT : (66+64*(Ccut*l)+65536*(1+Ccut*l)^2)*(T*W^2/(x^4*v)) ≤
      CC*l^4*(loss*tau) := by
    have HT0 : 0 ≤ T*W^2/(x^4*v) := by dsimp [T]; positivity
    have HH := mul_le_mul HC HT HT0 (mul_nonneg hTC (sq_nonneg l))
    convert HH using 1
    dsimp [CC]
    ring
  have HET : (76+64*(Ccut*l))*(width/v)*dn ≤ EC*l^5*dn := by
    have HE : 76+64*(Ccut*l) ≤ (76+64*Ccut)*l := by nlinarith
    have HL : l ≤ l^5 := le_self_pow₀ hl (by omega)
    calc
      _ ≤ ((76+64*Ccut)*l)*4*dn := by gcongr
      _ ≤ ((76+64*Ccut)*l^5)*4*dn := by gcongr
      _ = _ := by dsimp [EC]; ring
  have HRT : 32*(width/v)*rn ≤ 128*l^5*rn := by
    have H1 : 1 ≤ l^5 := one_le_pow₀ hl
    have HH := mul_le_mul_of_nonneg_right hwv (show 0 ≤ 32*rn by positivity)
    have HP := mul_le_mul_of_nonneg_right H1 (show 0 ≤ 128*rn by positivity)
    nlinarith only [HH,HP]
  rw [mass_high_broad_exact_normalization hx hW hv]
  change 48*(V*W^2/(x^4*v))+(76+64*(Ccut*l))*(width/v)*dn+
    32*(width/v)*rn+(66+64*(Ccut*l)+65536*(1+Ccut*l)^2)*(T*W^2/(x^4*v))+
    16*cut*W^2/(x^4*v) ≤
    nativeHighMassBroadFiniteConstant Ccut*l^5*(loss*tau/l+dn+rn)+16*cut*W^2/(x^4*v)
  have HH := add_le_add (add_le_add (add_le_add HVT HET) HRT) HCT
  apply (add_le_add HH (le_refl _)).trans
  apply add_le_add _ (le_refl _)
  have HE : nativeHighMassBroadFiniteConstant Ccut*l^5*(loss*tau/l+dn+rn)=
      (VC+CC+EC+128)*l^4*(loss*tau)+(VC+CC+EC+128)*l^5*(dn+rn) := by
    dsimp [nativeHighMassBroadFiniteConstant,VC,CC,EC,TC]
    field_simp
    ring
  rw [HE]
  apply le_of_sub_nonneg
  convert (show 0 ≤ (EC+128)*l^4*(loss*tau)+(VC+CC+128)*l^5*dn+
      (VC+CC+EC)*l^5*rn by positivity) using 1
  ring

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_high_mass_broad_budget_normalized_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    (hlog : 1 ≤ Real.log a.context.N)
    {v width cut diameter : ℝ} (hv : 0 < v) (hwidth : 0 ≤ width) (hwidthhi : width ≤ 4*v)
    (hdiameter : 0 ≤ diameter) (hwidthlog : Real.log (width/cut) ≤ Ccut*Real.log a.context.N) :
    let W := a.canonicalDirectTestBandScale
    let loss := (32:ℝ)^2+25*(1+v/a.context.U)*Real.log ((1+a.context.U)/a.context.U)+1
    a.canonicalBroadMassBudgetAtDiameter ell Q (Ccut*Real.log a.context.N) cut v width diameter/
      (a.xs^4*v/W^2) ≤
      nativeHighMassBroadFiniteConstant Ccut*(Real.log a.context.N)^5*
        (loss*(W^2/(a.canonicalMassPower v*v^2*a.xs^4))/Real.log a.context.N+
          diameter^2*W^2/a.xs^4+
          a.canonicalMassReverseAtDiameter ell Q v diameter*W^2/a.xs^4)+
        16*cut*W^2/(a.xs^4*v) := by
  dsimp only
  have hU := a.context.hU
  have hxs := a.hxs
  have hloss : 0 ≤ (32:ℝ)^2+25*(1+v/a.context.U)*Real.log ((1+a.context.U)/a.context.U)+1 := by
    have hrl : 0 ≤ Real.log ((1+a.context.U)/a.context.U) :=
      Real.log_nonneg ((one_le_div hU).mpr (by linarith))
    positivity
  have hEven : 0 ≤ (2*Q)^(2*ell) := by rw [Nat.mul_comm 2 ell,pow_mul]; exact sq_nonneg _
  have hy : 0 ≤ a.canonicalMassHeight v := by unfold canonicalMassHeight; positivity
  have hR : 0 ≤ a.canonicalMassReverseAtDiameter ell Q v diameter := by
    unfold canonicalMassReverseAtDiameter
    exact mul_nonneg (Real.rpow_nonneg hdiameter _)
      (Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg hy ell)) _)
  exact mass_high_broad_finite_normalized_le a.hxs a.canonical_direct_test_band_pos
    (a.canonical_mass_power_pos v) hv hwidth hwidthhi hdiameter hR hloss hlog hCcut hwidthlog

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

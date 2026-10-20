module

public import ComparisonNativeActualBroadMassNormalization
public import ComparisonNativeActualMassBandScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_broad_mass_band_budget_normalized_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (hell : 2 < ell) (Q Ccut c Cv : ℝ)
    (hCcut : 0 ≤ Ccut) (hc : 0 < c) (hCv : 0 ≤ Cv)
    (hm : 0 < m) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    {W : ℝ} (hxsW : a.xs ≤ W) (hW1 : W ≤ 1) (hN : 1 ≤ a.context.N) (hlog : 1 ≤ Real.log a.context.N)
    (htsmall : a.context.U/W ≤ 1)
    {v width cut : ℝ} (hv : 0 < v) (hvlo : c*W ≤ v) (hvhi : v ≤ Cv*W)
    (hwidth : 0 ≤ width) (hwidthhi : width ≤ 4*v) (hcut : 0 ≤ cut)
    (hwidthlog : Real.log (width/cut) ≤ Ccut*Real.log a.context.N) :
    a.canonicalBroadMassBudget ell Q (Ccut*Real.log a.context.N) cut v width/W^3 ≤
      nativeMassBroadEnvelopeConstant ell Q Ccut Cv
        (actualMassStrengthConstant Az cl Ct Cv/(256*c^2)) (nativeMassBroadTraceConstant Cv D)*
        (Real.log a.context.N)^5*
          (a.context.U/W+(a.canonicalMassDiameter/W)^2+
            (a.canonicalMassDiameter/W)^(((ell:ℝ)-2)/((ell:ℝ)-1)))+
        (16*C0^3)*a.context.N^3*cut := by
  let x := W
  let y := a.canonicalMassHeight v
  let P := a.canonicalMassPower v
  let Dm := a.canonicalMassDiameter
  let R := a.canonicalMassReverse ell Q v
  let l := Real.log a.context.N
  let tau := 1/(P*(16*v)^2*x^2)
  let t := a.context.U/x
  let d := Dm/x
  let Cn := actualMassStrengthConstant Az cl Ct Cv/(256*c^2)
  let Ctr := nativeMassBroadTraceConstant Cv D
  let Cr := nativeMassReverseConstant ell Q (1+16*Cv)
  let loss := 1025+25*(1+v/a.context.U)*Real.log ((1+a.context.U)/a.context.U)
  let V := 108*loss*l^2/(P*(v/4))*Real.log (width/cut)
  let T := 54*loss*l^2*width/(P*(v/4)^2)
  have hx : 0 < x := a.hxs.trans_le hxsW
  have hxs0 := a.hxs.le
  have hP : 0 < P := a.canonical_mass_power_pos v
  have hU := a.context.hU
  have hl : 1 ≤ l := hlog
  have hl0 : 0 ≤ l := zero_le_one.trans hl
  have ht : 0 ≤ t := div_nonneg a.context.hU.le hx.le
  have hd : 0 ≤ Dm := a.canonical_mass_diameter_nonneg hl0
  have hCn : 0 ≤ Cn := by
    dsimp [Cn,actualMassStrengthConstant,actualMassEndpointConstant]
    positivity
  have hlogD : 0 ≤ Real.log (1+D^2) := Real.log_nonneg (by nlinarith [sq_nonneg D])
  have hCtr : 0 ≤ Ctr := by dsimp [Ctr,nativeMassBroadTraceConstant]; positivity
  have hCr : 0 ≤ Cr := by
    dsimp [Cr,nativeMassReverseConstant]
    have hEven : 0 ≤ (2*Q)^(2*ell) := by rw [Nat.mul_comm 2 ell,pow_mul]; exact sq_nonneg _
    exact Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg (by positivity) _)) _
  have Htau : tau ≤ Cn*t^2 := mass_normalized_noise_le hP hx a.context.hU hv
    (show 0 ≤ actualMassStrengthConstant Az cl Ct Cv by
      unfold actualMassStrengthConstant actualMassEndpointConstant; positivity)
    hc (a.canonical_mass_band_power_size hcl hAz hCt hxsW hW1 hv hvhi) hvlo
  have Hloss : loss*tau ≤ Cn*Ctr*l*t := mass_broad_loss_noise_le hx a.context.hU hv.le
    hCn hCv (by positivity) hl htsmall hvhi
    (Real.log_nonneg ((one_le_div a.context.hU).mpr (by linarith)))
    (a.canonical_mass_trace_log_le hN hlog) Htau
  have hvx : v/x ≤ Cv := (div_le_iff₀ hx).mpr (by simpa only [mul_comm] using hvhi)
  have hwx : width/x ≤ 4*Cv := (div_le_iff₀ hx).mpr (by nlinarith)
  have Hvnorm := mass_broad_variance_normalization (loss:=loss) (tlog:=l)
    (wlog:=Real.log (width/cut)) hx hP hv
  have HTnorm := mass_broad_covariance_normalization (width:=width) (loss:=loss) (tlog:=l) hx hP hv
  have hloss : 0 ≤ loss := by
    dsimp [loss]
    have hr : 0 ≤ Real.log ((1+a.context.U)/a.context.U) :=
      Real.log_nonneg ((one_le_div a.context.hU).mpr (by linarith))
    positivity
  have hltau : 0 ≤ loss*tau := by
    exact mul_nonneg hloss (by dsimp [tau]; positivity)
  have HV : V/x^3 ≤ (110592*Cn*Ctr*Cv*Ccut)*l^4*t := by
    rw [Hvnorm]
    have HE : 110592*loss*l^2*(v/x)*tau*Real.log (width/cut)=
      110592*(loss*tau)*l^2*(v/x)*Real.log (width/cut) := by ring
    rw [HE]
    have Hfirst := mul_le_mul_of_nonneg_left hwidthlog
      (show 0 ≤ 110592*(loss*tau)*l^2*(v/x) by positivity)
    apply Hfirst.trans
    calc
      _ ≤ 110592*(Cn*Ctr*l*t)*l^2*Cv*(Ccut*l) := by gcongr
      _ = _ := by ring
  have HT : T/x^3 ≤ (221184*Cn*Ctr*(4*Cv))*l^3*t := by
    rw [HTnorm]
    have HE : 221184*loss*l^2*(width/x)*tau=221184*(loss*tau)*l^2*(width/x) := by ring
    rw [HE]
    calc
      _ ≤ 221184*(Cn*Ctr*l*t)*l^2*(4*Cv) := by gcongr
      _ = _ := by ring
  have hR : R/x^2 ≤ Cr*d^(((ell:ℝ)-2)/((ell:ℝ)-1)) :=
    mass_reverse_normalized_le hell hx hd
      (by dsimp [y,canonicalMassHeight]; positivity) (by positivity)
      (a.canonical_mass_band_height_le hxsW hvhi)
  have hrev : 0 ≤ R/x^2 := by
    have hEven : 0 ≤ (2*Q)^(2*ell) := by rw [Nat.mul_comm 2 ell,pow_mul]; exact sq_nonneg _
    have hy : 0 ≤ y := by dsimp [y,canonicalMassHeight]; positivity
    have hR0 : 0 ≤ R := mul_nonneg (Real.rpow_nonneg hd _)
      (Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg hy ell)) _)
    exact div_nonneg hR0 (sq_nonneg _)
  have HEta : (76+64*(Ccut*l))*(width/x)*d^2 ≤ ((76+64*Ccut)*(4*Cv))*l^5*d^2 := by
    have HC : 76+64*(Ccut*l) ≤ (76+64*Ccut)*l := by nlinarith
    have HP : l ≤ l^5 := le_self_pow₀ hl (by omega)
    calc
      _ ≤ ((76+64*Ccut)*l)*(4*Cv)*d^2 := by gcongr
      _ ≤ ((76+64*Ccut)*l^5)*(4*Cv)*d^2 := by gcongr
      _ = _ := by ring
  have HR : 32*(width/x)*(R/x^2) ≤ (128*Cv*Cr)*l^5*d^(((ell:ℝ)-2)/((ell:ℝ)-1)) := by
    have H1 : 1 ≤ l^5 := one_le_pow₀ hl
    calc
      _ ≤ 32*(4*Cv)*(Cr*d^(((ell:ℝ)-2)/((ell:ℝ)-1))) := by gcongr
      _ = (128*Cv*Cr)*d^(((ell:ℝ)-2)/((ell:ℝ)-1)) := by ring
      _ ≤ _ := by
        have HR0 : 0 ≤ (128*Cv*Cr)*d^(((ell:ℝ)-2)/((ell:ℝ)-1)) :=
          mul_nonneg (by positivity) (Real.rpow_nonneg (div_nonneg hd hx.le) _)
        have HH := mul_le_mul_of_nonneg_left H1 HR0
        nlinarith [HH]
  have HTcoeff : 66+64*(Ccut*l)+65536*(1+Ccut*l)^2 ≤
      (66+64*Ccut+65536*(1+Ccut)^2)*l^2 := by
    have HH : 1+Ccut*l ≤ (1+Ccut)*l := by nlinarith
    have HHpow := pow_le_pow_left₀ (by positivity) HH 2
    have HL : l ≤ l^2 := by nlinarith
    have H1 : 1 ≤ l^2 := one_le_pow₀ hl
    nlinarith
  have HTterm : (66+64*(Ccut*l)+65536*(1+Ccut*l)^2)*(T/x^3) ≤
      ((66+64*Ccut+65536*(1+Ccut)^2)*221184*Cn*Ctr*(4*Cv))*l^5*t := by
    have HT0 : 0 ≤ T/x^3 := by dsimp [T]; positivity
    calc
      _ ≤ ((66+64*Ccut+65536*(1+Ccut)^2)*l^2)*
          ((221184*Cn*Ctr*(4*Cv))*l^3*t) := by gcongr
      _ = _ := by ring
  have HVterm : 48*(V/x^3) ≤ (48*110592*Cn*Ctr*Cv*Ccut)*l^5*t := by
    have HL : l^4 ≤ l^5 := pow_le_pow_right₀ hl (by omega)
    calc
      _ ≤ 48*((110592*Cn*Ctr*Cv*Ccut)*l^4*t) := by gcongr
      _ ≤ 48*((110592*Cn*Ctr*Cv*Ccut)*l^5*t) := by gcongr
      _ = _ := by ring
  have Hinv : 1/x^3 ≤ C0^3*a.context.N^3 :=
    (one_div_le_one_div_of_le (pow_pos a.hxs 3) (pow_le_pow_left₀ a.hxs.le hxsW 3)).trans
      (a.canonical_mass_inverse_cube_le hC0 hm hN)
  have Hcut := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Hinv
      (show 0 ≤ (16:ℝ) by norm_num)) hcut
  have Hcut' : 16*cut/x^3 ≤ (16*C0^3)*a.context.N^3*cut := by
    convert Hcut using 1 <;> ring
  have Hnorm := mass_broad_cubic_normalization (width:=width) (cut:=cut) (D:=Dm)
    (V:=V) (T:=T) (R:=R) (L:=Ccut*l) hx
  have hloss_eq : (32:ℝ)^2+25*(1+v/a.context.U)*Real.log ((1+a.context.U)/a.context.U)+1=loss := by
    dsimp [loss]
    ring
  rw [canonicalBroadMassBudget]
  rw [hloss_eq]
  change nativeConditionalLedgerBudget 1 width cut Dm V T R (Ccut*l)/x^3 ≤
    nativeMassBroadEnvelopeConstant ell Q Ccut Cv Cn Ctr*l^5*
      (t+d^2+d^(((ell:ℝ)-2)/((ell:ℝ)-1)))+(16*C0^3)*a.context.N^3*cut
  rw [Hnorm]
  have Hdsq : 0 ≤ d^2 := sq_nonneg _
  have Hdpow : 0 ≤ d^(((ell:ℝ)-2)/((ell:ℝ)-1)) := Real.rpow_nonneg (div_nonneg hd hx.le) _
  have Htotal := add_le_add
    (add_le_add (add_le_add (add_le_add HVterm HEta) HR) HTterm) Hcut'
  apply Htotal.trans
  apply add_le_add _ (le_refl _)
  apply le_of_sub_nonneg
  convert (show 0 ≤
    ((76+64*Ccut)*(4*Cv))*l^5*(t+d^(((ell:ℝ)-2)/((ell:ℝ)-1)))+
    (128*Cv*Cr)*l^5*(t+d^2)+
    ((48*110592*Cn*Ctr*Cv*Ccut)+
      (66+64*Ccut+65536*(1+Ccut)^2)*221184*Cn*Ctr*(4*Cv))*l^5*
        (d^2+d^(((ell:ℝ)-2)/((ell:ℝ)-1))) by positivity) using 1
  dsimp [nativeMassBroadEnvelopeConstant,Cr]
  ring

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

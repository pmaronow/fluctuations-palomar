module

public import ComparisonActualHighWallCriticalBroadTraceNumerics
public import ComparisonActualHighWallOrdinaryNumerics
public import ComparisonNativeActualMassBudgetRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def criticalBroadDiameterConstant (C0 D : ℝ) : ℝ := 9*C0^3*(2+Real.log (1+D^2))

theorem criticalBroadDiameterConstant_nonneg {C0 D : ℝ} (hC0 : 0≤C0) :
    0≤criticalBroadDiameterConstant C0 D := by
  have H:=Real.log_nonneg (by nlinarith [sq_nonneg D] : (1:ℝ)≤1+D^2)
  dsimp [criticalBroadDiameterConstant]
  positivity

theorem criticalBroad_diameter_nonneg
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlog : 0≤Real.log a.data.N) : 0≤a.criticalBroadMassDiameter := by
  unfold criticalBroadMassDiameter
  exact mul_nonneg (mul_nonneg (by norm_num) hlog)
    (add_nonneg a.data.hrbounds.1.le a.cavityCapTravel_nonneg)

theorem criticalBroad_diameter_rate
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hdelta : 0≤delta) (hC0 : 0 < C0)
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) :
    a.criticalBroadMassDiameter/a.xs ≤
      criticalBroadDiameterConstant C0 D*(Real.log a.data.N)^2*a.data.N^(-3*m) := by
  let L:=Real.log a.data.N
  let Cr:=1+Real.log (1+D^2)
  have hL : 1≤L:=hlog
  have hCr : 0≤Cr:=by dsimp [Cr];have :=Real.log_nonneg (by nlinarith [sq_nonneg D] : (1:ℝ)≤1+D^2);linarith
  have Horigin := (div_le_div_of_nonneg_right a.radius_le_smallMass a.hxs.le).trans
    (a.high_mass_small_ratio hC0)
  have Htravel:=comparisonTravel_ratio_bound (δ:=delta) hN a.data.hE a.data.hd
    a.hdD hC0 a.hupper a.hlower
  have Hscale : a.cavityCapTravel/a.xs≤a.cavityCapTravel/
      comparisonLowerScale a.data.N a.data.E a.data.d :=
    div_le_div_of_nonneg_left a.cavityCapTravel_nonneg
      (comparisonLowerScale_pos a.data.hN a.data.hE a.data.hd) a.hscale
  have Htravel' : a.cavityCapTravel/a.xs≤C0^3*a.data.N^(-(3*m+delta))*
      (Real.log a.data.N+Real.log (1+D^2)):=Hscale.trans Htravel
  have Hpow : a.data.N^(-(3*m+delta))≤a.data.N^(-3*m):=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have HlogD : 0≤Real.log (1+D^2):=Real.log_nonneg (by nlinarith [sq_nonneg D])
  have Hlogs : L+Real.log (1+D^2)≤Cr*L:=by
    dsimp only [Cr]
    nlinarith [mul_nonneg HlogD (sub_nonneg.mpr hL)]
  have HtravelSaved : a.cavityCapTravel/a.xs≤C0^3*a.data.N^(-3*m)*(Cr*L) := by
    apply Htravel'.trans
    have HP:=mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 3)
    exact mul_le_mul HP Hlogs (by positivity) (by positivity)
  have Hsum:=add_le_add Horigin HtravelSaved
  have HL:=mul_le_mul_of_nonneg_left Hsum (show 0≤9*L by linarith)
  have H1 : C0^3*a.data.N^(-3*m)≤C0^3*a.data.N^(-3*m)*L:=
    le_mul_of_one_le_right (by positivity) hL
  have Hsaved:=mul_le_mul_of_nonneg_left (add_le_add H1 (le_refl
    (C0^3*a.data.N^(-3*m)*(Cr*L)))) (show 0≤9*L by linarith)
  unfold criticalBroadMassDiameter
  have HE : 9*L*(a.data.rmin/a.xs+a.cavityCapTravel/a.xs)=
      9*Real.log a.data.N*(a.data.rmin+a.cavityCapTravel)/a.xs:=by dsimp [L];ring
  rw [HE] at HL
  apply HL.trans (Hsaved.trans_eq _)
  dsimp [criticalBroadDiameterConstant,Cr,L]
  ring

def criticalBroadReverseConstant (ell : ℕ) (Q C C0 D : ℝ) : ℝ :=
  nativeMassReverseConstant ell Q (1+16*C)*
    (criticalBroadDiameterConstant C0 D)^(((ell:ℝ)-2)/((ell:ℝ)-1))

theorem criticalBroadReverseConstant_nonneg (ell : ℕ) (Q : ℝ)
    {C C0 D : ℝ} (hC : 0≤C) (hC0 : 0≤C0) :
    0≤criticalBroadReverseConstant ell Q C C0 D := by
  apply mul_nonneg _ (Real.rpow_nonneg (criticalBroadDiameterConstant_nonneg hC0) _)
  unfold nativeMassReverseConstant
  apply Real.rpow_nonneg
  apply mul_nonneg
  · rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  · positivity

theorem criticalBroad_reverse_nonneg
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q : ℝ) {v : ℝ} (hv : 0≤v) (hlog : 0≤Real.log a.data.N) :
    0≤a.criticalBroadMassReverse ell Q v := by
  unfold criticalBroadMassReverse
  apply mul_nonneg (Real.rpow_nonneg (a.criticalBroad_diameter_nonneg hlog) _) _
  apply Real.rpow_nonneg
  apply mul_nonneg
  · rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  · exact pow_nonneg (a.highMassHeight_nonneg (width:=16) (by norm_num) hv) ell

theorem criticalBroad_reverse_rate
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (hell : 2<ell) (Q : ℝ)
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0)
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N)
    {C v : ℝ} (hC : 0≤C) (hv : 0≤v) (hvhi : v≤C*a.xs) :
    a.criticalBroadMassReverse ell Q v/a.xs^2 ≤
      criticalBroadReverseConstant ell Q C C0 D*(Real.log a.data.N)^4*
        a.data.N^(-(32*actualMassSavingExponent m delta)) := by
  have Htheta:=native_mass_reverse_exponent_range hell
  have Heta:=actualMassSavingExponent_bounds m delta
  have Hpow:=native_mass_fixed_power_rate_le hN hlog
    (div_nonneg (a.criticalBroad_diameter_nonneg (by linarith)) a.hxs.le)
    (criticalBroadDiameterConstant_nonneg (D:=D) hC0.le)
    (a:=((ell:ℝ)-2)/((ell:ℝ)-1)) (b:=3*m) (q:=32*actualMassSavingExponent m delta)
    (by linarith [Htheta.1]) (by linarith [Htheta.2])
    (by nlinarith [Heta.2.1,mul_nonneg (show 0≤3*m by linarith) (sub_nonneg.mpr Htheta.1)])
    (by simpa only [neg_mul] using a.criticalBroad_diameter_rate hdelta.le hC0 hN hlog)
  have Hheight : a.criticalBroadMassHeight v≤(1+16*C)*a.xs := by
    unfold criticalBroadMassHeight
    nlinarith [min_le_left (16*v) (1:ℝ)]
  have Hrev:=mass_reverse_normalized_le hell a.hxs
    (a.criticalBroad_diameter_nonneg (by linarith))
    (a.highMassHeight_nonneg (width:=16) (by norm_num) hv)
    (show 0≤1+16*C by positivity) Hheight (Q:=Q)
  have HC : 0≤nativeMassReverseConstant ell Q (1+16*C) := by
    unfold nativeMassReverseConstant
    apply Real.rpow_nonneg
    apply mul_nonneg
    · rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
    · positivity
  have HS:=mul_le_mul_of_nonneg_left Hpow HC
  apply Hrev.trans
  simpa only [criticalBroadReverseConstant,mul_assoc] using HS

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

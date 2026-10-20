module

public import ComparisonActualHighWallTargetResponseSavedOnStrongMasterAlong
public import ComparisonActualHighWallInitialSavedCoefficientModulus
public import ComparisonActualGeneralTargetResponseCommonModulusNumerics
public import ComparisonActualHighWallTargetRadiusFractionalPrices
public import ComparisonActualHighWallCriticalThermalRadiusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000

def actualHighWallInitialSavedResponseRate
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (saving eta Ccut : ℝ) : ℝ :=
  (n:ℝ)^(-eta)+((n+1:ℕ):ℝ)^(-m)+
    ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))+
    ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))+
    ((n+1:ℕ):ℝ)^(-(actualSlowWindowExponent m delta/128)/2)+
    ((n+1:ℕ):ℝ)^(-saving)+
    (∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2))/M.data.d^2+M.data.d^3

theorem actual_high_wall_initial_saved_response_rate_nonneg
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (saving eta Ccut : ℝ) (hCcut : 0 ≤ Ccut) :
    0 ≤ actualHighWallInitialSavedResponseRate M saving eta Ccut := by
  have HJ : 0 ≤ ∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2):=
    intervalIntegral.integral_nonneg (mul_nonneg hCcut M.data.hd.le) (fun _ _=>Real.sqrt_nonneg _)
  have HN : ∀q : ℝ,0 ≤ ((n+1:ℕ):ℝ)^q:=fun q=>Real.rpow_nonneg (Nat.cast_nonneg _) q
  have Heta : 0 ≤ (n:ℝ)^(-eta):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have HJdiv:=div_nonneg HJ (sq_nonneg M.data.d)
  have Hd3:=pow_nonneg M.data.hd.le 3
  unfold actualHighWallInitialSavedResponseRate
  linarith only [Heta,HN (-m),HN (-(actualMassSavingExponent m delta/256)),
    HN (-(actualMassSavingExponent m delta/32)),HN (-(actualSlowWindowExponent m delta/128)/2),
    HN (-saving),HJdiv,Hd3]

theorem actual_high_wall_initial_saved_response_rate_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (saving eta Ccut : ℝ) (hsaving : 0 < saving) (heta : 0 < eta) (hCcut : 0 < Ccut)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>actualHighWallInitialSavedResponseRate (M n) saving eta Ccut)
      atTop (𝓝 0) := by
  have Hdim : Tendsto (fun n=>(dim n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hdim
  have HN : Tendsto (fun n=>((dim n+1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have Heta:=(tendsto_rpow_neg_atTop heta).comp Hdim
  have Hm:=(tendsto_rpow_neg_atTop hm).comp HN
  have Hmass:=actualMassSavingExponent_pos hm hdelta
  have Hrho:=(tendsto_rpow_neg_atTop (div_pos Hmass (by norm_num : (0:ℝ)<256))).comp HN
  have Hstar:=(tendsto_rpow_neg_atTop (div_pos Hmass (by norm_num : (0:ℝ)<32))).comp HN
  have Hslow:=actualSlowWindowExponent_pos hm hdelta hroom
  have Hpair:=(tendsto_rpow_neg_atTop
    (div_pos (div_pos Hslow (by norm_num : (0:ℝ)<128)) (by norm_num : (0:ℝ)<2))).comp HN
  have Hterm:=(tendsto_rpow_neg_atTop hsaving).comp HN
  have HJ:=ActualHighWallOverlapMinimum.actual_high_wall_critical_thermal_radius_tendsto_zero_along
    hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hdlim hsRatio
  have H:=((((((Heta.add Hm).add Hrho).add Hstar).add Hpair).add Hterm).add HJ).add (hdlim.pow 3)
  simpa only [actualHighWallInitialSavedResponseRate,Function.comp_def,zero_add,zero_pow (by decide : 3 ≠ 0),neg_div] using H

theorem exists_actual_high_wall_initial_saved_response_fractional_constant
    (depth : ℕ) (P : (j : Fin depth) → ActualHighWallInitialForestSavedLevelConstants j.val)
    (Bclock cK Cd Ci : ℝ) (hBc : 0 ≤ Bclock) (hcK : 0 < cK)
    (hCd : 0 ≤ Cd) (hCi : 0 ≤ Ci) :
    ∃Cr : ℝ,0 < Cr ∧ ∀{n : ℕ} {m delta cl cu Az C0 Ct D : ℝ}
      (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (as : List PositiveMass) (i star : ℕ) (saving eta Ccut : ℝ),0 ≤ Ccut →
      (1+actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0))*
        (nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)) ≤
          ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*M.data.d →
      actualHighWallInitialSavedTargetResponsePrice depth P Cd Ci saving eta Ccut cK M as i star ≤
        Cr*actualHighWallFractionalReaderModulus (2*(depth+2)) M.data.d
          (actualHighWallInitialSavedResponseRate M saving eta Ccut+M.data.d^2)
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)) := by
  obtain ⟨CA,CB,CF,CZ,hCA,hCB,hCF,hCZ,HCoeff⟩:=
    exists_actual_high_wall_initial_saved_uniform_coefficient_modulus depth P Bclock cK hBc hcK
  have hden : 0 < Real.exp (-4*Bclock)*cK:=by positivity
  obtain ⟨Cr,hCr,Hreader⟩:=exists_actual_general_target_response_common_modulus_constant depth
    (Real.exp (-4*Bclock)*cK) Cd CA CB CF CZ 1 2 Ci
    hden hCd hCA.le hCB.le hCF.le hCZ.le (by norm_num) (by norm_num) hCi
  refine ⟨Cr,hCr,?_⟩
  intro n m delta cl cu Az C0 Ct D M as i star saving eta Ccut hCcut Hstar
  let e:=actualHighWallInitialSavedResponseRate M saving eta Ccut
  let Di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let R:=actualHighWallInitialSavedRootBundle depth (Di/M.data.d)
  let J:=∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2)
  have he : 0 ≤ e:=actual_high_wall_initial_saved_response_rate_nonneg M saving eta Ccut hCcut
  have hDi : 0 ≤ Di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hf : 0 ≤ Di/M.data.d:=div_nonneg hDi M.data.hd.le
  have hR : 0 ≤ R:=by dsimp only [R,actualHighWallInitialSavedRootBundle];positivity
  have hNeta : 0 ≤ (n:ℝ)^(-eta):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hNm : 0 ≤ ((n+1:ℕ):ℝ)^(-m):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrho : 0 ≤ ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256)):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hstar : 0 ≤ ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32)):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpair : 0 ≤ ((n+1:ℕ):ℝ)^(-(actualSlowWindowExponent m delta/128)/2):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hterm : 0 ≤ ((n+1:ℕ):ℝ)^(-saving):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hJ : 0 ≤ J:=intervalIntegral.integral_nonneg (mul_nonneg hCcut M.data.hd.le) (fun _ _=>Real.sqrt_nonneg _)
  have hJdiv : 0 ≤ J/M.data.d^2:=div_nonneg hJ (sq_nonneg _)
  have hd3 : 0 ≤ M.data.d^3:=pow_nonneg M.data.hd.le _
  have Hnoise : (n:ℝ)^(-eta)+((n+1:ℕ):ℝ)^(-m)+
      ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))+M.data.d^3 ≤ e:=by
    dsimp only [e,actualHighWallInitialSavedResponseRate,J] at *
    linarith
  have HstarE : ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32)) ≤ e:=by
    dsimp only [e,actualHighWallInitialSavedResponseRate,J] at *
    linarith
  have HpairE : ((n+1:ℕ):ℝ)^(-(actualSlowWindowExponent m delta/128)/2) ≤ 1*e:=by
    dsimp only [e,actualHighWallInitialSavedResponseRate,J] at *
    linarith
  have HtermE : 2*((n+1:ℕ):ℝ)^(-saving) ≤ 2*e:=by
    dsimp only [e,actualHighWallInitialSavedResponseRate,J] at *
    linarith
  have HJE : J/M.data.d^2 ≤ e:=by
    dsimp only [e,actualHighWallInitialSavedResponseRate,J] at *
    linarith
  have Hthermal : J ≤ e*M.data.d:=by
    have H:=mul_le_mul_of_nonneg_right HJE (sq_nonneg M.data.d)
    have HJexact : J/M.data.d^2*M.data.d^2=J:=div_mul_cancel₀ J (pow_ne_zero 2 M.data.hd.ne')
    rw [HJexact] at H
    have Hd2 : M.data.d^2 ≤ M.data.d:=by nlinarith only [M.data.hd.le,M.data.hd1]
    exact H.trans (mul_le_mul_of_nonneg_left Hd2 he)
  have HC:=HCoeff M as i star eta Ccut e he Hnoise
    (Hstar.trans (mul_le_mul_of_nonneg_right HstarE M.data.hd.le)) Hthermal
  have H:=Hreader M.data.d R e M.data.hd hR he
    (fun j=>(P j).A eta cK M as i) (fun j=>(P j).B Ccut cK M as i star)
    (fun j=>(P j).F M) (fun j=>(P j).Cfr)
    (((n+1:ℕ):ℝ)^(-(actualSlowWindowExponent m delta/128)/2))
    (2*((n+1:ℕ):ℝ)^(-saving)) Ci
    (fun j=>(HC j).1) (fun j=>(HC j).2.1)
    (fun j=>(HC j).2.2.1) (fun j=>(HC j).2.2.2) HpairE HtermE le_rfl
  convert H using 1
  · rfl
  · dsimp only [actualHighWallFractionalReaderModulus,R,actualHighWallInitialSavedRootBundle,Di,e]
    ring

end OAI.SKFluctuations.Cavity

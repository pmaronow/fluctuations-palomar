module

public import ComparisonActualHighWallThetaZeroPositiveFloorThermal
public import ComparisonActualHighWallThetaZeroErrorTransport
public import ComparisonNativeActualHighMassDiameter
public import ComparisonConditionalErrorSize
public import ComparisonActualHighWallThetaZeroStrongStarCapRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem theta_zero_error_point_le_from_B
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {K : ℝ} (_hK : 0 ≤ K)
    (hB : ∀u∈Ioc (0:ℝ) 1,
      orderedPathB (n+1) Q.sweepBf Q.sweepHf u ≤ K*(Q.xs+u)^2)
    {u : ℝ} (hu : u∈Ioc (0:ℝ) 1) :
    Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤
      Q.lam*(K+(Az+1/cl)^2)*(Q.xs+u)^2 := by
  let S:=orderedPathS (n+1) Q.sweepBf Q.sweepHf u
  let B:=orderedPathB (n+1) Q.sweepBf Q.sweepHf u
  let R:=Q.sweepRadius u
  let Cr:=Az+1/cl
  let X:=Q.xs+u
  have hSK:=orderedPath_SK_bounds (n+1) Q.data.hn Q.sweepBf Q.sweepHf
    Q.sweep_bf_monotone Q.sweep_hf_monotone hu
  have hS : 0≤S:=hSK.1
  have hT : 0≤B-S^2:=sub_nonneg.mpr hSK.2.2.1
  have hR : 0≤R:=(Q.data.theta_zero_radius_bounds Q.alpha u).1
  have hX : 0≤X:=add_nonneg Q.hxs.le hu.1.le
  have hCr : 0≤Cr:=by dsimp [Cr];positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
  have hRup : R≤Cr*X:=Q.inverse_radius_le_source_mass hcl hAz ⟨hu.1.le,hu.2⟩
  have hR2 : R^2≤Cr^2*X^2:=by
    have HH:=pow_le_pow_left₀ hR hRup 2
    nlinarith only [HH]
  have hBup : B≤K*X^2:=hB u hu
  have hBr0 : 0≤(B-S^2)+(S-R)^2:=add_nonneg hT (sq_nonneg _)
  have hBr : (B-S^2)+(S-R)^2≤(K+Cr^2)*X^2:=by
    have hSR : 0≤S*R:=mul_nonneg hS hR
    nlinarith only [hBup,hR2,hSR]
  have hc:=Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u
  have Hcoef:=mul_le_mul_of_nonneg_right hc.2 hBr0
  have Hbr:=mul_le_mul_of_nonneg_left hBr Q.hlam.le
  change Q.sweepCoefficient u*((B-S^2)+(S-R)^2)≤Q.lam*(K+Cr^2)*X^2
  exact Hcoef.trans (by nlinarith only [Hbr])

theorem theta_zero_outer_coefficient_le
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ Q.data.N) (hnd : 1/Q.data.N ≤ Q.data.d)
    (hcu : 0 < cu) {lo u : ℝ} (houter : cu*Az*Q.xs < lo)
    (hlo : Q.data.s ≤ lo) (hu : u∈Ioc lo 1) :
    Q.sweepCoefficient u ≤
      (1+Real.log Q.data.N)*Q.data.d^3/(lo/cu) := by
  have hsu : Q.data.s ≤ u := hlo.trans hu.1.le
  have hr:=Q.shiftedNativeModel.R_bounds u
  have hspec:=Q.shiftedNativeModel.R_spec ⟨hsu,hu.2⟩
  have hRlo : lo/cu ≤ Q.sweepRadius u :=
    Q.actual_mass_slab_radius_lower hcu houter hr
      (by change lo≤Q.alpha.val.val (Q.shiftedNativeModel.R u)
          rw [hspec];exact hu.1.le)
  have hR0 : 0 < Q.sweepRadius u := Q.data.hrbounds.1.trans_le hr.1
  have hlo0 : 0 < lo := Q.data.hs.1.trans_le hlo
  have hrlo0 : 0 < lo/cu := div_pos hlo0 hcu
  have hlog : 0 ≤ Real.log Q.data.N := Real.log_nonneg hN
  have hA : 0 ≤ (1+Real.log Q.data.N)*Q.data.d^3 := by positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
  have He:=laplaceComparisonStrength_le_log_cubic hN Q.data.hd hnd
    Q.hlam Q.hld hR0 hr.2
  have Hden:=div_le_div_of_nonneg_left hA hrlo0 hRlo
  have hcoef : Q.sweepCoefficient u=
      laplaceComparisonStrength Q.data.d Q.lam (Q.sweepRadius u) := by
    simp [sweepCoefficient,omittedStrengthCoefficient,hsu]
  rw [hcoef]
  exact He.trans Hden

theorem theta_zero_outer_error_point_le_from_B
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ Q.data.N) (hnd : 1/Q.data.N ≤ Q.data.d)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {K lo u : ℝ} (_hK : 0 ≤ K)
    (hB : ∀u∈Ioc (0:ℝ) 1,
      orderedPathB (n+1) Q.sweepBf Q.sweepHf u ≤ K*(Q.xs+u)^2)
    (houter : cu*Az*Q.xs < lo) (hlo : Q.data.s ≤ lo)
    (hu : u∈Ioc lo 1) :
    Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤
      ((1+Real.log Q.data.N)*Q.data.d^3/(lo/cu))*
        (K+(Az+1/cl)^2)*(Q.xs+u)^2 := by
  let S:=orderedPathS (n+1) Q.sweepBf Q.sweepHf u
  let B:=orderedPathB (n+1) Q.sweepBf Q.sweepHf u
  let R:=Q.sweepRadius u
  let Cr:=Az+1/cl
  let X:=Q.xs+u
  have hu0 : u∈Ioc (0:ℝ) 1 := ⟨Q.data.hs.1.trans (hlo.trans_lt hu.1),hu.2⟩
  have hSK:=orderedPath_SK_bounds (n+1) Q.data.hn Q.sweepBf Q.sweepHf
    Q.sweep_bf_monotone Q.sweep_hf_monotone hu0
  have hS : 0≤S:=hSK.1
  have hR : 0≤R:=(Q.data.theta_zero_radius_bounds Q.alpha u).1
  have hRup : R≤Cr*X:=Q.inverse_radius_le_source_mass hcl hAz ⟨hu0.1.le,hu0.2⟩
  have hR2 : R^2≤Cr^2*X^2:=by
    have HH:=pow_le_pow_left₀ hR hRup 2
    nlinarith only [HH]
  have hBup : B≤K*X^2:=hB u hu0
  have hBr : (B-S^2)+(S-R)^2≤(K+Cr^2)*X^2:=by
    have hSR : 0≤S*R:=mul_nonneg hS hR
    nlinarith only [hBup,hR2,hSR]
  have hBr0 : 0≤(B-S^2)+(S-R)^2:=
    add_nonneg (sub_nonneg.mpr hSK.2.2.1) (sq_nonneg _)
  have hCoef:=theta_zero_outer_coefficient_le Q hN hnd hcu houter hlo hu
  have H1:=mul_le_mul_of_nonneg_right hCoef hBr0
  have hG : 0≤(1+Real.log Q.data.N)*Q.data.d^3/(lo/cu) := by
    have hlog : 0≤Real.log Q.data.N:=Real.log_nonneg hN
    have hlo0 : 0<lo:=Q.data.hs.1.trans_le hlo
    positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
  have H3:=mul_le_mul_of_nonneg_left hBr hG
  change Q.sweepCoefficient u*((B-S^2)+(S-R)^2)≤_
  simpa only [mul_assoc] using H1.trans H3

theorem positive_floor_outer_error_on_band
    (P : Q.Potential) (hN : 1 ≤ Q.data.N) (hnd : 1/Q.data.N ≤ Q.data.d)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {K lo hi : ℝ} (hK : 0 ≤ K)
    (hB : ∀u∈Ioc (0:ℝ) 1,
      orderedPathB (n+1) Q.sweepBf Q.sweepHf u ≤ K*(Q.xs+u)^2)
    (hlo : Q.data.s ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1)
    (houter : cu*Az*Q.xs < lo) :
    (∫u in lo..hi,P.positiveSet.indicator (fun _=>(1:ℝ))
      (Q.shiftedNativeModel.R u)*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      ((1+Real.log Q.data.N)*Q.data.d^3/(lo/cu))*
        (K+(Az+1/cl)^2)*(Q.xs+hi)^2*
          Q.data.N^delta*(comparisonSmallMass Q.data.N Q.data.E)^2/(lo/cu) := by
  let model:=Q.shiftedNativeModel
  let mask:=fun u=>P.positiveSet.indicator (fun _=>(1:ℝ)) (model.R u)
  let G:=(1+Real.log Q.data.N)*Q.data.d^3/(lo/cu)
  let C:=G*(K+(Az+1/cl)^2)*(Q.xs+hi)^2
  have hband : Icc lo hi⊆Icc (0:ℝ) 1 :=
    Icc_subset_Icc (Q.data.hs.1.le.trans hlo) hhi
  have hiE:IntervalIntegrable (fun u=>mask u*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u)
      volume lo hi :=
    (Q.error_mask_intervalIntegrable P.positiveSet P.positiveSet_measurable).mono_set (by
      rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
      exact hband)
  have hmaskMeas : Measurable mask :=
    (measurable_const.indicator P.positiveSet_measurable).comp model.R_continuous.measurable
  have hiMask : IntervalIntegrable mask volume lo hi := by
    have hfull : IntervalIntegrable mask volume 0 1 := by
      simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul
        hmaskMeas (show (0:ℝ) ≤ 1 from zero_le_one)
        (fun u _=>by dsimp [mask];by_cases h:model.R u∈P.positiveSet <;> simp [h])
        (intervalIntegrable_const (c:=(1:ℝ)))
    exact hfull.mono_set (by
      rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
      exact hband)
  have hmass:=P.positive_floor_mass_on_band hcu hlo hlohi hhi houter
  have hlo0 : 0<lo:=Q.data.hs.1.trans_le hlo
  have hG : 0≤G:=by
    have hlog : 0≤Real.log Q.data.N:=Real.log_nonneg hN
    dsimp [G]
    positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
  have hC : 0≤C:=by dsimp [C];positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
  have Hpoint:(∫u in lo..hi,mask u*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u)≤
      ∫u in lo..hi,C*mask u := by
    apply intervalIntegral.integral_mono_ae_restrict hlohi hiE (hiMask.const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne lo)] with u hu hune
    have huPos : u∈Ioc lo 1 := ⟨lt_of_le_of_ne hu.1 hune.symm,hu.2.trans hhi⟩
    have Hraw:=theta_zero_outer_error_point_le_from_B Q hN hnd hcl hcu hAz hK hB
      houter hlo huPos
    have hsq:=pow_le_pow_left₀ (by linarith [Q.hxs,hu.1] : 0≤Q.xs+u)
      (add_le_add_right hu.2 Q.xs) 2
    have hcoef : 0≤G*(K+(Az+1/cl)^2):=by dsimp [G];positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
    have Hcoef:=mul_le_mul_of_nonneg_left hsq hcoef
    have Herr:Q.data.thetaZeroErrorDensity Q.lam Q.alpha u≤C:=by
      exact Hraw.trans Hcoef
    have hmask0 : 0 ≤ mask u:=by
      dsimp [mask]
      by_cases hp:model.R u∈P.positiveSet <;> simp [hp]
    calc
      mask u*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤ mask u*C :=
        mul_le_mul_of_nonneg_left Herr hmask0
      _=C*mask u:=mul_comm _ _
  rw [intervalIntegral.integral_const_mul] at Hpoint
  have Hmass:=mul_le_mul_of_nonneg_left hmass hC
  have Hfinal:=Hpoint.trans Hmass
  change (∫u in lo..hi,mask u*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u)≤_
  convert Hfinal using 1
  dsimp only [C,G]
  ring

theorem positive_floor_mass_inner_interval (P : Q.Potential)
    {hi : ℝ} (hshi : Q.data.s ≤ hi) (hhi : hi ≤ 1) :
    (∫u in Q.data.s..hi,
      P.positiveSet.indicator (fun _=>(1:ℝ))
        (Q.shiftedNativeModel.R u)) ≤
      Q.data.N^(-delta)*comparisonSmallMass Q.data.N Q.data.E := by
  let mask := fun u=>P.positiveSet.indicator (fun _=>(1:ℝ))
    (Q.shiftedNativeModel.R u)
  have hmask : Measurable mask :=
    (measurable_const.indicator P.positiveSet_measurable).comp
      Q.shiftedNativeModel.R_continuous.measurable
  have hiMask : IntervalIntegrable mask volume Q.data.s 1 := by
    have hfull : IntervalIntegrable mask volume 0 1 := by
      simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul
        hmask (show (0:ℝ) ≤ 1 from zero_le_one)
        (fun u _=>by
          dsimp [mask]
          by_cases hp:Q.shiftedNativeModel.R u∈P.positiveSet <;> simp [hp])
        (intervalIntegrable_const (c:=(1:ℝ)))
    exact hfull.mono_set (by
      rw [uIcc_of_le Q.data.hs1,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc Q.data.hs.1.le le_rfl)
  have hiMaskSet : IntegrableOn mask (Icc Q.data.s 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Q.data.hs1).mp hiMask
  have hIccHi : (∫u in Q.data.s..hi,mask u) =
      ∫u in Icc Q.data.s hi,mask u := by
    rw [intervalIntegral.integral_of_le hshi,←integral_Icc_eq_integral_Ioc]
  have hIccOne : (∫u in Q.data.s..1,mask u) =
      ∫u in Icc Q.data.s 1,mask u := by
    rw [intervalIntegral.integral_of_le Q.data.hs1,
      ←integral_Icc_eq_integral_Ioc]
  have Hsub : (∫u in Q.data.s..hi,mask u) ≤
      ∫u in Q.data.s..1,mask u := by
    rw [hIccHi,hIccOne]
    apply setIntegral_mono_set hiMaskSet
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      dsimp [mask]
      by_cases hp:Q.shiftedNativeModel.R u∈P.positiveSet <;> simp [hp]
    · exact Eventually.of_forall (Icc_subset_Icc le_rfl hhi)
  exact Hsub.trans P.positive_floor_mass_global

theorem positive_floor_inner_error_on_carrier
    (P : Q.Potential) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {K C hi : ℝ} (hK : 0 ≤ K) (_hC : 0 ≤ C)
    (hB : ∀u∈Ioc (0:ℝ) 1,
      orderedPathB (n+1) Q.sweepBf Q.sweepHf u ≤ K*(Q.xs+u)^2)
    (hcarrier : Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam)
    (hshi : Q.data.s ≤ hi) (hhi : hi ≤ 1)
    (hinner : hi ≤ C*Q.xs) :
    (∫u in Q.data.s..hi,
      P.positiveSet.indicator (fun _=>(1:ℝ))
        (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      (K+(Az+1/cl)^2)*(1+C)^2*Q.data.N^delta*Q.data.E := by
  let mask := fun u=>P.positiveSet.indicator (fun _=>(1:ℝ))
    (Q.shiftedNativeModel.R u)
  let Cprice := Q.lam*(K+(Az+1/cl)^2)*((1+C)*Q.xs)^2
  have hband : Icc Q.data.s hi ⊆ Icc (0:ℝ) 1 :=
    Icc_subset_Icc Q.data.hs.1.le hhi
  have hiE :=
    (Q.error_mask_intervalIntegrable P.positiveSet P.positiveSet_measurable).mono_set
      (by rw [uIcc_of_le hshi,uIcc_of_le zero_le_one]; exact hband)
  have hmask : Measurable mask :=
    (measurable_const.indicator P.positiveSet_measurable).comp
      Q.shiftedNativeModel.R_continuous.measurable
  have hiMask : IntervalIntegrable mask volume Q.data.s hi := by
    have hfull : IntervalIntegrable mask volume 0 1 := by
      simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul
        hmask (show (0:ℝ) ≤ 1 from zero_le_one)
        (fun u _=>by
          dsimp [mask]
          by_cases hp:Q.shiftedNativeModel.R u∈P.positiveSet <;> simp [hp])
        (intervalIntegrable_const (c:=(1:ℝ)))
    exact hfull.mono_set (by
      rw [uIcc_of_le hshi,uIcc_of_le zero_le_one]
      exact hband)
  have hCprice : 0 ≤ Cprice := by dsimp [Cprice]; positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
  have hmass := positive_floor_mass_inner_interval P hshi hhi
  have Hpoint : (∫u in Q.data.s..hi,
      mask u*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      ∫u in Q.data.s..hi,Cprice*mask u := by
    apply intervalIntegral.integral_mono_ae_restrict hshi hiE
      (hiMask.const_mul Cprice)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u huint
    have hu0 : u∈Ioc (0:ℝ) 1 :=
      ⟨Q.data.hs.1.trans_le huint.1,huint.2.trans hhi⟩
    have Hraw := theta_zero_error_point_le_from_B Q hcl hAz hK hB hu0
    have hsum0 : 0 ≤ Q.xs+u := by linarith [Q.hxs,hu0.1]
    have hsum : Q.xs+u ≤ (1+C)*Q.xs := by
      nlinarith only [huint.2,hinner]
    have hsq := pow_le_pow_left₀ hsum0 hsum 2
    have hcoef : 0 ≤ Q.lam*(K+(Az+1/cl)^2) := by positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
    have Hcoef := mul_le_mul_of_nonneg_left hsq hcoef
    have Herr : Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤ Cprice := by
      dsimp only [Cprice]
      nlinarith only [Hraw,Hcoef]
    have hmask0 : 0 ≤ mask u := by
      dsimp [mask]
      by_cases hp:Q.shiftedNativeModel.R u∈P.positiveSet <;> simp [hp]
    calc
      mask u*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤ mask u*Cprice :=
        mul_le_mul_of_nonneg_left Herr hmask0
      _ = Cprice*mask u := mul_comm _ _
  rw [intervalIntegral.integral_const_mul] at Hpoint
  have Hmass := mul_le_mul_of_nonneg_left hmass hCprice
  have Hbound := Hpoint.trans Hmass
  have hcarrierCost : Q.lam*Q.xs^2*Q.data.N^(-delta)*
      comparisonSmallMass Q.data.N Q.data.E =
      Q.data.N^delta*Q.data.E := by
    rw [hcarrier]
    exact comparison_conditional_floor_mass_cost Q.data.hN Q.data.hE Q.hlam
  change (∫u in Q.data.s..hi,
      mask u*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤ _
  calc
    _ ≤ Cprice*(Q.data.N^(-delta)*
          comparisonSmallMass Q.data.N Q.data.E) := Hbound
    _ = (K+(Az+1/cl)^2)*(1+C)^2*
          (Q.lam*Q.xs^2*Q.data.N^(-delta)*
            comparisonSmallMass Q.data.N Q.data.E) := by
      dsimp only [Cprice]
      ring
    _ = (K+(Az+1/cl)^2)*(1+C)^2*Q.data.N^delta*Q.data.E := by
      rw [hcarrierCost]
      ring

theorem eq7_outer_floor_band_shape
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b lo hi : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hcu : 0 < cu)
    (hlo : Q.data.s ≤ lo) (hlohi : lo ≤ hi)
    (hloBand : a*Q.xs ≤ lo) (hhiBand : hi ≤ b*lo) :
    (Q.xs+hi)^2 ≤ (cu*(1/a+b))^2*(lo/cu)^2 := by
  have hlo0 : 0 < lo := Q.data.hs.1.trans_le hlo
  have hsum0 : 0 ≤ Q.xs+hi := by linarith [Q.hxs,hlohi]
  have hxlo : Q.xs ≤ lo/a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hloBand)
  have hsum : Q.xs+hi ≤ (1/a+b)*lo := by
    calc
      Q.xs+hi ≤ lo/a+b*lo := add_le_add hxlo hhiBand
      _ = (1/a+b)*lo := by ring
  have Hsq := pow_le_pow_left₀ hsum0 hsum 2
  calc
    (Q.xs+hi)^2 ≤ ((1/a+b)*lo)^2 := Hsq
    _ = (cu*(1/a+b))^2*(lo/cu)^2 := by
      field_simp [hcu.ne']

theorem eq7_outer_positive_floor_error_rate
    (P : Q.Potential)
    (hN : 1 ≤ Q.data.N) (hnd : 1/Q.data.N ≤ Q.data.d)
    (hC0 : 0 < C0) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {K a b lo hi : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (hb : 0 ≤ b)
    (hB : ∀u∈Ioc (0:ℝ) 1,
      orderedPathB (n+1) Q.sweepBf Q.sweepHf u ≤ K*(Q.xs+u)^2)
    (hlo : Q.data.s ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1)
    (houter : cu*Az*Q.xs < lo)
    (hloBand : a*Q.xs ≤ lo) (hhiBand : hi ≤ b*lo) :
    (∫u in lo..hi,P.positiveSet.indicator (fun _=>(1:ℝ))
      (Q.shiftedNativeModel.R u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      (cu*(1/a+b))^2*(K+(Az+1/cl)^2)*
        (1+Real.log Q.data.N)*Q.data.N^delta*
          (C0^3*Q.data.N^(-3*m)*Q.data.E) := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  let R := lo/cu
  let J := (cu*(1/a+b))^2
  let coeff := (K+(Az+1/cl)^2)*(1+Real.log Q.data.N)*Q.data.N^delta
  have hR : 0 < R := div_pos (Q.data.hs.1.trans_le hlo) hcu
  have hJ : 0 ≤ J := sq_nonneg _
  have hcoeff : 0 ≤ coeff := by
    have hlog : 0 ≤ Real.log Q.data.N := Real.log_nonneg hN
    dsimp [coeff]
    positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
  have hDU : 0 ≤ Q.data.d^3*U^2 := by positivity [Q.hlam.le, Q.data.hd.le, Q.data.hE.le, Q.data.hN.le]
  have Hgeom := eq7_outer_floor_band_shape Q ha hb hcu
    hlo hlohi hloBand hhiBand
  have Hratio : (Q.xs+hi)^2/R^2 ≤ J := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    exact Hgeom
  have Hphysical := positive_floor_outer_error_on_band P hN hnd
    hcl hcu hAz hK hB hlo hlohi hhi houter
  have Hcrit : Q.data.d^3*U^2 ≤
      C0^3*Q.data.N^(-3*m)*Q.data.E := by
    have H := mul_le_mul_of_nonneg_right
      (Q.original_critical_energy_ratio hC0) Q.data.hE.le
    convert H using 1
    dsimp only [U,comparisonSmallMass]
    field_simp [Q.data.hN.ne',Q.data.hE.ne']
  have HgeomScaled := mul_le_mul_of_nonneg_left Hratio
    (mul_nonneg hcoeff hDU)
  have HcritScaled := mul_le_mul_of_nonneg_left Hcrit
    (mul_nonneg hcoeff hJ)
  calc
    (∫u in lo..hi,P.positiveSet.indicator (fun _=>(1:ℝ))
      (Q.shiftedNativeModel.R u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
        ((1+Real.log Q.data.N)*Q.data.d^3/R)*
          (K+(Az+1/cl)^2)*(Q.xs+hi)^2*Q.data.N^delta*U^2/R :=
      Hphysical
    _ = (coeff*(Q.data.d^3*U^2))*((Q.xs+hi)^2/R^2) := by
      dsimp only [coeff]
      field_simp [hR.ne']
    _ ≤ (coeff*(Q.data.d^3*U^2))*J := HgeomScaled
    _ = (coeff*J)*(Q.data.d^3*U^2) := by ring
    _ ≤ (coeff*J)*(C0^3*Q.data.N^(-3*m)*Q.data.E) :=
      HcritScaled
    _ = (cu*(1/a+b))^2*(K+(Az+1/cl)^2)*
          (1+Real.log Q.data.N)*Q.data.N^delta*
            (C0^3*Q.data.N^(-3*m)*Q.data.E) := by
      dsimp only [coeff,J]
      ring

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7

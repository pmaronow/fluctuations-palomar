module

public import ComparisonActualHighOnlyConditionalOuterOrdinaryPrice
public import ComparisonActualHighOnlyOrdinaryLocalMassBudget
public import ComparisonActualHighOnlyConditionalErrorTransport
public import ComparisonActualHighOnlyOuterComparableDensity

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.retained_mask_mass_le_high_only
    (P : a.Potential) (ι : Type*) [Fintype ι] (c : ι→ShiftedCapInterval a P)
    {ag zg V : ℝ} (hag : 0 ≤ ag) (hags : ag < zg) (hzg : zg ≤ 1)
    (hwidth : a.alpha.val.val zg-a.alpha.val.val ag ≤ V) :
    (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>(1:ℝ)) (a.R u)) ≤ V := by
  let S := P.retainedSupport c ag zg
  have hS : MeasurableSet S := P.retainedSupport_measurable c hag hzg
  have hsub : S⊆Ioo ag zg := inter_subset_left
  have hsub1 : S⊆Ioo (0:ℝ) 1 := hsub.trans (Ioo_subset_Ioo hag hzg)
  rw [a.radius_mask_mass_above_zero S hS hsub1]
  have hac : AbsolutelyContinuousOnInterval a.alpha.val.val ag zg := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hags.le] using
      (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property).mono (Icc_subset_Icc hag hzg)
  have hi : IntegrableOn (deriv a.alpha.val.val) (Ioo ag zg) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hags.le).mp hac.intervalIntegrable_deriv
  have H : (∫r in S,deriv a.alpha.val.val r) ≤ ∫r in Ioo ag zg,deriv a.alpha.val.val r := by
    apply setIntegral_mono_set hi
    · exact ae_of_all _ (fun _=>a.alpha.val.property.2.deriv_nonneg)
    · exact Eventually.of_forall fun r hr=>hsub hr
  rw [a.inverse_slice_mass hag hags.le hzg] at H
  exact H.trans hwidth

theorem Potential.retained_error_from_cap_width_high_only
    (P : a.Potential) (ι : Type*) [Fintype ι] (c : ι→ShiftedCapInterval a P)
    {ag zg V diameter : ℝ} (hag : 0 ≤ ag) (hags : ag < zg) (hzg : zg ≤ 1)
    (hwidth : a.alpha.val.val zg-a.alpha.val.val ag ≤ V)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hcap : ∀t,(c t).right-(c t).left ≤ diameter) :
    (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u) ≤
      3*laplaceComparisonStrength a.data.d a.lam ag*
        (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>1) (a.R u)*a.shiftedNativeModel.thermal u)+
      16*laplaceComparisonStrength a.data.d a.lam ag*diameter^2*V := by
  let S := P.retainedSupport c ag zg
  let mask := fun u=>S.indicator (fun _=>(1:ℝ)) (a.R u)
  let T := a.shiftedNativeModel.thermal
  let gs := laplaceComparisonStrength a.data.d a.lam ag
  have hMismatchRadius : ∀ᵐr,r∈Icc (0:ℝ) 1 → r∈S →
      (a.radiusS r-r)^2 ≤ 16*diameter^2+2*a.radiusThermal r := by
    filter_upwards [P.hzero,volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hr hrS
    rcases hrS.2 with hcapS|hcontact
    · obtain ⟨t,ht⟩ := hcapS
      have H := P.cap_point_squared_mismatch (c t).hleft (c t).hright ht (hcontacts t).1
        (hcontacts t).2 ((c t).negative _ ht)
      have Hsq := pow_le_pow_left₀ (sub_nonneg.mpr (c t).hlt.le) (hcap t) 2
      change (a.radiusS r-r)^2 ≤ 16*((c t).right-(c t).left)^2+2*a.radiusThermal r at H
      nlinarith only [H,Hsq]
    · have H := (hrzero hr hcontact).2.2
      change (a.radiusS r-r)^2 ≤ a.radiusThermal r at H
      have HT := a.radiusThermal_nonneg hr
      nlinarith only [H,HT,sq_nonneg diameter]
  have hMismatch := ae_inverse_pullback
    (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property)
    (fun u (_ : u∈Icc a.data.s 1)=>omittedSweepQuantile_bounds zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
      a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha u)
    (fun u hu=>omittedSweepQuantile_spec zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
      a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha hu) hMismatchRadius
  have hMismatchMass : ∀ᵐu,u∈Icc a.data.s 1 → a.R u∈S →
      (orderedPathS (n+1) a.bf a.hf u-a.R u)^2 ≤ 16*diameter^2+2*T u := by
    filter_upwards [hMismatch] with u hu hui hsupport
    have H := hu hui hsupport
    simpa only [radiusS,radiusB,radiusThermal,omittedSweepQuantile_spec zero_le_one
      ⟨a.data.hs.1,a.data.hs1⟩ a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha hui,T,ShiftedNativeBandModel.thermal] using H
  have hS : MeasurableSet S := P.retainedSupport_measurable c hag hzg
  have hmask : Measurable mask := (measurable_const.indicator hS).comp a.shiftedNativeModel.R_continuous.measurable
  have hiMask : IntervalIntegrable mask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hmask zero_le_one
      (fun u _=>by by_cases h:a.R u∈S <;> simp [mask,h]) (intervalIntegrable_const (c:=(1:ℝ)))
  have hiT := a.shiftedNativeModel.thermal_mask_integrable S hS
  have hiE := a.error_mask_intervalIntegrable S hS
  have hgs : 0 < gs := laplaceComparisonStrength_pos a.data.d a.hlam _
  have hpoint : ∀ᵐu∂volume.restrict (Icc (0:ℝ) 1),
      mask u*a.comparisonErrorDensity u ≤ 3*gs*(mask u*T u)+(16*gs*diameter^2)*mask u := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hMismatchMass] with u hu hMismatchU
    by_cases hsupport : a.R u∈S
    · have hr : a.R u∈Ioo ag zg := hsupport.1
      have hhigh : a.data.s < u := a.radius_high_mass (hag.trans_lt hr.1)
      have hui : u∈Icc a.data.s 1 := ⟨hhigh.le,hu.2⟩
      have H := hMismatchU hui hsupport
      have hT0 : 0 ≤ T u := a.actual_thermal_nonneg_on_unit hu
      have hcoef : a.coefficient u ≤ gs := by
        change omittedStrengthCoefficient a.data.d a.data.s a.R a.lam u ≤ gs
        rw [omittedStrengthCoefficient,ite_eq_left hui.1]
        exact (laplaceComparisonStrength_monotonicities a.data.hd.ne' a.hlam (r₀:=0) le_rfl).1
          ⟨hag,hags.le.trans hzg⟩ (a.shiftedNativeModel.R_bounds u) hr.1.le
      have H1 := mul_le_mul_of_nonneg_left H (a.coefficient_nonneg u)
      have H2 := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 3*T u+16*diameter^2 by positivity)
      simp only [mask,indicator_of_mem hsupport,one_mul,mul_one]
      dsimp only [comparisonErrorDensity,T,ShiftedNativeBandModel.thermal] at H H1 H2 ⊢
      nlinarith only [H1,H2]
    · simp only [mask,indicator_of_notMem hsupport,zero_mul,mul_zero,add_zero,le_refl]
  have H := intervalIntegral.integral_mono_ae_restrict zero_le_one hiE
    ((hiT.const_mul (3*gs)).add (hiMask.const_mul (16*gs*diameter^2))) hpoint
  rw [intervalIntegral.integral_add (hiT.const_mul _) (hiMask.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at H
  have HM := mul_le_mul_of_nonneg_left (P.retained_mask_mass_le_high_only ι c hag hags hzg hwidth)
    (show 0 ≤ 16*gs*diameter^2 by positivity)
  simp_rw [a.shiftedNativeModel_radius] at H
  exact H.trans (add_le_add le_rfl HM)

end ActualHighOnlyOverlapMinimum
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_conditional_outer_ordinary_error_high_only
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (horder : (delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn : ℕ in atTop,∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs → a.data.d ≤ 1 →
      a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam → a.xs+1 ≤ a.data.N →
      ∀P : a.Potential,NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      ∀F : Finset (ordConnectedSection P.negativeSet),∀A : Set ℝ,∀v : ℝ,
        0 < v → v ≤ 1 → a.data.U ≤ v → a.data.s < v/2 → a.xs ≤ v → 4*cu*Az*a.xs ≤ v →
      (∫u in 0..1,(P.canonicalOrdinarySupport F A v).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u) ≤
        a.data.N^(4*delta)*a.data.E := by
  classical
  obtain ⟨Q,hQ,Hsource⟩ := eventually_actual_high_only_local_ordinary_mass_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hprice := eventually_actual_conditional_outer_ordinary_price_high_only (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    ell hell Q hQ hm hdelta hcl hcu hAz hC0 horder
  have Hlog := (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  have Hscalar := eventually_actual_minimum_physical_scalar_data_high_only (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  filter_upwards [Hsource,Hprice,Hlog,Hscalar] with n hnSource hnPrice hnLog hnScalar
  intro a hs0 hsxs hd1 hxs hyN P hclock F A v hv hv1 hUv hs hvxs houter
  have hN : 1 ≤ a.data.N := by exact_mod_cast Nat.succ_pos n
  have hlog : 1 ≤ Real.log a.data.N := by simpa only [Function.comp_apply] using hnLog
  have hnd := (hnScalar a hd1).2.2.1
  let c := P.ordinaryCapFamily (P.capFamily F) A 16 v
  letI : Fintype (P.OrdinaryCapIndex (P.capFamily F) A 16 v) := Fintype.ofFinite _
  let ag := a.R (v/2)
  let zg := a.R (min (16*v) 1)
  have hgeom := P.ordinary_group_geometry (P.capFamily F) A (by norm_num : (1:ℝ) ≤ 16) hv hv1 hs
  dsimp only at hgeom
  obtain ⟨hag,hzg,hagz,hagmass,hzgmass,hcap⟩ := hgeom
  change a.alpha.val.val ag=v/2 at hagmass
  change a.alpha.val.val zg=min (16*v) 1 at hzgmass
  have hagzStrict : ag < zg := by
    by_contra hh
    have HH:=a.alpha.val.property.2 (le_of_not_gt hh)
    rw [hagmass,hzgmass] at HH
    have Hmin : v/2 < min (16*v) 1 := lt_min (by linarith) (by linarith)
    exact (not_le.mpr Hmin) HH
  have hcontacts := P.ordinary_group_contacts (P.capFamily F) A (K:=16) (show a.data.s < v by linarith) (P.capFamily_contacts F)
  have hcapWidth : ∀t,(c t).right-(c t).left ≤ a.canonicalLocalMassDiameter v := by
    intro t
    let q := v/2+a.data.U
    have hq : 0 < q := by dsimp [q];have hU:=a.data.hU;positivity
    have hleft : q ≤ a.alpha.val.val (c t).left+a.data.U := by
      have H := t.property.2.1
      change v ≤ a.alpha.val.val (c t).left at H
      dsimp [q]
      linarith
    have hspan : a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ 32*q := by
      have H := (hcap t).2.2.2
      change a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ 16*v at H
      dsimp [q]
      have hU:=a.data.hU
      linarith
    have H := (c t).local_radius_travel hq hleft hspan
    have H0 : 0 ≤ 32*a.data.E/(a.data.N^delta*a.data.d^3*q) := by
      have HE:=a.data.hE;have HD:=a.data.hd;have HN:=a.data.hN;positivity
    have HH := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 9*Real.log a.data.N by linarith) H0
    apply H.trans
    dsimp only [canonicalLocalMassDiameter,q] at HH ⊢
    convert HH using 1 <;> ring
  have hwidth : a.alpha.val.val zg-a.alpha.val.val ag ≤ 16*v := by
    rw [hagmass,hzgmass]
    linarith [min_le_left (16*v) 1]
  have HE := P.retained_error_from_cap_width_high_only _ c hag.le hagzStrict hzg hwidth hcontacts hcapWidth
  have HT := hnSource a hs0 hsxs P hclock F A v (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) hv hv1 hs
    (by linarith) (Real.rpow_pos_of_pos a.data.hN _) (comparison_physical_cutoff_log (C:=10) a.data.hN).2.le
  have HP := hnPrice a hd1 hxs hyN v hv hv1 hUv hs hvxs houter
  have HH := mul_le_mul_of_nonneg_left HT
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (laplaceComparisonStrength_pos a.data.d a.hlam ag).le)
  exact HE.trans ((add_le_add HH le_rfl).trans HP)

end OAI.SKFluctuations.LaplaceWindowFormalization

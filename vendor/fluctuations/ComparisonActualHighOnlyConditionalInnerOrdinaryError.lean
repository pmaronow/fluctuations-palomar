module

public import ComparisonActualHighOnlyOrdinaryMassBudget
public import ComparisonActualHighOnlyConditionalErrorTransport
public import ComparisonActualHighOnlyConditionalOrdinaryPrice
public import ComparisonActualHighOnlyOuterComparableDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 20000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.retained_inner_mask_mass_le_high_only
    (P : a.Potential) (ι:Type*) [Fintype ι] (c:ι→ShiftedCapInterval a P)
    {ag zg bound:ℝ} (hag:0 ≤ ag) (hzg:0 < zg) (hzg1:zg ≤ 1) (hαzg:a.alpha.val.val zg ≤ bound) :
    (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>(1:ℝ)) (a.R u)) ≤ bound := by
  let S:=P.retainedSupport c ag zg
  have hS:MeasurableSet S:=P.retainedSupport_measurable c hag hzg1
  have hsub:S⊆Ioo (0:ℝ) zg:=fun r hr=>⟨hag.trans_lt hr.1.1,hr.1.2⟩
  have hsub1:S⊆Ioo (0:ℝ) 1:=hsub.trans (Ioo_subset_Ioo le_rfl hzg1)
  rw [a.radius_mask_mass_above_zero S hS hsub1]
  have hac:AbsolutelyContinuousOnInterval a.alpha.val.val 0 zg:=by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hzg.le] using
      (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property).mono
        (Icc_subset_Icc le_rfl hzg1)
  have hi:IntegrableOn (deriv a.alpha.val.val) (Ioo (0:ℝ) zg):=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hzg.le).mp hac.intervalIntegrable_deriv
  have H: (∫r in S,deriv a.alpha.val.val r) ≤ ∫r in Ioo (0:ℝ) zg,deriv a.alpha.val.val r:=by
    apply setIntegral_mono_set hi
    · exact ae_of_all _ (fun _=>a.alpha.val.property.2.deriv_nonneg)
    · exact Eventually.of_forall fun r hr=>hsub hr
  rw [a.inverse_slice_mass le_rfl hzg.le hzg1] at H
  rw [a.alpha.property.1] at H
  exact H.trans (by linarith [a.data.hs.1])

theorem Potential.retained_inner_error_le_thermal_high_only
    (P:a.Potential) (ι:Type*) [Fintype ι] (c:ι→ShiftedCapInterval a P)
    {ag zg bound:ℝ} (hag:0 ≤ ag) (hzg:0 < zg) (hzg1:zg ≤ 1) (hαzg:a.alpha.val.val zg ≤ bound) :
    (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u) ≤
      3*a.lam*(∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>1)
        (a.R u)*a.shiftedNativeModel.thermal u)+16*a.lam*a.cavityCapTravel^2*(bound) := by
  let S:=P.retainedSupport c ag zg
  let mask:=fun u=>S.indicator (fun _=>(1:ℝ)) (a.R u)
  let T:=a.shiftedNativeModel.thermal
  have hS:MeasurableSet S:=P.retainedSupport_measurable c hag hzg1
  have hmask:Measurable mask:=(measurable_const.indicator hS).comp a.shiftedNativeModel.R_continuous.measurable
  have hiMask:IntervalIntegrable mask volume 0 1:=by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hmask zero_le_one
      (fun u _=>by by_cases h:a.R u∈S <;> simp [mask,h]) (intervalIntegrable_const (c:=(1:ℝ)))
  have hiT:=a.shiftedNativeModel.thermal_mask_integrable S hS
  have hiE:=a.error_mask_intervalIntegrable S hS
  have hpoint:∀ᵐu∂volume.restrict (Icc (0:ℝ) 1),
      mask u*a.comparisonErrorDensity u ≤ 3*a.lam*(mask u*T u)+(16*a.lam*a.cavityCapTravel^2)*mask u:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae P.all_nonpositive_squared_mismatch_ae_high_mass] with u hu hMismatch
    by_cases hsupport:a.R u∈S
    · have hr:a.R u∈Ioo (0:ℝ) zg:=⟨hag.trans_lt hsupport.1.1,hsupport.1.2⟩
      have hhigh:a.data.s < u:=a.radius_high_mass hr.1
      have hui:u∈Icc a.data.s 1:=⟨hhigh.le,hu.2⟩
      have hnonpos:P.H (a.R u) ≤ 0:=by
        rcases hsupport.2 with hcap|hcontact
        · obtain ⟨t,ht⟩:=hcap
          exact ((c t).negative _ ht).le
        · exact hcontact.le
      have H:=hMismatch hui hnonpos
      have hT0:0 ≤ T u:=a.actual_thermal_nonneg_on_unit hu
      have H1:=mul_le_mul_of_nonneg_left H (a.coefficient_nonneg u)
      have H2:=mul_le_mul_of_nonneg_right (a.coefficient_le_lam u)
        (show 0 ≤ 3*T u+16*a.cavityCapTravel^2 by positivity)
      simp only [mask,indicator_of_mem hsupport,one_mul,mul_one]
      dsimp only [comparisonErrorDensity] at *
      change (orderedPathS (n+1) a.bf a.hf u-a.R u)^2 ≤ 16*a.cavityCapTravel^2+2*T u at H
      change a.coefficient u*(orderedPathS (n+1) a.bf a.hf u-a.R u)^2 ≤
        a.coefficient u*(16*a.cavityCapTravel^2+2*T u) at H1
      have H3:=mul_le_mul_of_nonneg_right (a.coefficient_le_lam u) hT0
      dsimp only [T,ShiftedNativeBandModel.thermal] at H H1 H2 H3 ⊢
      nlinarith only [H1,H2,H3]
    · simp only [mask,indicator_of_notMem hsupport,zero_mul,mul_zero,add_zero,le_refl]
  have H:=intervalIntegral.integral_mono_ae_restrict zero_le_one hiE
    ((hiT.const_mul (3*a.lam)).add (hiMask.const_mul (16*a.lam*a.cavityCapTravel^2))) hpoint
  rw [intervalIntegral.integral_add (hiT.const_mul _) (hiMask.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at H
  have HM:=mul_le_mul_of_nonneg_left (P.retained_inner_mask_mass_le_high_only ι c hag hzg hzg1 hαzg)
    (show 0 ≤ 16*a.lam*a.cavityCapTravel^2 by have hl:=a.hlam;positivity)
  simp_rw [a.shiftedNativeModel_radius] at H
  exact H.trans (add_le_add le_rfl HM)

end ActualHighOnlyOverlapMinimum
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_conditional_inner_ordinary_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock Cv:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hCv:0 ≤ Cv) (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential),
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      ∀(F:Finset (ordConnectedSection P.negativeSet)) (A:Set ℝ) (v:ℝ),
      0 < v → v ≤ 1 → a.data.s < v/2 → a.data.U ≤ v → v ≤ Cv*a.xs →
      (∫u in 0..1,(P.canonicalOrdinarySupport F A v).indicator (fun _=>1)
        (a.R u)*a.comparisonErrorDensity u) ≤ a.data.N^(7*delta)*a.data.E := by
  obtain ⟨Q,hQ,HS⟩:=eventually_actual_high_only_ordinary_mass_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have HP:=eventually_actual_conditional_ordinary_budget_price_high_only (cu:=cu) (D:=D) (Bclock:=Bclock) (Ct:=Ct)
    ell hell Q Cv hQ hCv hm hdelta hcl hAz hC0 horder
  have Hlog:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  filter_upwards [HS,HP,Hlog] with n hnS hnP hnLog
  intro a hs hsxs hd1 hxs hy P hclock F A v hv hv1 hstart hUv hvA
  have hlog:1 ≤ Real.log a.data.N:=by simpa only [Function.comp_apply] using hnLog
  let c:=P.ordinaryCapFamily (P.capFamily F) A 16 v
  let ag:=a.shiftedNativeModel.R (v/2)
  let zg:=a.shiftedNativeModel.R (min (16*v) 1)
  have HG:=P.ordinary_group_geometry (P.capFamily F) A (by norm_num : (1:ℝ) ≤ 16) hv hv1 hstart
  dsimp only at HG
  obtain ⟨hag,hzg,hagz,hagmass,hzgmass,hcap⟩:=HG
  have hzg0:0 < zg:=hag.trans_le hagz
  have HE:=P.retained_inner_error_le_thermal_high_only _ c hag.le hzg0 hzg
    (hzgmass.le.trans (min_le_left _ _))
  change (∫u in 0..1,(P.canonicalOrdinarySupport F A v).indicator (fun _=>1) (a.R u)*
    a.comparisonErrorDensity u) ≤ 3*a.lam*(∫u in 0..1,(P.canonicalOrdinarySupport F A v).indicator
      (fun _=>1) (a.R u)*a.shiftedNativeModel.thermal u)+16*a.lam*a.cavityCapTravel^2*(16*v) at HE
  have HT:=hnS a hs hsxs P hclock F A v (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) hv hv1 hstart
    (by linarith only [hlog]) (Real.rpow_pos_of_pos a.data.hN _) (comparison_physical_cutoff_log (C:=10) a.data.hN).2.le
  simp_rw [a.shiftedNativeModel_radius] at HT
  have hD:a.cavityCapTravel ≤ a.canonicalMassDiameter:=by
    unfold canonicalMassDiameter
    have H:=mul_nonneg (show 0 ≤ 9*Real.log a.data.N-1 by linarith only [hlog]) a.cavityCapTravel_nonneg
    nlinarith only [H]
  have HM:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ a.cavityCapTravel_nonneg hD 2) (show 0 ≤ 16*a.lam by have hl:=a.hlam;positivity))
    (show 0 ≤ 16*v by positivity)
  have HL:=mul_le_mul_of_nonneg_left HT (show 0 ≤ 3*a.lam by have hl:=a.hlam;positivity)
  exact HE.trans ((add_le_add HL HM).trans (hnP a hd1 hxs hy v hv hv1 hUv hvA))

end OAI.SKFluctuations.LaplaceWindowFormalization

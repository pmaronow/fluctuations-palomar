module

public import ComparisonActualHighOnlyConditionalWallDoubleOrdinaryLimit
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
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.wall_double_retained_mask_mass_le_high_only
    (P : a.Potential) (ι:Type*) [Fintype ι] (c:ι→ShiftedCapInterval a P)
    {zg:ℝ} (hzg:0 < zg) (hzg1:zg ≤ 1) (hαzg:a.alpha.val.val zg ≤ 32*a.data.s) :
    (∫u in 0..1,(P.retainedSupport c 0 zg).indicator (fun _=>(1:ℝ)) (a.R u)) ≤ 32*a.data.s := by
  let S:=P.retainedSupport c 0 zg
  have hS:MeasurableSet S:=P.retainedSupport_measurable c le_rfl hzg1
  have hsub:S⊆Ioo (0:ℝ) zg:=inter_subset_left
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

theorem Potential.wall_double_retained_error_le_thermal_high_only
    (P:a.Potential) (ι:Type*) [Fintype ι] (c:ι→ShiftedCapInterval a P)
    {zg:ℝ} (hzg:0 < zg) (hzg1:zg ≤ 1) (hαzg:a.alpha.val.val zg ≤ 32*a.data.s) :
    (∫u in 0..1,(P.retainedSupport c 0 zg).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u) ≤
      3*a.lam*(∫u in 0..1,(P.retainedSupport c 0 zg).indicator (fun _=>1)
        (a.R u)*a.shiftedNativeModel.thermal u)+16*a.lam*a.cavityCapTravel^2*(32*a.data.s) := by
  let S:=P.retainedSupport c 0 zg
  let mask:=fun u=>S.indicator (fun _=>(1:ℝ)) (a.R u)
  let T:=a.shiftedNativeModel.thermal
  have hS:MeasurableSet S:=P.retainedSupport_measurable c le_rfl hzg1
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
    · have hr:a.R u∈Ioo (0:ℝ) zg:=hsupport.1
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
  have HM:=mul_le_mul_of_nonneg_left (P.wall_double_retained_mask_mass_le_high_only ι c hzg hzg1 hαzg)
    (show 0 ≤ 16*a.lam*a.cavityCapTravel^2 by have hl:=a.hlam;positivity)
  simp_rw [a.shiftedNativeModel_radius] at H
  exact H.trans (add_le_add le_rfl HM)

end ActualHighOnlyOverlapMinimum
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_conditional_wall_double_ordinary_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs) (hUs:a.data.U ≤ a.data.s),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential) (ι:Type*) [Fintype ι] (c:ι→ShiftedCapInterval a P),
      (∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right) →
      (∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1)) →
      Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)) →
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      (∀t,0 < (c t).left) → (∀t,a.alpha.val.val (c t).right ≤ min (32*a.data.s) 1) →
      (∫u in 0..1,(P.retainedSupport c 0 (a.R (min (32*a.data.s) 1))).indicator (fun _=>1)
        (a.R u)*a.comparisonErrorDensity u) ≤ a.data.N^(7*delta)*a.data.E := by
  obtain ⟨Q,hQ,Hsource⟩:=eventually_actual_high_only_wall_double_ordinary_complete_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hprice:=eventually_actual_conditional_ordinary_budget_price_high_only (cu:=cu) (D:=D) (Bclock:=Bclock) (Ct:=Ct)
    ell hell Q 2 hQ (by norm_num) hm hdelta hcl hAz hC0 horder
  have Hlog:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  filter_upwards [Hsource,Hprice,Hlog] with n hnSource hnPrice hnLog
  intro a hs hsxs hUs hd1 hxs hy P ι inst c hwhole hcontacts hdisjoint hclock hleftpos hright
  have hlog:1 ≤ Real.log a.data.N:=by simpa only [Function.comp_apply] using hnLog
  have hspos:0 < a.data.s:=a.data.hU.trans_le hUs
  let zg:=a.R (min (32*a.data.s) 1)
  have hmass:min (32*a.data.s) 1∈Icc a.data.s 1:=⟨le_min (by linarith) a.data.hs1,min_le_right _ _⟩
  have hzg:0 < zg:=by
    dsimp only [zg]
    by_contra H
    have Hz:a.R (min (32*a.data.s) 1)=0:=le_antisymm (le_of_not_gt H)
      (a.shiftedNativeModel.R_bounds _).1
    have HH:=a.shiftedNativeModel.R_spec hmass
    change a.alpha.val.val (a.R (min (32*a.data.s) 1))=min (32*a.data.s) 1 at HH
    rw [Hz,a.alpha.property.1] at HH
    have Hgt:a.data.s < min (32*a.data.s) 1:=lt_min (by linarith) (by linarith)
    exact Hgt.ne HH
  have hzg1:zg ≤ 1:=(a.shiftedNativeModel.R_bounds _).2
  have hαzg:a.alpha.val.val zg ≤ 32*a.data.s:=
    (a.shiftedNativeModel.R_spec hmass).le.trans (min_le_left _ _)
  have HE:=P.wall_double_retained_error_le_thermal_high_only ι c hzg hzg1 hαzg
  have HT:=hnSource a hs hsxs hspos P ι c hwhole hcontacts hdisjoint hclock hleftpos hright
    (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) (by linarith) (Real.rpow_pos_of_pos a.data.hN _)
    (comparison_physical_cutoff_log (C:=10) a.data.hN).2.le
  have HP:=hnPrice a hd1 hxs hy (2*a.data.s) (by positivity) (by linarith only [hs]) (by linarith only [hUs,hspos]) (by linarith only [hsxs])
  have hD:a.cavityCapTravel ≤ a.canonicalMassDiameter:=by
    unfold canonicalMassDiameter
    have H:=mul_nonneg (show 0 ≤ 9*Real.log a.data.N-1 by linarith only [hlog]) a.cavityCapTravel_nonneg
    nlinarith only [H]
  have HM:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ a.cavityCapTravel_nonneg hD 2) (show 0 ≤ 16*a.lam by have hl:=a.hlam;positivity))
    (show 0 ≤ 32*a.data.s by positivity)
  have HL:=mul_le_mul_of_nonneg_left HT (show 0 ≤ 3*a.lam by have hl:=a.hlam;positivity)
  apply HE.trans
  exact (add_le_add HL HM).trans (by simpa only [show 16*(2*a.data.s)=32*a.data.s by ring] using HP)

end OAI.SKFluctuations.LaplaceWindowFormalization

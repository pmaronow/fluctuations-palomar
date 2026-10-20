module

public import ComparisonActualHighOnlyConditionalOuterBroadPrice
public import ComparisonActualHighOnlyOuterComparableBroadMassBudget
public import ComparisonActualHighOnlyConditionalErrorTransport
public import ComparisonActualHighOnlyOuterComparableDensity

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.outer_cap_left_positive_high_only (P:a.Potential) (cap:ShiftedCapInterval a P)
    (hcu:0 < cu) (hAz:0 ≤ Az) (htravel:a.cavityCapTravel ≤ a.xs)
    (houter:2*cu*(Az+1)*a.xs ≤ a.alpha.val.val cap.right) : 0 < cap.left := by
  have hzr:a.z ≤ cap.right := by
    by_contra hh
    have H:=a.alpha.val.property.2 (le_of_not_ge hh)
    have Hreg:=(a.regular a.z ⟨le_rfl,a.hz.2⟩).2
    change a.alpha.val.val a.z ≤ cu*a.z at Hreg
    have Hxs:=mul_le_mul_of_nonneg_left a.hzxs hcu.le
    have Hpos:=mul_pos hcu a.hxs
    have HA:=mul_nonneg (mul_nonneg hcu.le hAz) a.hxs.le
    nlinarith only [H,Hreg,Hxs,Hpos,houter,HA]
  have Hreg:=(a.regular cap.right ⟨hzr,cap.hright⟩).2
  change a.alpha.val.val cap.right ≤ cu*cap.right at Hreg
  have Hright:2*(Az+1)*a.xs ≤ cap.right := by
    have HH : cu*(2*(Az+1)*a.xs) ≤ cu*cap.right := by nlinarith only [Hreg,houter]
    exact le_of_mul_le_mul_left HH hcu
  have Hwidth:=((P.cap_interval_travel cap.hleft cap.hlt.le cap.hright cap.negative).2.1).trans htravel
  have Hazxs:=mul_nonneg hAz a.hxs.le
  nlinarith only [Hright,Hwidth,Hazxs,a.hxs]

theorem Potential.outer_cap_mass_error_le_thermal_high_only
    (P:a.Potential) (cap:ShiftedCapInterval a P) {l z v diameter:ℝ}
    (hl:cap.left ≤ l) (hl0:0 < l) (hlz:l < z) (hz:z ≤ cap.right)
    (hv:0 < v) (hv1:v ≤ 1) (hs:a.data.s < v/2)
    (hmass:v/2 ≤ a.alpha.val.val l)
    (hcontacts:P.H cap.left=0 ∧ (P.H cap.right=0 ∨ cap.right=1))
    (hdiam:cap.right-cap.left ≤ diameter) :
    (∫u in a.alpha.val.val l..a.alpha.val.val z,a.comparisonErrorDensity u) ≤
      3*laplaceComparisonStrength a.data.d a.lam (a.R (v/2))*
        (∫u in a.alpha.val.val l..a.alpha.val.val z,a.shiftedNativeModel.thermal u)+
      16*laplaceComparisonStrength a.data.d a.lam (a.R (v/2))*diameter^2*
        (a.alpha.val.val z-a.alpha.val.val l) := by
  have hz1:z ≤ 1:=hz.trans cap.hright
  have hl1:l ≤ 1:=hlz.le.trans hz1
  have hαl:=a.alpha.val.property.1 l
  have hαz:=a.alpha.val.property.1 z
  have hle:=a.alpha.val.property.2 hlz.le
  have hsα:a.data.s ≤ a.alpha.val.val l:=hs.le.trans hmass
  have hI:Icc (a.alpha.val.val l) (a.alpha.val.val z)⊆Icc (0:ℝ) 1:=Icc_subset_Icc hαl.1 hαz.2
  have hiE:=a.comparisonErrorDensity_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hle,uIcc_of_le zero_le_one];exact hI)
  have hiT:IntervalIntegrable a.shiftedNativeModel.thermal volume (a.alpha.val.val l) (a.alpha.val.val z):=
    (physicalOrderedThermal_intervalIntegrable n a.bf a.hf a.bf_monotone a.hf_monotone).mono_set
      (by rw [uIcc_of_le hle,uIcc_of_le zero_le_one];exact hI)
  let gs:=laplaceComparisonStrength a.data.d a.lam (a.R (v/2))
  have hgs:0 < gs:=laplaceComparisonStrength_pos a.data.d a.hlam _
  have Hpoint:∀ᵐu∂volume.restrict (Icc (a.alpha.val.val l) (a.alpha.val.val z)),
      a.comparisonErrorDensity u ≤ 3*gs*a.shiftedNativeModel.thermal u+16*gs*diameter^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (a.alpha.val.val l)),
      ae_restrict_of_ae (volume.ae_ne (a.alpha.val.val z))] with u hu hlu hzu
    have hui:u∈Icc a.data.s 1:=⟨hsα.trans hu.1,hu.2.trans hαz.2⟩
    have hr:a.R u∈Ioo cap.left cap.right:=by
      have H:=a.shiftedNativeModel.massSlice_quantile_mem ⟨hsα,hαl.2⟩ ⟨hsα.trans hle,hαz.2⟩ (hI hu)
      have HH:=H.mpr ⟨lt_of_le_of_ne hu.1 hlu.symm,lt_of_le_of_ne hu.2 hzu⟩
      dsimp only [ShiftedNativeBandModel.massSlice] at HH
      rw [a.shiftedNativeModel.R_inverse ⟨hl0.le,hl1⟩,a.shiftedNativeModel.R_inverse ⟨hl0.le.trans hlz.le,hz1⟩] at HH
      exact ⟨hl.trans_lt HH.1,HH.2.trans_le hz⟩
    have H:=P.cap_point_squared_mismatch cap.hleft cap.hright hr hcontacts.1 hcontacts.2 (cap.negative _ hr)
    have Hspec:=a.shiftedNativeModel.R_spec hui
    change a.alpha.val.val (a.R u)=u at Hspec
    change (a.radiusS (a.R u)-a.R u)^2 ≤ 16*(cap.right-cap.left)^2+2*a.radiusThermal (a.R u) at H
    simp only [radiusS,radiusThermal,radiusB,Hspec] at H
    have Hsq:=pow_le_pow_left₀ (sub_nonneg.mpr cap.hlt.le) hdiam 2
    have hcoef:a.coefficient u ≤ gs := by
      change omittedStrengthCoefficient a.data.d a.data.s a.R a.lam u ≤ gs
      rw [omittedStrengthCoefficient,ite_eq_left hui.1]
      have Hmono:=a.shiftedNativeModel.R_monotone (hmass.trans hu.1)
      exact (laplaceComparisonStrength_monotonicities a.data.hd.ne' a.hlam (r₀:=0) le_rfl).1
        (a.shiftedNativeModel.R_bounds _) (a.shiftedNativeModel.R_bounds _) Hmono
    have hT:=a.actual_thermal_nonneg_on_unit (hI hu)
    have H1:=mul_le_mul_of_nonneg_left H (a.coefficient_nonneg u)
    have H2:=mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ 3*a.shiftedNativeModel.thermal u+16*diameter^2 by positivity)
    have H3:=mul_le_mul_of_nonneg_left Hsq (show 0 ≤ 16*a.coefficient u by have HC:=a.coefficient_nonneg u;positivity)
    dsimp only [comparisonErrorDensity,ShiftedNativeBandModel.thermal] at H1 H2 ⊢
    nlinarith only [H1,H2,H3]
  have H:=intervalIntegral.integral_mono_ae_restrict hle hiE ((hiT.const_mul (3*gs)).add intervalIntegrable_const) Hpoint
  rw [intervalIntegral.integral_add (hiT.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at H
  simpa only [gs,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using H

end ActualHighOnlyOverlapMinimum
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_conditional_outer_broad_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs0:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam → a.xs+1 ≤ a.data.N →
      ∀(P:a.Potential) (cap:ShiftedCapInterval a P) (l z v:ℝ),
      (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1) →
      a.cavityCapTravel ≤ a.xs → 2*cu*(Az+1)*a.xs ≤ a.alpha.val.val cap.right →
      0 < l → l < z → cap.left ≤ l → z ≤ cap.right →
      0 < v → v ≤ 1 → a.data.s < v/2 → a.data.U ≤ v →
      a.xs ≤ v → 4*cu*Az*a.xs ≤ v →
      v/2 ≤ a.alpha.val.val l → a.alpha.val.val z ≤ min (4*v) 1 →
      v ≤ a.alpha.val.val z-a.alpha.val.val l →
      (∫u in a.alpha.val.val l..a.alpha.val.val z,a.comparisonErrorDensity u) ≤ a.data.N^(4*delta)*a.data.E := by
  obtain ⟨Q,hQ,HS⟩:=eventually_actual_high_only_outer_comparable_broad_mass_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have HP:=eventually_actual_conditional_outer_broad_price_high_only (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    ell hell Q hQ hm hdelta hcl hcu hAz hC0 horder
  have Hcut:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (comparison_log_loss_eventually (C:=8) (p:=0) (by norm_num) (by norm_num : (0:ℝ) < 9))
  have Hlog:=(tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  filter_upwards [HS,HP,Hcut,Hlog,eventually_actual_minimum_physical_scalar_data_high_only hm hC0]
    with n hnS hnP hnCut hnLog hnScalar
  intro a hs0 hsxs hd1 hxs hy P cap l z v hcontacts htravel houter hl0 hlz hclL hzcap hv hv1 hs hUv hvxs houterv hRho hupper hwidth
  have hlog:1 ≤ Real.log a.data.N:=by simpa only [Function.comp_apply] using hnLog
  have hscalar:=hnScalar a hd1
  have hαl:=a.alpha.val.property.1 l
  have hαz:=a.alpha.val.property.1 z
  have hm:=a.inverse_slice_mass hl0.le hlz.le (hzcap.trans cap.hright)
  have hcutU:2*a.data.N^(-(10:ℝ)) < a.data.U:=by
    have HH:8 ≤ a.data.N^(9:ℝ):=by simpa only [Function.comp_apply,Real.rpow_zero,mul_one] using hnCut
    have HM:=mul_le_mul_of_nonneg_right HH (Real.rpow_nonneg a.data.hN.le (-(10:ℝ)))
    have He:a.data.N^(9:ℝ)*a.data.N^(-(10:ℝ))=1/a.data.N:=by
      rw [←Real.rpow_add a.data.hN]
      norm_num only [show (9:ℝ)+-(10:ℝ)= -1 by norm_num,Real.rpow_neg_one]
      simp only [one_div]
    rw [He] at HM
    have Hpos:=Real.rpow_pos_of_pos a.data.hN (-(10:ℝ))
    exact lt_of_lt_of_le (by linarith only [HM,Hpos]) hscalar.2.2.2.1
  have HT:=hnS a hs0 hsxs P cap l z v (10*Real.log a.data.N) (a.data.N^(-(10:ℝ)))
    hcontacts htravel houter hl0 hlz hclL hzcap hv hv1 hs hUv hRho hupper (by rw [hm];exact hwidth)
    (by linarith) (Real.rpow_pos_of_pos a.data.hN _) hcutU (comparison_physical_cutoff_log (C:=10) a.data.hN).2.le
  have hsα:a.data.s ≤ a.alpha.val.val l:=hs.le.trans hRho
  have hsub:=a.shiftedNativeModel.mass_radius_cell_substitution a.shiftedNativeModel.thermal
    (show a.alpha.val.val l∈Icc a.data.s 1 from ⟨hsα,hαl.2⟩)
    (show a.alpha.val.val z∈Icc a.data.s 1 from ⟨hsα.trans (a.alpha.val.property.2 hlz.le),hαz.2⟩)
    (a.alpha.val.property.2 hlz.le)
  rw [a.shiftedNativeModel.R_inverse ⟨hl0.le,hlz.le.trans (hzcap.trans cap.hright)⟩,
    a.shiftedNativeModel.R_inverse ⟨hl0.le.trans hlz.le,hzcap.trans cap.hright⟩,integral_Icc_eq_integral_Ioo] at hsub
  rw [←hsub,hm] at HT
  have hleftContact:P.H cap.left=0:=hcontacts.1.resolve_right (ne_of_gt (P.outer_cap_left_positive_high_only cap hcu hAz htravel houter))
  have hvB:v ≤ a.alpha.val.val cap.right:=by
    have H:=a.alpha.val.property.2 hzcap
    linarith
  have hAmax:a.alpha.val.val cap.left ≤ 4*v:=
    ((a.alpha.val.property.2 hclL).trans (a.alpha.val.property.2 hlz.le)).trans (hupper.trans (min_le_left _ _))
  have Hlocal:=cap.outer_local_radius_travel hcl hcu hAz htravel houter hv hvB hAmax
  have Hglobal:cap.right-cap.left ≤ a.cavityCapTravel:=(P.cap_interval_travel cap.hleft cap.hlt.le cap.hright cap.negative).2.1
  have HD:cap.right-cap.left ≤ a.canonicalOuterBroadMassDiameter v:=by
    have Hmin:=le_min Hglobal Hlocal
    have H0:0 ≤ min a.cavityCapTravel ((32*cu^3/cl^3)*a.data.E/(a.data.N^delta*a.data.d^3*v)):=by
      have HL:=a.cavityCapTravel_nonneg;have HE:=a.data.hE;have HN:=a.data.hN;have HD:=a.data.hd;positivity
    have Hmul:=mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 9*Real.log a.data.N by linarith) H0
    exact Hmin.trans (by unfold canonicalOuterBroadMassDiameter;simpa only [one_mul] using Hmul)
  have HE:=P.outer_cap_mass_error_le_thermal_high_only cap hclL hl0 hlz hzcap hv hv1 hs hRho ⟨hleftContact,hcontacts.2⟩ HD
  have HL:=mul_le_mul_of_nonneg_left HT (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (laplaceComparisonStrength_pos a.data.d a.hlam (a.R (v/2))).le)
  have HC:=hnP a hd1 hxs hy v hv hv1 hUv hs hvxs houterv htravel (a.alpha.val.val z-a.alpha.val.val l)
    (sub_nonneg.mpr (a.alpha.val.property.2 hlz.le)) (by linarith only [hupper.trans (min_le_left _ _),hαl.1]) (by linarith only [hαz.2,hαl.1])
  exact HE.trans ((add_le_add HL le_rfl).trans HC)

end OAI.SKFluctuations.LaplaceWindowFormalization

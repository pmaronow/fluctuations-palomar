module

public import ComparisonActualHighWallThetaZeroEq7RegularFamilyPhysicalTailDraft
public import ComparisonActualHighWallThetaZeroRegularScaleCarrier
public import ComparisonOriginalQEq7DeterministicErrorCoreDraft
public import ComparisonActualHighWallThetaZeroEq7QuantitativePrefixCorrected

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.MacroInnerFamilyProbe
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable

theorem eventually_macro_inner_family
    (Bclock C eps : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hC : 2 ≤ C) (heps : 0 < eps) :
    ∃ ell : ℕ, 2 < ell ∧ (14+3*delta)/((ell:ℝ)-1) ≤ eps ∧
      ∃ qLow qPost qBroad : ℝ,
        1 ≤ qLow ∧ 1 ≤ qPost ∧ 1 ≤ qBroad ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ (Q : ActualThetaZeroOverlapMinimum
              (n+1) m delta cl cu Az C0 Ct D Bclock) (P : Q.Potential),
            Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam →
            Q.data.N^(-(10:ℝ)) ≤ Q.lam → 1 ≤ Q.xs →
            ∀ F : Finset (ordConnectedSection P.negativeSet),
              Q.lam*(∑ p : Eq7InnerCoverPiece (P.capFamily F) 1,
                eq7InnerThermalPiece (P.capFamily F) 1 p) ≤
              OriginalQEq7RegularFamilyRateDraft.familyConstant
                delta cl Az D C qLow qPost qBroad*
                (Real.log Q.data.N)^6*Q.data.N^(2*delta+eps)*Q.data.E := by
  obtain ⟨ell, hell, horder, qLow, qPost, qBroad, hqLow, hqPost, hqBroad, H⟩ :=
    eventually_eq7_inner_regular_family_from_physical_draft Bclock C eps
      hm hdelta hroom hcl hcu hAz hC0 hCt hC heps
  refine ⟨ell, hell, horder, qLow, qPost, qBroad, hqLow, hqPost, hqBroad, ?_⟩
  filter_upwards [H] with n hn Q P hcarrier hlamFloor hmacro
  have hC1 : 1 ≤ C := by linarith only [hC]
  have hgate : 1 ≤ C*Q.xs := by
    calc
      1 ≤ Q.xs := hmacro
      _ ≤ C*Q.xs := by nlinarith only [hC1, Q.hxs]
  exact hn Q P 1 hcarrier hlamFloor le_rfl hgate

theorem macro_base_carrier
    {n : ℕ} {m delta C0 D Bclock : ℝ}
    (a : ActualHighWallData (n+1) delta)
    (lam : ℝ) (hlam : 0 < lam) (hld : lam ≤ a.d^2) (alpha : a.Profile)
    (hminimum : ∀ beta : a.Profile,
      (a.thetaZeroShiftedParentData lam hlam hld).objective alpha ≤
        (a.thetaZeroShiftedParentData lam hlam hld).objective beta)
    (hdelta : 0 ≤ delta)
    (hmacro : 1 ≤ comparisonConditionalScale a.N delta a.E lam)
    (hdD : a.d ≤ D) (hupper : Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower : a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E)
    (hclock : a.T ≤ Bclock) :
    ∃ Q : ActualThetaZeroOverlapMinimum (n+1) m delta 1 1 2 C0 1 D Bclock,
      Q.data = a ∧ Q.lam = lam ∧ HEq Q.alpha alpha ∧
      Q.xs = comparisonConditionalScale a.N delta a.E lam ∧ Q.z = 1 := by
  let A := comparisonConditionalScale a.N delta a.E lam
  have hmin : min (2*A) 1 = 1 := min_eq_right (by dsimp [A]; linarith)
  have hregular : ∀ r ∈ Icc (min (2*A) 1) 1,
      (1:ℝ)*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ (1:ℝ)*r := by
    intro r hr
    rw [hmin] at hr
    have hr1 : r = 1 := le_antisymm hr.2 hr.1
    subst r
    simp only [one_mul, alpha.property.2.1, le_refl, and_self]
  obtain ⟨Q, hdata, hlamQ, halpha, hxs, hz⟩ :=
    a.theta_zero_regular_scale_carrier (m:=m) (cl:=1) (cu:=1)
      (Az:=2) (C0:=C0) (Ct:=1) (D:=D) (Bclock:=Bclock)
      lam hlam hld alpha hminimum hdelta
      (a.hs1.trans hmacro) (a.hr.trans hmacro) hdD hupper hlower
      hclock (by norm_num) (by norm_num) hregular
  exact ⟨Q, hdata, hlamQ, halpha, hxs, hz.trans hmin⟩

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem macro_full_floor_le_of_pointwise
    (P : Q.Potential) {K : ℝ} (hK : 0 ≤ K)
    (hcarrier : Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam)
    (hmacro : 1 ≤ Q.xs)
    (hpoint : ∀ u ∈ Ioc (0:ℝ) 1,
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤ Q.lam*K*(Q.xs+u)^2) :
    (∫ u in Q.data.s..1,
      P.positiveSet.indicator (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      4*K*Q.data.N^delta*Q.data.E := by
  have hlam0 : 0 ≤ Q.lam := Q.hlam.le
  let mask := fun u => P.positiveSet.indicator (fun _ => (1:ℝ))
    (Q.shiftedNativeModel.R u)
  let C := 4*Q.lam*K*Q.xs^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmeas : Measurable mask :=
    (measurable_const.indicator P.positiveSet_measurable).comp
      Q.shiftedNativeModel.R_continuous.measurable
  have himask : IntervalIntegrable mask volume Q.data.s 1 := by
    have H : IntervalIntegrable mask volume 0 1 := by
      simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hmeas
        zero_le_one (fun u _ => by
          dsimp [mask]
          by_cases hp : Q.shiftedNativeModel.R u ∈ P.positiveSet <;> simp [hp])
        (intervalIntegrable_const (c:=(1:ℝ)))
    exact H.mono_set (by
      rw [uIcc_of_le Q.data.hs1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc Q.data.hs.1.le le_rfl)
  have hierror := (Q.error_mask_intervalIntegrable
    P.positiveSet P.positiveSet_measurable).mono_set (by
      rw [uIcc_of_le Q.data.hs1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc Q.data.hs.1.le le_rfl)
  have H : (∫ u in Q.data.s..1, mask u*
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      ∫ u in Q.data.s..1, C*mask u := by
    apply intervalIntegral.integral_mono_ae_restrict Q.data.hs1 hierror
      (himask.const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hu0 : u ∈ Ioc (0:ℝ) 1 := ⟨Q.data.hs.1.trans_le hu.1, hu.2⟩
    have hsq := pow_le_pow_left₀ (add_pos Q.hxs hu0.1).le
      (show Q.xs+u ≤ 2*Q.xs by linarith only [hu.2, hmacro]) 2
    have hp : Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤ C := by
      have HH := mul_le_mul_of_nonneg_left hsq (mul_nonneg Q.hlam.le hK)
      dsimp only [C]
      nlinarith only [hpoint u hu0, HH]
    have hm0 : 0 ≤ mask u := indicator_nonneg (fun _ _ => zero_le_one) _
    exact (mul_le_mul_of_nonneg_left hp hm0).trans_eq (mul_comm _ _)
  rw [intervalIntegral.integral_const_mul] at H
  have Hmass := mul_le_mul_of_nonneg_left (P.positive_floor_mass_global) hC
  have hcal : Q.lam*Q.xs^2*Q.data.N^(-delta)*
      comparisonSmallMass Q.data.N Q.data.E = Q.data.N^delta*Q.data.E := by
    rw [hcarrier]
    exact comparison_conditional_floor_mass_cost Q.data.hN Q.data.hE Q.hlam
  calc
    _ ≤ C*(Q.data.N^(-delta)*comparisonSmallMass Q.data.N Q.data.E) :=
      H.trans Hmass
    _ = 4*K*(Q.lam*Q.xs^2*Q.data.N^(-delta)*
        comparisonSmallMass Q.data.N Q.data.E) := by dsimp [C]; ring
    _ = _ := by rw [hcal]; ring

theorem macro_radius_width_le
    (hdelta : 0 ≤ delta) (hlog : 1 ≤ Real.log Q.data.N)
    (hUfloor : Q.data.N^(-(1:ℝ)) ≤ comparisonSmallMass Q.data.N Q.data.E)
    (hcarrier : Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam)
    (hmacro : 1 ≤ Q.xs) :
    16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*(1-Q.eq7InnerPrefixEnd) ≤
      144*(Real.log Q.data.N)^2*Q.data.N^(2*delta)*Q.data.E := by
  have hlam0 : 0 ≤ Q.lam := Q.hlam.le
  let U := comparisonSmallMass Q.data.N Q.data.E
  let L := Real.log Q.data.N
  have hU : 0 < U := Q.data.hU
  have hU1 : U ≤ 1 := Q.data.hsmall.trans Q.data.hd1
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hNU : 1 ≤ Q.data.N*U := by
    rw [Real.rpow_neg Q.data.hN.le, Real.rpow_one, ←one_div] at hUfloor
    have H := (div_le_iff₀ Q.data.hN).mp hUfloor
    nlinarith only [H]
  have hratio : (1+U)/U ≤ 2*Q.data.N :=
    (div_le_iff₀ hU).mpr (by nlinarith only [hNU, hU1])
  have hrlog0 : 0 ≤ Real.log ((1+U)/U) :=
    Real.log_nonneg ((one_le_div hU).mpr (by linarith))
  have hrlog : Real.log ((1+U)/U) ≤ 2*L := by
    have H := Real.log_le_log (by positivity : 0 < (1+U)/U) hratio
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) Q.data.hN.ne'] at H
    have H2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    dsimp only [L]
    linarith only [H, H2, hlog]
  have hpow : 1 ≤ Q.data.N^delta := Real.one_le_rpow hN hdelta
  have hquot : comparisonConstraintLength Q.data.N Q.data.E Q.data.d /
      Q.data.N^delta ≤ U := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos Q.data.hN delta)).mpr
    have H := mul_le_mul_of_nonneg_left hpow hU.le
    exact (min_le_left _ _).trans (by simpa only [mul_one] using H)
  have htravel : Q.cavityCapTravel ≤ U*(2*L) := by
    unfold cavityCapTravel
    exact mul_le_mul hquot hrlog hrlog0 hU.le
  have hR0 : 0 ≤ Q.data.rmin+Q.cavityCapTravel :=
    add_nonneg Q.data.hrbounds.1.le Q.cavityCapTravel_nonneg
  have hR : Q.data.rmin+Q.cavityCapTravel ≤ 3*U*L := by
    have H := mul_le_mul_of_nonneg_left hlog hU.le
    have hr := Q.radius_le_smallMass
    dsimp only [U, L] at *
    nlinarith only [htravel, hr, H]
  have hRsq : (Q.data.rmin+Q.cavityCapTravel)^2 ≤ 9*U^2*L^2 := by
    have H := pow_le_pow_left₀ hR0 hR 2
    nlinarith only [H]
  have hcal : Q.lam*Q.xs^2*U = Q.data.N^(2*delta)*Q.data.E := by
    rw [hcarrier]
    exact comparison_conditional_small_mass_cost Q.data.hN Q.data.hE Q.hlam
  have hxs2 : 1 ≤ Q.xs^2 := by nlinarith only [hmacro]
  have hcost : Q.lam*U^2 ≤ Q.data.N^(2*delta)*Q.data.E := by
    have H := mul_le_mul_of_nonneg_right (hU1.trans hxs2) hU.le
    have HH := mul_le_mul_of_nonneg_left H Q.hlam.le
    nlinarith only [HH, hcal]
  have hz0 : 0 ≤ Q.eq7InnerPrefixEnd :=
    Q.data.hs.1.le.trans Q.eq7_inner_s_le_prefix_end
  have hw : 0 ≤ 1-Q.eq7InnerPrefixEnd ∧ 1-Q.eq7InnerPrefixEnd ≤ 1 := by
    constructor <;> linarith only [hz0, Q.eq7_inner_prefix_end_le_one]
  calc
    _ ≤ 16*Q.lam*(9*U^2*L^2)*(1-Q.eq7InnerPrefixEnd) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRsq (by positivity)) hw.1
    _ ≤ 16*Q.lam*(9*U^2*L^2) := by
      exact mul_le_of_le_one_right (by positivity) hw.2
    _ = 144*L^2*(Q.lam*U^2) := by ring
    _ ≤ _ := by
      have H := mul_le_mul_of_nonneg_left hcost (by positivity : 0 ≤ 144*L^2)
      simpa only [L, mul_assoc] using H

theorem macro_density_of_parts
    (P : Q.Potential) {B Prefix Floor Radius Target : ℝ}
    (hfinite : ∀ F : Finset (ordConnectedSection P.negativeSet),
      Q.lam*(∑ p : Eq7InnerCoverPiece (P.capFamily F) 1,
        eq7InnerThermalPiece (P.capFamily F) 1 p) ≤ B)
    (hprefix : (∫ u in (0:ℝ)..Q.eq7InnerPrefixEnd,
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤ Prefix)
    (hfloor : (∫ u in Q.data.s..1,
      P.positiveSet.indicator (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤ Floor)
    (hradius : 16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*
      (1-Q.eq7InnerPrefixEnd) ≤ Radius)
    (hbudget : Prefix+3*B+Radius+Floor ≤ Target) :
    Q.data.thetaZeroOriginalSweepDensity Q.lam Q.alpha ≤ Target := by
  have hT := P.eq7_inner_post_weighted_thermal_of_finite_piece_prices_draft
    Q.eq7_inner_prefix_end_le_one le_rfl hfinite
  have hSlice := Q.shiftedNativeModel.massSlice_thermal_mask_integral
    ⟨Q.eq7_inner_s_le_prefix_end, Q.eq7_inner_prefix_end_le_one⟩
    ⟨Q.data.hs1, le_rfl⟩ Q.eq7_inner_prefix_end_le_one
    (P.negativeSet ∪ P.contactSet)
    (P.negativeSet_open.measurableSet.union P.contactSet_measurable)
  rw [hSlice] at hT
  have hError := P.eq7_inner_error_le_thermal_full_floor_core
    Q.eq7_inner_s_le_prefix_end Q.eq7_inner_prefix_end_le_one le_rfl
  have hz0 : 0 ≤ Q.eq7InnerPrefixEnd :=
    Q.data.hs.1.le.trans Q.eq7_inner_s_le_prefix_end
  have hi0 := Q.error_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hz0, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl Q.eq7_inner_prefix_end_le_one)
  have hi1 := Q.error_intervalIntegrable.mono_set (by
    rw [uIcc_of_le Q.eq7_inner_prefix_end_le_one, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hz0 le_rfl)
  have Hadd := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  rw [Q.data.theta_zero_density_eq_error_integral]
  linarith only [hT, hError, Hadd, hprefix, hfloor, hradius, hbudget]

private theorem eventually_rate_quarter (C a b : ℝ) (p : ℕ)
    (hC : 0 ≤ C) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, ∀ E : ℝ, 0 ≤ E →
      C*(Real.log ((n+1:ℕ):ℝ))^p*((n+1:ℕ):ℝ)^a*E ≤
        (1/4:ℝ)*((n+1:ℕ):ℝ)^b*E := by
  have HN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have H := HN.eventually (comparison_log_loss_eventually
    (C:=4*C) (p:=(p:ℝ)) (eps:=b-a) (by positivity) (sub_pos.mpr hab))
  filter_upwards [H] with n hn E hE
  rw [Real.rpow_natCast] at hn
  have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
  have HH := mul_le_mul_of_nonneg_right hn
    (mul_nonneg (Real.rpow_pos_of_pos hN a).le hE)
  have heq : ((n+1:ℕ):ℝ)^(b-a)*((n+1:ℕ):ℝ)^a = ((n+1:ℕ):ℝ)^b := by
    rw [←Real.rpow_add hN, sub_add_cancel]
  rw [←mul_assoc (((n+1:ℕ):ℝ)^(b-a)) (((n+1:ℕ):ℝ)^a) E, heq] at HH
  nlinarith only [HH]

theorem eventually_macro_density
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam →
        Q.data.N^(-(10:ℝ)) ≤ Q.lam → 1 ≤ Q.xs →
        Q.data.thetaZeroOriginalSweepDensity Q.lam Q.alpha ≤
          Q.data.N^(10*delta)*Q.data.E := by
  obtain ⟨ell, _, _, qLow, qPost, qBroad, _, _, _, Hfamily⟩ :=
    eventually_macro_inner_family Bclock 2 delta
      hm hdelta hroom hcl hcu hAz hC0 hCt (by norm_num) hdelta
  let Kfamily := max 1 (OriginalQEq7RegularFamilyRateDraft.familyConstant
    delta cl Az D 2 qLow qPost qBroad)
  have hKfamily : 0 ≤ Kfamily := zero_le_one.trans (le_max_left _ _)
  obtain ⟨Kprefix, hKprefix, Hprefix⟩ :=
    eventually_theta_zero_eq7_unified_prefix_quantitative_corrected_draft
      hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Kpoint, hKpoint, Hpoint⟩ := eventually_theta_zero_near_zero_point
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Kfloor := 4*(Kpoint+(Az+1/cl)^2)
  have hKfloor : 0 ≤ Kfloor := by dsimp [Kfloor]; positivity
  have Hcap := eventually_original_q_constraint_length_lower_draft
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    (Bclock:=Bclock) hm.le hC0
  have HN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hlog := HN.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1))
  have HthermalBudget := eventually_rate_quarter (3*Kfamily) (3*delta) (10*delta)
    6 (by positivity) (by linarith only [hdelta])
  have HprefixBudget := eventually_rate_quarter Kprefix (2*delta) (10*delta)
    0 hKprefix.le (by linarith only [hdelta])
  have HfloorBudget := eventually_rate_quarter Kfloor delta (10*delta)
    0 hKfloor (by linarith only [hdelta])
  have HradiusBudget := eventually_rate_quarter 144 (2*delta) (10*delta)
    2 (by norm_num) (by linarith only [hdelta])
  filter_upwards [Hfamily, Hprefix, Hpoint, Hcap, Hlog,
    HthermalBudget, HprefixBudget, HfloorBudget, HradiusBudget]
    with n hnFamily hnPrefix hnPoint hnCap hnLog hnThermalBudget
      hnPrefixBudget hnFloorBudget hnRadiusBudget
  intro Q hcarrier hlamFloor hmacro
  let P : Q.Potential := Classical.choice Q.exists_potential
  let B := Kfamily*(Real.log Q.data.N)^6*Q.data.N^(3*delta)*Q.data.E
  have hfinite : ∀ F : Finset (ordConnectedSection P.negativeSet),
      Q.lam*(∑ p : Eq7InnerCoverPiece (P.capFamily F) 1,
        eq7InnerThermalPiece (P.capFamily F) 1 p) ≤ B := by
    intro F
    have H := hnFamily Q P hcarrier hlamFloor hmacro F
    have hexp : 2*delta+delta = 3*delta := by ring
    rw [hexp] at H
    have hN0 : 0 ≤ Q.data.N := Q.data.hN.le
    have hE0 : 0 ≤ Q.data.E := Q.data.hE.le
    have hK := le_max_right 1 (OriginalQEq7RegularFamilyRateDraft.familyConstant
      delta cl Az D 2 qLow qPost qBroad)
    have Hmono := mul_le_mul_of_nonneg_right hK
      (by positivity : 0 ≤ (Real.log Q.data.N)^6*Q.data.N^(3*delta)*Q.data.E)
    exact H.trans (by simpa only [B, Kfamily, mul_assoc] using Hmono)
  have hU1 : comparisonSmallMass Q.data.N Q.data.E ≤ 1 :=
    Q.data.hsmall.trans Q.data.hd1
  have hprefix := hnPrefix Q hcarrier (hU1.trans hmacro)
  have hfloor := macro_full_floor_le_of_pointwise P
    (K:=Kpoint+(Az+1/cl)^2) (by positivity) hcarrier hmacro (hnPoint Q)
  have hradius := macro_radius_width_le hdelta.le
    (show 1 ≤ Real.log Q.data.N from hnLog)
    ((hnCap Q).trans (min_le_left _ _)) hcarrier hmacro
  have hbudgetT : 3*B ≤ (1/4:ℝ)*Q.data.N^(10*delta)*Q.data.E := by
    have H := hnThermalBudget Q.data.E Q.data.hE.le
    simpa only [B, ActualHighWallData.N, mul_assoc] using H
  have hbudgetP := hnPrefixBudget Q.data.E Q.data.hE.le
  have hbudgetF := hnFloorBudget Q.data.E Q.data.hE.le
  have hbudgetR := hnRadiusBudget Q.data.E Q.data.hE.le
  apply macro_density_of_parts P hfinite hprefix hfloor hradius
  dsimp only [Kfloor] at hbudgetF
  simp only [pow_zero, mul_one] at hbudgetP hbudgetF
  simp only [ActualHighWallData.N] at *
  linarith only [hbudgetT, hbudgetP, hbudgetF, hbudgetR]

theorem eventually_macro_gate_producer
    {m delta C0 D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (a : ActualHighWallData (n+1) delta)
        (_hdD : a.d ≤ D)
        (_hupper : Real.sqrt a.N*a.E ≤ a.d^2)
        (_hlower : a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E)
        (_hclock : a.T ≤ Bclock)
        (lam : ℝ) (hlam : lam ∈ Ioo (a.N^(-(10:ℝ))) (a.d^2)),
        a.N^(10*delta)*a.E < 2*lam →
        1 ≤ comparisonConditionalScale a.N delta a.E lam →
        ∀ alpha : a.Profile,
          (∀ beta : a.Profile,
            (a.thetaZeroShiftedParentData lam
              ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).objective alpha ≤
            (a.thetaZeroShiftedParentData lam
              ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).objective beta) →
          a.thetaZeroOriginalSweepDensity lam alpha ≤ a.N^(10*delta)*a.E := by
  have H := eventually_macro_density (cl:=1) (cu:=1) (Az:=2) (Ct:=1)
    (D:=D) (Bclock:=Bclock) hm hdelta hroom
    (by norm_num) (by norm_num) (by norm_num) hC0 (by norm_num)
  filter_upwards [H] with n hn
  intro a hdD hupper hlower hclock lam hlam _hunresolved hmacro alpha hminimum
  obtain ⟨Q, hdata, hQlam, hQalpha, hQxs, _⟩ := macro_base_carrier a
    lam ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le alpha
    hminimum hdelta.le hmacro hdD hupper hlower hclock
  have hcarrier : Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam := by
    rw [hdata, hQlam]
    exact hQxs
  have hFloor : Q.data.N^(-(10:ℝ)) ≤ Q.lam := by rw [hdata, hQlam]; exact hlam.1.le
  have hA : 1 ≤ Q.xs := by rw [hQxs]; exact hmacro
  have HQ := hn Q hcarrier hFloor hA
  cases hdata
  cases hQlam
  cases hQalpha
  exact HQ

end OAI.SKFluctuations.LaplaceWindowFormalization.MacroInnerFamilyProbe

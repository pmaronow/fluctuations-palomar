module

public import ComparisonNativeHybridThermalTailAccumulation
public import ComparisonNativeMassDyadicThermalBand
public import ComparisonActualHighOnlyInitialMassMismatch
public import ComparisonActualHighOnlyStrongIntermediateMassPhysicalDyad
public import ComparisonActualHighOnlyTargetHighTailHighDyad

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_regular_target_thermal_tail_high_only
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.data.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
        ∀u : ℝ, 2*c*M.xs ≤ u → u ≤ 1 →
          (∫s in u..1,orderedPathB (n+1) M.bf M.hf s-(orderedPathS (n+1) M.bf M.hf s)^2) ≤
            M.data.N^(-(actualMassSavingExponent m delta/4))*
              (M.xs^4/M.canonicalDirectTestBandScale^2) := by
  have Hmid := eventually_actual_high_only_regular_strong_intermediate_mass_dyad
    (D:=D) (Cs:=Cs) c Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hhigh := eventually_actual_regular_strong_high_mass_dyad_high_only
    (D:=D) (Cs:=Cs) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let eta := actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hcoef := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=nativeIntermediateAccumulationConstant 1+3)
      (d:=1) (q:=-eta/2) (r:=-eta/4) zero_lt_one (by linarith))
  filter_upwards [Hmid,Hhigh,Hcoef] with n hnMid hnHigh hnCoef
  intro M hclock hs hsxs hsomit hsmall hW1 u hu hu1
  let W := M.canonicalDirectTestBandScale
  let lo := c*M.xs
  let f := fun s=>orderedPathB (n+1) M.bf M.hf s-(orderedPathS (n+1) M.bf M.hf s)^2
  let A := M.data.N^(-eta/2)*(M.xs^4/W^2)
  have hW : 0 < W := M.canonical_direct_test_band_pos
  have hlo : 0 < lo := mul_pos hc M.hxs
  have hlohalf : lo ≤ 1/2 := by dsimp only [lo] at *; linarith only [hu,hu1]
  have hfi : IntervalIntegrable f volume 0 1 := M.original_thermal_intervalIntegrable
  have hf0 s (hs : s∈Icc (0:ℝ) 1) : 0 ≤ f s := M.actual_thermal_nonneg_on_unit hs
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have Htail := native_hybrid_tail_integral_le_dyadic_budget hfi hf0 hlo hlohalf hA hW hW1 (by
    intro v hv hv2 hvlo
    have hB := actualIntermediateMassEffectiveScale_pos hW hv
    by_cases hhigh : c*W ≤ v
    · have HH := hnHigh M hclock hs hsxs hsomit hsmall hW1 v hv hv2 hhigh
      have htarget : 0 < M.xs^4*v/W^2 := by have :=M.hxs; positivity
      have HI := (div_le_iff₀ htarget).mp HH
      have HI' : (∫s in v..2*v,f s) ≤ A*v := by
        convert HI using 1
        dsimp only [A,f,W,eta]
        simp only [neg_div]
        ring
      exact HI'.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB.le) hA)
    · have HH := hnMid M hclock hs hsxs hsomit hsmall hW1 v hv hv2 hvlo (not_le.mp hhigh).le
      have htarget : 0 < M.xs^4*v/(actualIntermediateMassEffectiveScale W v)^2 := by
        have :=M.hxs; positivity
      have HI := (div_le_iff₀ htarget).mp HH
      have HI' : (∫s in v..2*v,f s) ≤ A*actualIntermediateMassEffectiveScale W v := by
        apply HI.trans_eq
        change M.data.N^(-(eta/2))*(M.xs^4*v/(actualIntermediateMassEffectiveScale W v)^2)=_
        rw [show M.xs^4*v/(actualIntermediateMassEffectiveScale W v)^2 =
          M.xs^4*(v/(actualIntermediateMassEffectiveScale W v)^2) by ring,
          actualIntermediateMassEffectiveScale_inverse_square hW hv]
        dsimp [A]
        rw [neg_div]
        ring
      exact HI'.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hv.le) hA))
  have hbig : IntervalIntegrable f volume lo 1 := by
    apply hfi.mono_set
    rw [uIcc_of_le (by linarith only [hlohalf]),uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hlo.le le_rfl
  have hlu : lo ≤ u := by dsimp only [lo] at *; linarith only [hu,hlo]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc lo 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hf0 s ⟨hlo.le.trans hs.1.le,hs.2⟩
  have Hmono := intervalIntegral.integral_mono_interval hlu hu1 le_rfl hnonneg hbig
  have Hc : (nativeIntermediateAccumulationConstant 1+3)*M.data.N^(-eta/2) ≤
      M.data.N^(-eta/4) := by
    simpa only [ActualHighOnlyComparisonData.N,mul_one,one_mul,neg_div] using hnCoef
  have Hrate := mul_le_mul_of_nonneg_right Hc (show 0 ≤ M.xs^4/W^2 by positivity)
  apply Hmono.trans (Htail.trans _)
  convert Hrate using 1 <;> (dsimp only [A,W,eta]; simp only [neg_div]; try ring)

theorem eventually_actual_regular_target_high_l1_tail_high_only
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.data.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
        ∀u : ℝ, 2*c*M.xs ≤ u → u ≤ 1 →
          (∫s in u..1,Real.sqrt (orderedPathB (n+1) M.bf M.hf s-
            (orderedPathS (n+1) M.bf M.hf s)^2)) ≤
            M.data.N^(-(actualMassSavingExponent m delta/8))*
              (M.xs^2/M.canonicalDirectTestBandScale) := by
  filter_upwards [eventually_actual_regular_target_thermal_tail_high_only (D:=D) Bclock
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter] with n hn
  intro M hclock hs hsxs hsomit hsmall hW1 u hu hu1
  have hx := M.hxs
  have hu0 : 0 ≤ u := (by positivity : 0 ≤ 2*c*M.xs).trans hu
  have hfi := (M.original_thermal_intervalIntegrable).mono_set (by
    rw [uIcc_of_le hu1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hu0 le_rfl)
  have Hsq := interval_integral_sqrt_sq_le_length hu1 hfi
    (fun s hs=>M.actual_thermal_nonneg_on_unit ⟨hu0.trans hs.1,hs.2⟩)
  have HT := hn M hclock hs hsxs hsomit hsmall hW1 u hu hu1
  have Hmul := mul_le_mul_of_nonneg_left HT (sub_nonneg.mpr hu1)
  have Hlen := mul_le_mul_of_nonneg_right (show 1-u ≤ 1 by linarith)
    (show 0 ≤ M.data.N^(-(actualMassSavingExponent m delta/4))*
      (M.xs^4/M.canonicalDirectTestBandScale^2) by positivity)
  have Hsquare : (M.data.N^(-(actualMassSavingExponent m delta/8))*
      (M.xs^2/M.canonicalDirectTestBandScale))^2 =
      M.data.N^(-(actualMassSavingExponent m delta/4))*
        (M.xs^4/M.canonicalDirectTestBandScale^2) := by
    rw [mul_pow,div_pow,←Real.rpow_mul_natCast M.data.hN.le]
    norm_num only [Nat.cast_ofNat]
    rw [show -(actualMassSavingExponent m delta/8)*(2:ℝ) =
      -(actualMassSavingExponent m delta/4) by ring]
    ring
  have HR : 0 ≤ M.data.N^(-(actualMassSavingExponent m delta/8))*
      (M.xs^2/M.canonicalDirectTestBandScale) := by
    have :=M.canonical_direct_test_band_pos
    positivity
  have HH := Hsq.trans (Hmul.trans Hlen)
  rw [one_mul,←Hsquare] at HH
  nlinarith

theorem eventually_actual_regular_target_tail_with_initial_modulus_high_only
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity M.alpha.val.val M.b M.h 0 1),
        M.data.s≤1/4 → M.data.s≤M.xs → 64*M.data.s≤c*M.xs →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.data.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
        ∀x : ℝ, M.xs ≤ x → 2*c*x ≤ 1 → ∀u∈Icc (0:ℝ) 1,
          (∫s in u..1,Real.sqrt (orderedPathB (n+1) M.bf M.hf s-
            (orderedPathS (n+1) M.bf M.hf s)^2)) ≤
          (∫s in 0..2*c*x,Real.sqrt (orderedPathB (n+1) M.bf M.hf s-
            (orderedPathS (n+1) M.bf M.hf s)^2))+
            M.data.N^(-(actualMassSavingExponent m delta/8))*
              (M.xs^2/M.canonicalDirectTestBandScale) := by
  filter_upwards [eventually_actual_regular_target_high_l1_tail_high_only (D:=D) Bclock
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter] with n hn
  intro M hclock hs hsxs hsomit hsmall hW1 x hxs hx1 u hu
  have hx : 0 < x := M.hxs.trans_le hxs
  have hcut : 0 ≤ 2*c*x := by positivity
  have HI := native_intervalIntegrable_sqrt_of_intervalIntegrable
    (M.original_thermal_intervalIntegrable)
  have Hleft := HI.mono_set (by
    rw [uIcc_of_le hcut,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hx1)
  have Hright := HI.mono_set (by
    rw [uIcc_of_le hx1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hcut le_rfl)
  have Hmono := intervalIntegral.integral_mono_interval (a:=u) (b:=1)
    (c:=0) (d:=1) hu.1 hu.2 le_rfl (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) HI
  have Htail := hn M hclock hs hsxs hsomit hsmall hW1 (2*c*x)
    (mul_le_mul_of_nonneg_left hxs (by positivity)) hx1
  rw [←intervalIntegral.integral_add_adjacent_intervals Hleft Hright] at Hmono
  exact Hmono.trans (add_le_add le_rfl Htail)

end OAI.SKFluctuations.LaplaceWindowFormalization

module

public import ComparisonNativeActualFinitePhysicalConsumers
public import ComparisonNativeGlobalErrorAssemblySelective
public import ComparisonNativeNearZeroPhysicalSize
public import ComparisonNativeFloorPhysicalSize
public import ComparisonNativeActualMinimumCapTravelUnit
public import ComparisonNativeLargeConditionalScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000
namespace NativeOverlapMinimum

theorem eventually_actual_conditional_density_with_order
    (ell : ℕ) (hell : 2 < ell+1)
    {margin delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (horder : (delta+2)/(ell:ℝ) ≤ delta) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.context.d ≤ 1 →
      a.xs=comparisonConditionalScale a.context.N delta a.context.E a.lam →
      ∀(Kb Kh : ℝ≥0),
      LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1) →
      LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1) →
      nativeActualSweepDensity a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM
        (n+1) a.b a.h a.context.d a.lam a.alpha ≤ a.context.N^(10*delta)*a.context.E := by
  obtain ⟨Q,hQ,hbands⟩ := eventually_actual_finite_physical_consumers ell hell hm hdelta hroom
    hcl hcu hclcu hAz hC0 hCt horder
  obtain ⟨K,hK,hB⟩ := eventually_native_comparison_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hsR : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
  let gamma := 1/C0
  have hgamma : 0 < gamma := one_div_pos.mpr hC0
  let C := 1+cu*(Az+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnear := hsR.eventually (actual_native_near_zero_error_eventually (Cx:=1)
    hdelta hK.le (by norm_num) hAz hcl)
  have hfloor := hsR.eventually (actual_comparison_floor_error_eventually (C:=C)
    hdelta hm.le hgamma hK.le hC)
  have hsum := hsR.eventually (comparison_log_loss_eventually (C:=48) (p:=1) (by norm_num) hdelta)
  have hfour := hsR.eventually (comparison_log_loss_eventually (C:=4) (p:=0) (by norm_num) hdelta)
  have hq := hsR.eventually ((tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop 2))
  have hlog := hsR.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1))
  have htravel := eventually_actual_minimum_cap_travel_lt_one (m:=margin) (delta:=delta)
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hC0 (by linarith)
  filter_upwards [hbands,hs.eventually hB,hnear,hfloor,hsum,hfour,hq,hlog,htravel,
    hsR.eventually (eventually_ge_atTop (8:ℝ)),eventually_actual_minimum_physical_scalar_data hm hC0]
    with n hnbands hnB hnnear hnfloor hnsum hn4 hnq hnlog hntravel hn8 hnscalar
  intro a hd1 hxs Kb Kh hparent hfield
  have hN : 1 ≤ a.context.N := by exact_mod_cast Nat.succ_pos n
  have hscalar := hnscalar a hd1
  by_cases hy : a.xs+1 ≤ a.context.N
  · obtain ⟨p⟩ := a.exists_potential hnq
    have hnd := hscalar.2.2.1
    have hlg : 1 ≤ Real.log a.context.N := hnlog
    let dphys := Fintype.card (FeatureIndex (n+1))-1
    let e := cavityCanonicalFeatureEquiv n
    let Lside := 10*Real.log a.context.N
    have hLside : 0 ≤ Lside := by dsimp [Lside]; positivity
    let base := p.generalCanonicalModel Kb Kh hparent hfield (ell+1) hell Q Lside hQ hLside
      dphys e hlg hnd 1 zero_lt_one le_rfl
    obtain ⟨bands,hbudget⟩ := hnbands a hd1 hxs hy p Kb Kh hparent hfield dphys e hlg hnd
    change bands.budget=48*Real.log a.context.N*a.context.N^(7*delta)*a.context.E+
      (∫u in 0..min (8*base.U) 1,base.comparisonErrorDensity u) at hbudget
    have hshort : nativeCapTravel base < 1 := by
      change a.cavityCapTravel < 1
      exact hntravel a
    have hnonpositive := actual_full_native_nonpositive_error_le_of_finite_band_consumers base bands hshort
    have hlow := hnnear base a.z rfl rfl rfl (by
      change a.xs ≤ 1*comparisonConditionalScale a.context.N delta a.context.E a.lam
      simpa only [one_mul] using hxs.le)
      (hxs ▸ hscalar.2.2.2.2.2.1) a.hz a.hzxs (fun r hr=>(a.regular r hr).1) (hnB a)
    rw [nativeBroadNearZero_integral_eq_initial_mass] at hlow
    change (∫u in 0..min (8*base.U) 1,base.comparisonErrorDensity u) ≤
      a.context.N^(3*delta)*a.context.E at hlow
    have hlower : gamma*a.context.N^(-(2:ℝ)/3+margin)*a.context.d ≤ a.context.E := by
      have hh := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
      simpa only [gamma,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hh
    have hpositive := hnfloor base (nativeActualPositiveSet base) rfl rfl
      (nativeActualPositiveSet_measurable base) rfl hscalar.1 hlower
      (by
        filter_upwards [p.hfloor] with r hr hr01 hrp
        exact hr hr01 hrp.2)
      (hnB a) (by
        intro r hr _
        have hh := a.profile_upper_scale hcu hAz hr
        change a.xs+a.alpha.val.val r ≤ C*(comparisonConditionalScale a.context.N delta a.context.E a.lam+r)
        rw [←hxs]
        exact hh)
    change (∫u in 0..1,(nativeActualPositiveSet base).indicator (fun _=>1) (base.R u)*base.comparisonErrorDensity u) ≤
      a.context.N^(2*delta)*a.context.E at hpositive
    have htotal := actual_native_error_eq_nonpositive_add_positive base
    have hfull : (∫u in 0..1,base.comparisonErrorDensity u) ≤
        48*Real.log a.context.N*a.context.N^(7*delta)*a.context.E+
          2*(a.context.N^(3*delta)*a.context.E)+a.context.N^(2*delta)*a.context.E := by
      rw [htotal]
      rw [hbudget] at hnonpositive
      linarith
    have hNp := a.context.hN
    have hsum0 : 48*Real.log a.context.N ≤ a.context.N^delta := by
      simpa only [Real.rpow_one] using hnsum
    have h4 : 4 ≤ a.context.N^delta := by simpa only [Real.rpow_zero,mul_one] using hn4
    have hmain := mul_le_mul_of_nonneg_right hsum0
      (show 0 ≤ a.context.N^(7*delta)*a.context.E by have := a.context.hE; positivity)
    have he8 : a.context.N^delta*(a.context.N^(7*delta)*a.context.E)=a.context.N^(8*delta)*a.context.E := by
      rw [←mul_assoc,←Real.rpow_add hNp]
      congr 2
      ring
    rw [he8] at hmain
    have h38 := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN (show 3*delta ≤ 8*delta by linarith)) a.context.hE.le
    have h28 := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN (show 2*delta ≤ 8*delta by linarith)) a.context.hE.le
    have hlast := mul_le_mul_of_nonneg_right h4
      (show 0 ≤ a.context.N^(8*delta)*a.context.E by have := a.context.hE; positivity)
    have he9 : a.context.N^delta*(a.context.N^(8*delta)*a.context.E)=a.context.N^(9*delta)*a.context.E := by
      rw [←mul_assoc,←Real.rpow_add hNp]
      congr 2
      ring
    rw [he9] at hlast
    have h910 := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN (show 9*delta ≤ 10*delta by linarith)) a.context.hE.le
    change (∫u in 0..1,base.comparisonErrorDensity u) ≤ _
    nlinarith
  · have hlarge : a.context.N ≤ comparisonConditionalScale a.context.N delta a.context.E a.lam+1 := by
      rw [←hxs]
      exact (lt_of_not_ge hy).le
    have hb := a.context.actual_sweep_density_large_conditional_scale a.alpha a.b a.h
      a.hlam a.hlb a.hb a.hh a.hh0 hn8 hscalar.1 hlarge
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ a.context.hE.le
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem eventually_actual_conditional_density
    {margin delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.context.d ≤ 1 →
      a.xs=comparisonConditionalScale a.context.N delta a.context.E a.lam →
      ∀(Kb Kh : ℝ≥0),
      LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1) →
      LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1) →
      nativeActualSweepDensity a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM
        (n+1) a.b a.h a.context.d a.lam a.alpha ≤ a.context.N^(10*delta)*a.context.E := by
  obtain ⟨ell,hell⟩ := exists_nat_gt (max 2 ((delta+2)/delta))
  have hell2 : 2 < ell+1 := by
    have hh : (2:ℝ) < ell := (le_max_left _ _).trans_lt hell
    have hn : 2 < ell := by exact_mod_cast hh
    omega
  have hp : 0 < (ell:ℝ) := lt_trans (by norm_num : (0:ℝ) < 2) ((le_max_left _ _).trans_lt hell)
  have horder : (delta+2)/(ell:ℝ) ≤ delta := by
    apply (div_le_iff₀ hp).mpr
    have hh := (div_lt_iff₀ hdelta).mp ((le_max_right _ _).trans_lt hell)
    nlinarith
  exact eventually_actual_conditional_density_with_order ell hell2 hm hdelta hroom hcl hcu hclcu hAz hC0 hCt horder

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

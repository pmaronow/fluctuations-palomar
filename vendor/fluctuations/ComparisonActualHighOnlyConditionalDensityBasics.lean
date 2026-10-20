module

public import ComparisonActualHighOnlySweepBudget
public import ComparisonActualHighOnlyClocks
public import ComparisonActualHighOnlyInitialCharges
public import ComparisonNativeActualConditionalScales
public import ComparisonNativeLargeConditionalScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
namespace ActualHighOnlyComparisonData
variable {n : ℕ} {delta : ℝ}

theorem original_sweep_density_le_two_strength
    (a : ActualHighOnlyComparisonData n delta) (alpha : a.Profile) {lam : ℝ}
    (hlam : 0<lam) (hld : lam≤a.d^2) : a.originalSweepDensity lam alpha≤2*lam := by
  let R:=a.R alpha
  let bf:=a.bf alpha lam
  let hf:=a.hf alpha lam
  have hbf:=a.bf_monotone alpha (show lam∈Icc (0:ℝ) (a.d^2) from ⟨hlam.le,hld⟩)
  have hhf:=a.hf_monotone alpha (show lam∈Icc (0:ℝ) (a.d^2) from ⟨hlam.le,hld⟩)
  have hR:=omittedSweepQuantile_monotone zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha
  have hRb:=omittedSweepQuantile_bounds zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha
  have hquad:=actual_quadratic_integrable n a.hn bf hf hbf hhf R (hR.monotoneOn _)
    (fun u _=>(hRb u).1)
  have hco : ∀u,a.coefficient alpha lam u∈Icc (0:ℝ) lam := by
    intro u
    unfold coefficient omittedStrengthCoefficient
    split_ifs
    · exact ⟨(laplaceComparisonStrength_pos a.d hlam _).le,laplaceComparisonStrength_le a.d hlam.le _⟩
    · exact ⟨le_rfl,hlam.le⟩
  have hg:Measurable (fun u=>laplaceComparisonStrength a.d lam (R u)):=
    (laplaceComparisonStrength_contDiff a.d lam).continuous.measurable.comp
      (omittedSweepQuantile_continuous zero_le_one ⟨a.hs.1,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha).measurable
  have he:Measurable (a.coefficient alpha lam):=by
    convert hg.indicator (s:={u:ℝ|a.s≤u}) (measurableSet_le measurable_const measurable_id) using 1
    funext u
    simp only [coefficient,omittedStrengthCoefficient,Set.indicator_apply,mem_ofPred_eq,Function.comp_apply,R]
  have hi:=intervalIntegrable_bounded_measurable_mul he hlam.le (fun u _=>hco u) (hquad.1.add hquad.2)
  have hp:∀ᵐu∂volume.restrict (Ioc (0:ℝ) 1),
      a.coefficient alpha lam u*((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
        (orderedPathS n bf hf u-R u)^2)≤2*lam:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hs:=orderedPath_SK_bounds n a.hn bf hf hbf hhf hu
    have hr:R u∈Icc (0:ℝ) 1:=hRb u
    have hr2:(R u)^2≤1:=by nlinarith [hr.1,hr.2]
    have hbracket:(orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
        (orderedPathS n bf hf u-R u)^2≤2:=by
      have hm:=mul_nonneg hs.1 hr.1
      change 0≤orderedPathS n bf hf u*R u at hm
      nlinarith [hs.2.2.2]
    exact (mul_le_mul_of_nonneg_left hbracket (hco u).1).trans (by linarith [(hco u).2])
  unfold originalSweepDensity
  change (∫u in 0..1,a.coefficient alpha lam u*((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
    (orderedPathS n bf hf u-R u)^2))≤2*lam
  have H:(∫u in 0..1,a.coefficient alpha lam u*((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
      (orderedPathS n bf hf u-R u)^2))≤∫u in (0:ℝ)..1,(2*lam):=by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp intervalIntegrable_const) hp
  simpa using H

theorem original_sweep_density_large_conditional_scale
    (a : ActualHighOnlyComparisonData n delta) (alpha : a.Profile) {lam : ℝ}
    (hlam : 0<lam) (hld : lam≤a.d^2) (hN : 8≤a.N) (hE1 : a.E≤1)
    (hlarge : a.N≤comparisonConditionalScale a.N delta a.E lam+1) :
    a.originalSweepDensity lam alpha≤a.N^(2*delta)*a.E:=
  (a.original_sweep_density_le_two_strength alpha hlam hld).trans
    (comparison_large_conditional_scale_strength_le hN a.hE hE1 hlam hlarge)

end ActualHighOnlyComparisonData
namespace ActualHighOnlyOverlapMinimum
theorem eventually_actual_minimum_physical_scalar_data_high_only
    {margin delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < margin) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.context.d ≤ 1 →
      a.context.E ≤ 1 ∧ 1/a.context.N ≤ a.context.E ∧
      1/a.context.N ≤ a.context.d ∧ 1/a.context.N ≤ a.context.U ∧
      a.context.U ≤ 1 ∧ a.context.U ≤ a.xs ∧
      a.context.L ≤ a.context.U ∧ a.context.N^(-(1:ℝ)) ≤ a.context.L ∧
      4 ≤ a.context.N*a.context.E*a.context.d := by
  let gamma := 1/C0
  have hgamma : 0 < gamma := one_div_pos.mpr hC0
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hsR : Tendsto (fun n : ℕ=>(n+1:ℕ):ℕ→ℝ) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hs
  have hE := hs.eventually (eventually_coefficient_rpow_le (c:=1) (d:=gamma^2)
    (q:=-1) (r:=-(5:ℝ)/6+2*margin) (by positivity) (by linarith))
  have hd := hs.eventually (eventually_coefficient_rpow_le (c:=1) (d:=gamma)
    (q:=-1) (r:=-(1:ℝ)/6+margin) hgamma (by linarith))
  have hU := hs.eventually (eventually_coefficient_rpow_le (c:=C0^3) (d:=1)
    (q:=-3*margin) (r:=0) (by norm_num) (by linarith))
  have hP := hs.eventually (eventually_coefficient_rpow_le (c:=4) (d:=gamma^3)
    (q:=0) (r:=3*margin) (by positivity) (by linarith))
  have hL := hsR.eventually (comparison_physical_cap_length_eventually hm.le hgamma)
  filter_upwards [hE,hd,hU,hP,hL] with n hEn hdn hUn hPn hLn
  intro a hd1
  have hN : 1 ≤ a.context.N := by exact_mod_cast Nat.succ_pos n
  have hupper : a.context.E ≤ a.context.d^2/Real.sqrt a.context.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.context.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have hlower : gamma*a.context.N^(-(2:ℝ)/3+margin)*a.context.d ≤ a.context.E := by
    dsimp [gamma]
    have hh := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hh
  have hp := comparison_parent_scale_lower_bounds a.context.hN hgamma a.context.hd hlower hupper
  have hE1 : a.context.E ≤ 1 := by
    have hs1 : 1 ≤ Real.sqrt a.context.N := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN
    have hE0 := a.context.hE
    have hd0 := a.context.hd
    nlinarith [a.hupper]
  simp only [one_mul,Real.rpow_neg_one,←one_div] at hEn hdn
  have hElo : 1/a.context.N ≤ a.context.E := hEn.trans hp.2.1
  have hdlo : 1/a.context.N ≤ a.context.d := hdn.trans hp.1
  have hUlo : 1/a.context.N ≤ a.context.U := by
    unfold ActualHighOnlyComparisonData.U comparisonSmallMass
    apply one_div_le_one_div_of_le (mul_pos a.context.hN a.context.hE)
    nlinarith
  have hU1 : a.context.U ≤ 1 := by
    unfold ActualHighOnlyComparisonData.U comparisonSmallMass
    apply (div_le_one (mul_pos a.context.hN a.context.hE)).mpr
    simpa only [mul_comm] using (div_le_iff₀ a.context.hN).mp hElo
  have hUxs : a.context.U ≤ a.xs := by
    have hr := a.canonical_mass_small_ratio hC0
    simp only [Real.rpow_zero,one_mul] at hUn
    exact (div_le_one a.hxs).mp (hr.trans hUn)
  have hLlo : a.context.N^(-(1:ℝ)) ≤ a.context.L := by
    exact hLn a.context.d a.context.E a.context.hd hd1 a.context.hE hlower hupper
  have hprod := mul_le_mul hp.2.1 hp.1 (by positivity) a.context.hE.le
  have hprodN := mul_le_mul_of_nonneg_left hprod a.context.hN.le
  have he : a.context.N*((gamma^2*a.context.N^(-(5:ℝ)/6+2*margin))*
      (gamma*a.context.N^(-(1:ℝ)/6+margin)))=gamma^3*a.context.N^(3*margin) := by
    nth_rw 1 [←Real.rpow_one a.context.N]
    calc
      _ = gamma^3*(a.context.N^(1:ℝ)*a.context.N^(-(5:ℝ)/6+2*margin)*
        a.context.N^(-(1:ℝ)/6+margin)) := by ring
      _ = _ := by rw [←Real.rpow_add a.context.hN,←Real.rpow_add a.context.hN]; congr 2; ring
  rw [he] at hprodN
  simp only [Real.rpow_zero,mul_one] at hPn
  refine ⟨hE1,hElo,hdlo,hUlo,hU1,hUxs,min_le_left _ _,hLlo,?_⟩
  exact hPn.trans (by nlinarith only [hprodN])

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

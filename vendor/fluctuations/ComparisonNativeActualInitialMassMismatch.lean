module

public import ComparisonNativeActualAllCapMismatch
public import ComparisonNativeActualProfileSequence
public import ComparisonNativeActualInitialMassConcentration
public import ComparisonSignedCavityMinimumSourceClocks

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 7000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem mass_squared_mismatch_intervalIntegrable {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable (fun u=>(orderedPathS (n+1) M.bf M.hf u-M.R u)^2) volume 0 1 := by
  have hi : IntervalIntegrable (fun u=>orderedPathS (n+1) M.bf M.hf u-M.R u) volume 0 1 :=
    (show MonotoneOn (orderedPathS (n+1) M.bf M.hf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.mass_mean_monotone).intervalIntegrable.sub
      ((comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha).intervalIntegrable 0 1)
  have hb : ∀u∈Ioc (0:ℝ) 1,|orderedPathS (n+1) M.bf M.hf u-M.R u|≤1 := by
    intro u hu
    have HS:=M.mass_mean_unit_bounds (Ioc_subset_Icc_self hu)
    have HR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha u
    exact abs_le.mpr ⟨by linarith only [HS.1,HR.2],by linarith only [HS.2,HR.1]⟩
  simpa only [pow_two] using Hierarchy.intervalIntegrable_mul_bounded hi hi hb

theorem Potential.initial_mass_squared_mismatch_le {n : ℕ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {v A : ℝ} (hv : v∈Icc (0:ℝ) 1) (hA : 0≤A)
    (hamp : ∀u∈Ioc (0:ℝ) v,(orderedPathS (n+1) M.bf M.hf u-M.R u)^2≤A) :
    (∫u in 0..v,(orderedPathS (n+1) M.bf M.hf u-M.R u)^2) ≤
      16*M.cavityCapTravel^2*v+
      2*(∫u in 0..v,orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2)+
      A*(M.context.N^(-delta)*M.context.U) := by
  let F:=fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  have hsub : uIcc (0:ℝ) v ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hv.2
  have hi:=(M.mass_squared_mismatch_intervalIntegrable).mono_set hsub
  have hiF:=(native_comparison_thermal_intervalIntegrable M).mono_set hsub
  have hiMask : IntervalIntegrable p.positiveMassMask volume 0 v :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mpr
      (p.positiveMassMask_integrable.mono_set (Icc_subset_Icc le_rfl hv.2))
  have hpoint : ∀ᵐu∂volume.restrict (Icc (0:ℝ) v),
      (orderedPathS (n+1) M.bf M.hf u-M.R u)^2 ≤
        16*M.cavityCapTravel^2+2*F u+A*p.positiveMassMask u := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae p.all_nonpositive_squared_mismatch_ae_mass,
      ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with u hu hnonpos hu0
    have hui : u∈Icc (0:ℝ) 1 := ⟨hu.1,hu.2.trans hv.2⟩
    by_cases hp : p.H (M.R u)≤0
    · have hz:=(p.positiveMassMask_zero_iff u).mpr hp
      simpa only [hz,mul_zero,add_zero,F] using hnonpos hui hp
    · have hm : p.positiveMassMask u=1 := by
        have HR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
          M.context.hm M.context.hM M.alpha u
        have hm : M.R u∈p.positiveRadiusSet := ⟨HR,lt_of_not_ge hp⟩
        simp only [Potential.positiveMassMask,indicator_of_mem hm]
      rw [hm,mul_one]
      have H:=hamp u ⟨lt_of_le_of_ne hu.1 hu0.symm,hu.2⟩
      have HF:=M.actual_thermal_nonneg_on_unit hui
      change 0≤F u at HF
      nlinarith only [H,HF,sq_nonneg M.cavityCapTravel]
  have Hint:=intervalIntegral.integral_mono_ae_restrict hv.1 hi
    ((intervalIntegrable_const.add (hiF.const_mul 2)).add (hiMask.const_mul A)) hpoint
  have hmask : (∫u in 0..v,p.positiveMassMask u)≤M.context.N^(-delta)*M.context.U := by
    rw [intervalIntegral.integral_of_le hv.1,←integral_Icc_eq_integral_Ioc]
    apply le_trans _ p.positiveMassMask_mass_le
    apply setIntegral_mono_set p.positiveMassMask_integrable _
      (Eventually.of_forall (Icc_subset_Icc le_rfl hv.2))
    exact ae_of_all _ (fun u=>by
      dsimp only [Potential.positiveMassMask]
      exact indicator_nonneg (fun _ _=>zero_le_one) _)
  change (∫u in 0..v,(orderedPathS (n+1) M.bf M.hf u-M.R u)^2) ≤ _ at Hint
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add (hiF.const_mul 2))
      (hiMask.const_mul A),intervalIntegral.integral_add intervalIntegrable_const
      (hiF.const_mul 2),intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at Hint
  simp only [sub_zero,smul_eq_mul] at Hint
  have Hmask:=mul_le_mul_of_nonneg_left hmask hA
  nlinarith only [Hint,Hmask]

theorem actual_cap_travel_ratio_tendsto_zero
    (hC0 : 0<C0) (hroom : 0<3*m+delta)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) :
    Tendsto (fun n=>(M n).cavityCapTravel/W n) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [] with n
    exact hb.trans_le (div_nonneg (M n).cavityCapTravel_nonneg
      ((M n).hxs.trans_le (hxs n)).le)
  · intro e he
    filter_upwards [eventually_actual_minimum_cap_travel_small (D:=D)
      (epsilon:=e/2) hC0 hroom (half_pos he)] with n hn
    have hw:=(M n).hxs.trans_le (hxs n)
    have H:=((hn (M n)).1).trans (mul_le_mul_of_nonneg_left (hxs n) (half_pos he).le)
    exact ((div_le_iff₀ hw).mpr H).trans_lt (by linarith)

theorem actual_floor_mass_ratio_tendsto_zero
    (hC0 : 0<C0) (hroom : 0<3*m+delta)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) :
    Tendsto (fun n=>((M n).context.N^(-delta)*(M n).context.U)/W n) atTop (𝓝 0) := by
  have Hpow : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)^(-(3*m+delta))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hroom).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have Hlim:=Hpow.const_mul (C0^3)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n=>by
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg (M n).context.hN.le _)
      (M n).context.hU.le) hw.le) _ Hlim
  intro n
  have HU:=((div_le_div_of_nonneg_left (M n).context.hU.le (M n).hxs (hxs n)).trans
    ((M n).canonical_mass_small_ratio hC0))
  have H:=mul_le_mul_of_nonneg_left HU
    (Real.rpow_nonneg (M n).context.hN.le (-delta))
  rw [←mul_assoc,mul_comm ((M n).context.N^(-delta)) (C0^3),mul_assoc,
    ←Real.rpow_add (M n).context.hN] at H
  have he : -delta+-3*m=-(3*m+delta) := by ring
  rw [he] at H
  simpa only [mul_div_assoc,NativeOverlapContext.N] using H

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

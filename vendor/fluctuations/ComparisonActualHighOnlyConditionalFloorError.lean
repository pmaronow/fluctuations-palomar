module

public import ComparisonActualHighOnlyConditionalErrorTransport
public import ComparisonNativeFloorPhysicalSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_floor_error_of_ae_raw_high_only
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (F : Set ℝ) (hF : MeasurableSet F) {A K : ℝ} (hA : 0≤A) (hK : 0≤K)
    (hfloor : ∀ᵐr,r∈Icc (0:ℝ) 1 → r∈F → deriv a.alpha.val.val r=comparisonFloor a.data.N delta a.data.U r)
    (hraw : ∀ᵐr,r∈Icc (0:ℝ) 1 → r∈F → a.radiusB r≤K*(A+r)^2) :
    (∫u in 0..1,F.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)≤
      (K+1)*(2*a.lam*A^2*a.data.N^(-delta)*a.data.U+
        4*a.data.d^3*Real.log a.data.N*a.data.N^delta*a.data.U^2*
          Real.log ((1+a.data.N^(2*delta)*a.data.U)/(a.data.N^(2*delta)*a.data.U))) := by
  have hN : 1≤a.data.N:=by exact_mod_cast Nat.succ_pos n
  have hk:=comparisonFloor_continuousOn (δ:=delta) a.data.hN a.data.hU (show (0:ℝ)≤0 by rfl)
  have he:ContinuousOn (laplaceComparisonStrength a.data.d a.lam) (Icc (0:ℝ) 1):=
    (laplaceComparisonStrength_contDiff a.data.d a.lam).continuous.continuousOn
  have hright:IntegrableOn (fun r=>(K+1)*(comparisonFloor a.data.N delta a.data.U r*
      laplaceComparisonStrength a.data.d a.lam r*(A+r)^2)) (Icc (0:ℝ) 1):=
    (((hk.mul he).mul (((continuousOn_const (c:=A)).add continuousOn_id).pow 2)).const_mul (K+1)).integrableOn_Icc
  rw [a.original_error_mask_radius_integral F hF]
  have hle:=integral_mono_of_nonneg
    (f:=fun r=>deriv a.alpha.val.val r*F.indicator (fun _=>(1:ℝ)) r*a.radiusErrorDensity r)
    (g:=fun r=>(K+1)*(comparisonFloor a.data.N delta a.data.U r*
      laplaceComparisonStrength a.data.d a.lam r*(A+r)^2)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact mul_nonneg (mul_nonneg a.alpha.val.property.2.deriv_nonneg
        (indicator_nonneg (fun _ _=>zero_le_one) _))
        (mul_nonneg (laplaceComparisonStrength_pos a.data.d a.hlam r).le
          (add_nonneg (a.radiusThermal_nonneg hr) (sq_nonneg _)))) hright (by
      filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hfloor,ae_restrict_of_ae hraw]
        with r hr hf hrawr
      by_cases hrF:r∈F
      · rw [indicator_of_mem hrF,mul_one,hf hr hrF]
        have hquad:a.radiusThermal r+(a.radiusS r-r)^2≤(K+1)*(A+r)^2:=by
          have hmom:=a.radius_moments.2.2 r hr
          unfold radiusThermal
          nlinarith [hrawr hr hrF,mul_nonneg hmom.1.1 hr.1,mul_nonneg hA hr.1,sq_nonneg A]
        have H:=mul_le_mul_of_nonneg_left hquad
          (mul_nonneg (comparisonFloor_pos (δ:=delta) a.data.hN a.data.hU hr.1).le
            (laplaceComparisonStrength_pos a.data.d a.hlam r).le)
        dsimp only [radiusErrorDensity]
        nlinarith only [H]
      · rw [indicator_of_notMem hrF,mul_zero,zero_mul]
        exact mul_nonneg (by linarith : 0≤K+1)
          (mul_nonneg (mul_nonneg (comparisonFloor_pos (δ:=delta) a.data.hN a.data.hU hr.1).le
            (laplaceComparisonStrength_pos a.data.d a.hlam r).le) (sq_nonneg _)))
  have hbound:=mul_le_mul_of_nonneg_left
    (comparison_floor_quadratic_weight (A:=A) (delta:=delta) hN hlog a.data.hU a.data.hd hnd a.hlam a.hld)
    (show 0≤K+1 by linarith)
  rw [integral_const_mul] at hle
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc] at hbound
  exact hle.trans hbound

theorem actual_floor_error_of_normalized_B_high_only
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (F : Set ℝ) (hF : MeasurableSet F) {A K C : ℝ} (hA : 0≤A) (hK : 0≤K) (hC : 0≤C)
    (hfloor : ∀ᵐr,r∈Icc (0:ℝ) 1 → r∈F → deriv a.alpha.val.val r=comparisonFloor a.data.N delta a.data.U r)
    (hB : ∀u∈Ioc (0:ℝ) 1,orderedPathB (n+1) a.bf a.hf u≤K*(a.xs+u)^2)
    (hscale : ∀r∈Icc (0:ℝ) 1,r∈F → a.xs+a.alpha.val.val r≤C*(A+r)) :
    (∫u in 0..1,F.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)≤
      (K*C^2+1)*(2*a.lam*A^2*a.data.N^(-delta)*a.data.U+
        4*a.data.d^3*Real.log a.data.N*a.data.N^delta*a.data.U^2*
          Real.log ((1+a.data.N^(2*delta)*a.data.U)/(a.data.N^(2*delta)*a.data.U))) := by
  apply a.actual_floor_error_of_ae_raw_high_only hlog hnd F hF hA (mul_nonneg hK (sq_nonneg C)) hfloor
  filter_upwards [volume.ae_ne (0:ℝ)] with r hr0 hr hrF
  have hrp:0 < r:=lt_of_le_of_ne hr.1 hr0.symm
  have hαp:0 < a.alpha.val.val r:=by
    have H:=inverseConstraint_strictMonoOn a.data.hc a.data.hk a.data.hkc a.alpha.property
      (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) hr hrp
    rw [a.alpha.property.1] at H
    exact a.data.hs.1.trans_lt H
  have H:=hB _ ⟨hαp,(a.alpha.val.property.1 r).2⟩
  have hs:=pow_le_pow_left₀ (add_nonneg a.hxs.le hαp.le) (hscale r hr hrF) 2
  have ht:=mul_le_mul_of_nonneg_left hs hK
  change a.radiusB r≤_ at H
  nlinarith only [H,ht]

theorem profile_upper_scale_high_only
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) (hAz : 0≤Az) {r:ℝ} (hr:r∈Icc (0:ℝ) 1) :
    a.xs+a.alpha.val.val r≤(1+cu*(Az+1))*(a.xs+r) := by
  have hbound:a.alpha.val.val r≤cu*(Az*a.xs+r):=by
    by_cases hzr:a.z≤r
    · have hh:=(a.regular r ⟨hzr,hr.2⟩).2
      nlinarith [mul_nonneg (mul_nonneg hcu.le hAz) a.hxs.le]
    · have hh:=(a.alpha.val.property.2 (le_of_not_ge hzr)).trans
        (a.regular a.z ⟨le_rfl,a.hz.2⟩).2
      have hz:=mul_le_mul_of_nonneg_left a.hzxs hcu.le
      nlinarith [mul_nonneg hcu.le hr.1]
  have hcuxs:=mul_nonneg hcu.le a.hxs.le
  have hcur:=mul_nonneg (mul_nonneg hcu.le hAz) hr.1
  nlinarith [hr.1]

theorem eventually_actual_conditional_floor_error_high_only
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∀ᶠn:ℕ in atTop,∀a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.d≤1 → a.data.s≤1/4 → a.data.s≤a.xs →
      a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam → ∀P:a.Potential,
      (∫u in 0..1,P.positiveRadiusSet.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)≤
        a.data.N^(2*delta)*a.data.E := by
  obtain ⟨K,hK,HB⟩:=eventually_actual_high_only_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=1+cu*(Az+1)
  let gamma:=1/C0
  have hgamma:0 < gamma:=one_div_pos.mpr hC0
  have hC:0≤C:=by dsimp [C];positivity
  have hsR:Tendsto (fun n:ℕ=>((n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hcost:=hsR.eventually (comparison_floor_physical_cost_eventually (C:=C)
    hdelta hm.le hgamma hK.le)
  have Hlog:=hsR.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  filter_upwards [(tendsto_add_atTop_nat 1).eventually HB,Hcost,Hlog,
    eventually_actual_minimum_physical_scalar_data_high_only hm hC0] with n hnB hnCost hnLog hnScalar
  intro a hd1 hs hsxs hxs P
  have hscalar:=hnScalar a hd1
  have hlo:gamma*a.data.N^(-(2:ℝ)/3+m)*a.data.d≤a.data.E:=by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [gamma,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have HB':∀u∈Ioc (0:ℝ) 1,orderedPathB (n+1) a.bf a.hf u≤K*(a.xs+u)^2:=fun u hu=>hnB a hs hsxs u hu
  have HF:∀ᵐr,r∈Icc (0:ℝ) 1 → r∈P.positiveRadiusSet →
      deriv a.alpha.val.val r=comparisonFloor a.data.N delta a.data.U r:=by
    filter_upwards [P.hfloor] with r hr hri hrF
    exact hr hri hrF.2
  have H:=a.actual_floor_error_of_normalized_B_high_only hnLog hscalar.2.2.1 P.positiveRadiusSet
    P.positiveRadiusSet_measurable (A:=a.xs) a.hxs.le hK.le hC HF HB'
    (fun r hr _=>a.profile_upper_scale_high_only hcu hAz hr)
  rw [hxs] at H
  exact H.trans (hnCost a.data.E a.data.d a.lam a.data.hE hscalar.1 a.data.hd a.hlam hlo)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

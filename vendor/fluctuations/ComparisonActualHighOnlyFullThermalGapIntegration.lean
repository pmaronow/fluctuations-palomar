module

public import ComparisonActualHighOnlyFullThermalScalarGap
public import ComparisonActualHighOnlyAnalyticBasics

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
namespace ActualHighOnlyOverlapMinimum
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}
def originalFullThermalScalarGapIntegralSaving
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (A C e : ℝ) : ℝ :=
  C*((∫u in 0..1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))/M.xs^2)+C*A/(M.context.N*M.xs)+A*e

theorem originalFullThermalScalarGapIntegralSaving_nonneg
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {A C e : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e) :
    0 ≤ M.originalFullThermalScalarGapIntegralSaving A C e := by
  have hd : 0≤(∫u in 0..1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2)) := intervalIntegral.integral_nonneg zero_le_one (fun _ _=>Real.sqrt_nonneg _)
  have hx := M.hxs
  have hN := M.context.hN
  unfold originalFullThermalScalarGapIntegralSaving
  positivity

theorem actual_full_thermal_pointwise_modulus_integral_le
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {A C e q : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hq : q ∈ Icc (0:ℝ) 1) (hqA : q ≤ A*M.xs)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 q)
    (hpoint : ∀u ∈ Ioo (0:ℝ) q, |f u| ≤ C*M.xs^2*
      (Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2)+1/M.context.N)+e*M.xs^3) :
    (∫u in 0..q, |f u|) ≤ M.originalFullThermalScalarGapIntegralSaving A C e*M.xs^4 := by
  have hDI := native_intervalIntegrable_sqrt_of_intervalIntegrable
    (high_only_original_thermal_intervalIntegrable M)
  have hDq := hDI.mono_set (show uIcc (0:ℝ) q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2)
  have hDle : (∫u in 0..q, Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2)) ≤
      ((∫u in 0..1, Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2))/M.xs^2)*M.xs^2 := by
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 M.hxs.ne')]
    exact intervalIntegral.integral_mono_interval le_rfl hq.1 hq.2
      (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) hDI
  have hbound : (∫u in 0..q, |f u|) ≤
      ∫u in 0..q, C*M.xs^2*(Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2)+1/M.context.N)+e*M.xs^3 := by
    apply intervalIntegral.integral_mono_ae_restrict hq.1 hf.abs
      (((hDq.add intervalIntegrable_const).const_mul _).add intervalIntegrable_const)
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0:ℝ)), ae_restrict_of_ae (volume.ae_ne q)]
      with u hu hu0 huq
    exact hpoint u ⟨lt_of_le_of_ne hu.1 hu0.symm, lt_of_le_of_ne hu.2 huq⟩
  rw [intervalIntegral.integral_add ((hDq.add intervalIntegrable_const).const_mul _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hDq intervalIntegrable_const] at hbound
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hbound
  have h1 := mul_le_mul_of_nonneg_left hDle (mul_nonneg hC (sq_nonneg M.xs))
  have h2 := mul_le_mul_of_nonneg_left hqA
    (mul_nonneg (mul_nonneg hC (sq_nonneg M.xs)) (by positivity : 0 ≤ 1/M.context.N))
  have h3 := mul_le_mul_of_nonneg_right hqA (mul_nonneg he (pow_nonneg M.hxs.le 3))
  have hx := M.hxs.ne'
  have hN := M.context.hN.ne'
  have hid : M.originalFullThermalScalarGapIntegralSaving A C e*M.xs^4 =
      C*M.xs^2*(((∫u in 0..1,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))/M.xs^2)*M.xs^2)+
        (C*M.xs^2*(1/M.context.N))*(A*M.xs)+(A*M.xs)*(e*M.xs^3) := by
    unfold originalFullThermalScalarGapIntegralSaving
    field_simp
  rw [hid]
  nlinarith only [hbound, h1, h2, h3]

theorem actual_original_full_thermal_scalar_gap_before_star_integral_le
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {A C e star : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hstar : star ∈ Icc (0:ℝ) 1)
    (hpoint : ∀u, 0 < u → u ≤ A*M.xs → u < star →
      |orderedPathS (n+1) M.bf M.hf u-scalarCovarianceResponse hT
        (M.inheritedScalarMassProfile hT htotal) (actualMixedClock (n+1) M.bf M.hf u)| ≤
        C*M.xs^2*(Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2)+1/M.context.N)+e*M.xs^3) :
    (∫u in 0..min (A*M.xs) star, |orderedPathS (n+1) M.bf M.hf u-
      scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
        (actualMixedClock (n+1) M.bf M.hf u)|) ≤
      M.originalFullThermalScalarGapIntegralSaving A C e*M.xs^4 := by
  have hq : min (A*M.xs) star ∈ Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hA M.hxs).le hstar.1, (min_le_right _ _).trans hstar.2⟩
  apply M.actual_full_thermal_pointwise_modulus_integral_le hA hC he hq (min_le_left _ _) _
    (M.original_scalar_gap_intervalIntegrable hT _ hq)
  intro u hu
  exact hpoint u hu.1 (hu.2.le.trans (min_le_left _ _)) (hu.2.trans_le (min_le_right _ _))

theorem actual_original_full_thermal_scalar_gap_covered_integral_le
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {A C e star : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hstar : star ∈ Icc (0:ℝ) 1) (hcover : A*M.xs ≤ star)
    (hpoint : ∀u, 0 < u → u ≤ A*M.xs → u < star →
      |orderedPathS (n+1) M.bf M.hf u-scalarCovarianceResponse hT
        (M.inheritedScalarMassProfile hT htotal) (actualMixedClock (n+1) M.bf M.hf u)| ≤
        C*M.xs^2*(Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2)+1/M.context.N)+e*M.xs^3) :
    (∫u in 0..A*M.xs, |orderedPathS (n+1) M.bf M.hf u-
      scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
        (actualMixedClock (n+1) M.bf M.hf u)|) ≤
      M.originalFullThermalScalarGapIntegralSaving A C e*M.xs^4 := by
  simpa only [min_eq_left hcover] using M.actual_original_full_thermal_scalar_gap_before_star_integral_le
    hT htotal hA hC he hstar hpoint

end ActualHighOnlyOverlapMinimum
open ActualHighOnlyOverlapMinimum

def ActualOriginalScalarGapIntegralOnBandAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} {dim : ℕ→ℕ}
    (hT : 0<T) (A : ℝ) (eta : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) : Prop :=
  ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T,
    (∫u in 0..A*(M n).xs,|orderedPathS (dim n+1) (M n).bf (M n).hf u-
      scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT htotal)
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|)≤eta n*(M n).xs^4

theorem actual_high_only_comparable_context_original_scalar_gap_integral_of_full_thermal
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (Atarget : ℝ) (hAtarget : 0<Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2) atTop (𝓝 0)) :
    ∃eta : ℕ→ℝ,(∀n,0≤eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ActualOriginalScalarGapIntegralOnBandAlong_high_only G.hT Atarget eta M := by
  obtain ⟨C,hC,rate,hrate,Hrate,Hpoint⟩:=
    actual_high_only_comparable_context_original_scalar_gap_pointwise_of_full_thermal
      Atarget hAtarget hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G Hfull
  let site:=fun n=>1/((M n).context.N*(M n).xs)
  have Hsite : Tendsto site atTop (𝓝 0):=by
    have HH:=(actual_low_error_omitted_site_ratio_tendsto_zero_along_high_only hm hC0 dim hdim M).mul G.xs_zero
    simp only [zero_mul] at HH
    convert HH using 1
    funext n
    dsimp only [site,NativeOverlapContext.N]
    have hx:=(M n).hxs.ne'
    field_simp
  let eta:=fun n=>(M n).originalFullThermalScalarGapIntegralSaving Atarget C (rate n)
  have Heta : Tendsto eta atTop (𝓝 0):=by
    have HH:=((Hfull.const_mul C).add (Hsite.const_mul (C*Atarget))).add (Hrate.const_mul Atarget)
    simpa only [eta,originalFullThermalScalarGapIntegralSaving,site,mul_zero,add_zero,mul_one_div] using HH
  have heta n : 0≤eta n:=
    (M n).originalFullThermalScalarGapIntegralSaving_nonneg hAtarget hC (hrate n)
  refine ⟨eta,heta,Heta,?_⟩
  have Hband:=((G.xs_zero.const_mul Atarget).eventually
    (eventually_le_nhds (show Atarget*(0:ℝ)<1 by simp)))
  filter_upwards [Hpoint,Hband] with n hn hband
  obtain ⟨htotal,hn⟩:=hn
  refine ⟨htotal,?_⟩
  simpa only [eta,min_eq_left hband] using
    (M n).actual_original_full_thermal_scalar_gap_before_star_integral_le G.hT htotal
      hAtarget hC (hrate n) (star:=1) ⟨zero_le_one,le_rfl⟩ (fun u hu huA _=>hn u hu huA)

end OAI.SKFluctuations.LaplaceWindowFormalization

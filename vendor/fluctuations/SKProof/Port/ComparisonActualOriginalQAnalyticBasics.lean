module

public import SKProof.Port.ComparisonActualOriginalQClocks
public import SKProof.Port.OriginalQHighOnlyBridge
public import ComparisonNativeActualFullWeightedMass
public import ComparisonNativeActualNormalizedScalarGap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
attribute [local instance] Measure.Subtype.measureSpace
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

def inheritedScalarCavityResidual
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) (u : ℝ) : ℝ :=
  orderedPathS (n+1) M.sweepBf M.sweepHf u-
    scalarCovarianceResponse hT (M.inheritedScalarMassProfileBare hT htotal)
      (actualMixedClock (n+1) M.sweepBf M.sweepHf u)

theorem mass_mean_monotone
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn (orderedPathS (n+1) M.sweepBf M.sweepHf) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  by_cases hu0 : u = 0
  · subst u
    simpa only [orderedPathS,orderedPathPair_zero] using M.mass_mean_nonneg hv
  · let c := M.data
    have hbf := M.sweep_bf_monotone
    have hhf := M.sweep_hf_monotone
    have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    exact (orderedPath_SK_monotone (n+1) (by omega) M.sweepBf M.sweepHf hbf hhf).1
      ⟨huPos,hu.2⟩ ⟨huPos.trans_le huv,hv.2⟩ huv

theorem mass_mean_unit_bounds {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    orderedPathS (n+1) M.sweepBf M.sweepHf u ∈ Icc (0:ℝ) 1 := by
  refine ⟨M.mass_mean_nonneg hu,?_⟩
  by_cases hu0 : u=0
  · subst u
    simp only [orderedPathS,orderedPathPair_zero]
    norm_num
  · have H := orderedPath_SK_bounds (n+1) (by omega) M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩
    exact H.2.1

theorem mass_squared_mismatch_intervalIntegrable {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable (fun u=>(orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)^2) volume 0 1 := by
  have hi : IntervalIntegrable (fun u=>orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u) volume 0 1 :=
    (show MonotoneOn (orderedPathS (n+1) M.sweepBf M.sweepHf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.mass_mean_monotone).intervalIntegrable.sub
      ((M.sweepRadius_continuous).intervalIntegrable 0 1)

  have hb : ∀u∈Ioc (0:ℝ) 1,|orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u|≤1 := by
    intro u hu
    have HS:=M.mass_mean_unit_bounds (Ioc_subset_Icc_self hu)
    have HR:=M.sweepRadius_bounds0 u

    exact abs_le.mpr ⟨by linarith only [HS.1,HR.2],by linarith only [HS.2,HR.1]⟩
  simpa only [pow_two] using Hierarchy.intervalIntegrable_mul_bounded hi hi hb

theorem original_retained_mismatch_integrable {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (v : ℝ) :
    Integrable (fun w : ParisiFinite.OrderPoint=>orderedPathS (n+1) M.sweepBf M.sweepHf w-M.sweepRadius w)
      ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v}) ∧
    Integrable (fun w : ParisiFinite.OrderPoint=>(orderedPathS (n+1) M.sweepBf M.sweepHf w-M.sweepRadius w)^2)
      ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v}) := by
  have hi : IntervalIntegrable (fun u=>orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u) volume 0 1 :=
    (show MonotoneOn (orderedPathS (n+1) M.sweepBf M.sweepHf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.mass_mean_monotone).intervalIntegrable.sub
      ((M.sweepRadius_continuous).intervalIntegrable 0 1)

  have hi1:=unitInterval.measurePreserving_coe.integrable_comp_of_integrable
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi)
  have hi2:=unitInterval.measurePreserving_coe.integrable_comp_of_integrable
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      M.mass_squared_mismatch_intervalIntegrable)
  exact ⟨hi1.integrableOn,hi2.integrableOn⟩

theorem inherited_bare_residual_integrable {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (mu : Measure ParisiFinite.OrderPoint) [IsFiniteMeasure mu] (x : ℝ) :
    Integrable (fun w : ParisiFinite.OrderPoint=>
      (((M.b w-T)*orderedPathS (n+1) M.sweepBf M.sweepHf w+M.h w)/x^3)) mu := by
  have hbm : Measurable (fun w : ParisiFinite.OrderPoint=>M.b w) :=
    (show Monotone (fun w : ParisiFinite.OrderPoint=>M.b w) from
      fun u v huv=>M.hb u.property v.property huv).measurable
  have hhm : Measurable (fun w : ParisiFinite.OrderPoint=>M.h w) :=
    (show Monotone (fun w : ParisiFinite.OrderPoint=>M.h w) from
      fun u v huv=>M.hh u.property v.property huv).measurable
  have hsm : Measurable (fun w : ParisiFinite.OrderPoint=>orderedPathS (n+1) M.sweepBf M.sweepHf w) :=
    (show Monotone (fun w : ParisiFinite.OrderPoint=>orderedPathS (n+1) M.sweepBf M.sweepHf w) from
      fun u v huv=>M.mass_mean_monotone u.property v.property huv).measurable
  have hmeas:=((hbm.sub_const T).mul hsm).add hhm
  have hi : Integrable (fun w : ParisiFinite.OrderPoint=>
      (M.b w-T)*orderedPathS (n+1) M.sweepBf M.sweepHf w+M.h w) mu := by
    apply (integrable_const (M.b 1+|T|+M.h 1)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with w
    have hb0 : 0 ≤ M.b w := M.hb0.trans (M.hb (by norm_num) w.property w.property.1)
    have hb1 : M.b w ≤ M.b 1 := M.hb w.property (by norm_num) w.property.2
    have hh0 : 0 ≤ M.h w := M.hh0.trans (M.hh (by norm_num) w.property w.property.1)
    have hh1 : M.h w ≤ M.h 1 := M.hh w.property (by norm_num) w.property.2
    have hs:=M.mass_mean_unit_bounds w.property
    have hbabs : |M.b w-T| ≤ M.b 1+|T| :=
      (abs_sub (M.b w) T).trans (by rw [abs_of_nonneg hb0];linarith)
    have hm:=mul_le_mul hbabs hs.2 hs.1 (by linarith [abs_nonneg T])
    have H:=abs_add_le ((M.b w-T)*orderedPathS (n+1) M.sweepBf M.sweepHf w) (M.h w)
    change |(M.b w-T)*orderedPathS (n+1) M.sweepBf M.sweepHf w+M.h w| ≤ _
    rw [abs_mul,abs_of_nonneg hs.1,abs_of_nonneg hh0] at H
    nlinarith only [H,hm,hh1]
  exact hi.div_const _

theorem original_scalar_gap_intervalIntegrable
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (alpha : boundedMassProfiles) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (fun u => orderedPathS (n+1) M.sweepBf M.sweepHf u -
      scalarCovarianceResponse hT alpha (actualMixedClock (n+1) M.sweepBf M.sweepHf u)) volume 0 q := by
  have hsub : uIcc (0:ℝ) q ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hq.1]
    exact Icc_subset_Icc le_rfl hq.2
  have hs : IntervalIntegrable (orderedPathS (n+1) M.sweepBf M.sweepHf) volume 0 q :=
    (M.mass_mean_monotone.mono hsub).intervalIntegrable
  have hK : MonotoneOn (actualMixedClock (n+1) M.sweepBf M.sweepHf) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (M.inherited_hf_monotone hu hv huv)
      (mul_le_mul (M.inherited_bf_monotone hu hv huv)
        (M.mass_mean_monotone hu hv huv) (M.mass_mean_nonneg hu) (NNReal.coe_nonneg _))
  have hki : IntervalIntegrable (fun u => actualMixedClock (n+1) M.sweepBf M.sweepHf u/T) volume 0 q :=
    (hK.mono hsub).intervalIntegrable.div_const T
  have he : IntervalIntegrable (fun u => scalarPlantedEnergy hT alpha
      (actualMixedClock (n+1) M.sweepBf M.sweepHf u/T)) volume 0 q := by
    rw [intervalIntegrable_iff, uIoc_of_le hq.1]
    apply Integrable.of_bound
      ((scalarPlantedEnergy_continuous hT alpha).comp_aestronglyMeasurable
        hki.1.aestronglyMeasurable) 1
    filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (scalarPlantedEnergy_bounds hT alpha _).1]
    exact (scalarPlantedEnergy_bounds hT alpha _).2
  exact hs.sub he

theorem inherited_scalar_cavity_residual_normalized_integrable {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) (x v : ℝ) :
    Integrable (fun w : ParisiFinite.OrderPoint =>
      M.inheritedScalarCavityResidual hT htotal w/x^3)
      (comparisonNormalizedClockMass x v) := by
  have hi := M.original_scalar_gap_intervalIntegrable hT
    (M.inheritedScalarMassProfileBare hT htotal) (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
  have hi1 := unitInterval.measurePreserving_coe.integrable_comp_of_integrable
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi)
  have hi2 : Integrable (fun w : ParisiFinite.OrderPoint =>
      M.inheritedScalarCavityResidual hT htotal w)
      ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v}) :=
    hi1.integrableOn
  exact (hi2.smul_measure ENNReal.ofReal_ne_top).div_const _

theorem original_weighted_mismatch_integrable (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (mu : Measure ParisiFinite.OrderPoint) [IsFiniteMeasure mu] (x : ℝ) :
    Integrable (fun w : ParisiFinite.OrderPoint =>
      M.sweepCoefficient w*
        (orderedPathS (n+1) M.sweepBf M.sweepHf w-M.sweepRadius w)/x^3) mu := by
  have hrm : Measurable (fun w : ParisiFinite.OrderPoint => M.sweepRadius w) :=
    (M.sweepRadius_continuous).measurable.comp measurable_subtype_coe

  have hsm : Measurable (fun w : ParisiFinite.OrderPoint => orderedPathS (n+1) M.sweepBf M.sweepHf w) :=
    (show Monotone (fun w : ParisiFinite.OrderPoint => orderedPathS (n+1) M.sweepBf M.sweepHf w) from
      fun u v huv => M.mass_mean_monotone u.property v.property huv).measurable
  have hg := (laplaceComparisonStrength_contDiff M.data.d M.lam).continuous.measurable.comp hrm
  have hem : Measurable (fun w : ParisiFinite.OrderPoint=>M.sweepCoefficient w) := by
    have H:=hg.indicator (s:={w : ParisiFinite.OrderPoint | M.data.s≤(w:ℝ)})
      (measurableSet_le measurable_const measurable_subtype_coe)
    convert H using 1
    funext w
    simp only [sweepCoefficient,omittedStrengthCoefficient,Set.indicator_apply,mem_ofPred_eq,Function.comp_apply]
  have hi : Integrable (fun w : ParisiFinite.OrderPoint =>
      M.sweepCoefficient w*
        (orderedPathS (n+1) M.sweepBf M.sweepHf w-M.sweepRadius w)) mu := by
    apply (integrable_const (2*M.lam)).mono' (hem.mul (hsm.sub hrm)).aestronglyMeasurable
    filter_upwards [] with w
    have hs := M.mass_mean_unit_bounds w.property
    have hr := M.sweepRadius_bounds0 (w:ℝ)

    have he := M.coefficient_nonneg w
    have hel := M.coefficient_le_lam w
    have hm : |orderedPathS (n+1) M.sweepBf M.sweepHf w-M.sweepRadius w| ≤ 2 := by
      apply abs_le.mpr; constructor <;> linarith only [hs.1,hs.2,hr.1,hr.2]
    change |M.sweepCoefficient w*
      (orderedPathS (n+1) M.sweepBf M.sweepHf w-M.sweepRadius w)| ≤ 2*M.lam
    rw [abs_mul,abs_of_nonneg he]
    exact (mul_le_mul_of_nonneg_left hm he).trans (by linarith only [hel])
  exact hi.div_const _

theorem canonical_direct_test_band_pos
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    0 < a.directTestWorkingScale := a.hxs.trans_le (le_max_left _ _)

theorem canonical_direct_test_band_ge_scale
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    a.xs ≤ a.directTestWorkingScale := le_max_left _ _

theorem canonical_direct_test_band_geometry
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs) :
    a.directTestWorkingScale ≤ (Cs+1)*a.data.d ∧
      a.directTestWorkingScale^2 ≤ (Cs+1)*a.lam := by
  have Hg : 0 ≤ laplaceComparisonStrength a.data.d a.lam a.xs:=
    (laplaceComparisonStrength_pos _ a.hlam _).le
  have HgLam:=laplaceComparisonStrength_le a.data.d a.hlam.le a.xs
  have Hgd:=HgLam.trans a.hld
  have HxLam:=hsmall.trans (mul_le_mul_of_nonneg_left HgLam hCs)
  have Hxd:=hsmall.trans (mul_le_mul_of_nonneg_left Hgd hCs)
  have HX : a.xs ≤ (Cs+1)*a.data.d := by
    have Hcoef : Cs ≤ (Cs+1)^2 := by nlinarith
    have HH:=mul_le_mul_of_nonneg_right Hcoef (sq_nonneg a.data.d)
    have Hbound : a.xs^2 ≤ ((Cs+1)*a.data.d)^2:=by nlinarith
    have HY : 0 ≤ (Cs+1)*a.data.d:=mul_nonneg (by linarith) a.data.hd.le
    nlinarith [a.hxs]
  have Hsqrt : Real.sqrt (laplaceComparisonStrength a.data.d a.lam a.xs) ≤ a.data.d := by
    have H:=Real.sqrt_le_sqrt Hgd
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos a.data.hd] using H
  constructor
  · exact max_le HX (Hsqrt.trans (by nlinarith [a.data.hd]))
  · unfold directTestWorkingScale
    rcases le_total a.xs (Real.sqrt (laplaceComparisonStrength a.data.d a.lam a.xs)) with H|H
    · rw [max_eq_right H,Real.sq_sqrt Hg]
      nlinarith [a.hlam,mul_nonneg hCs a.hlam.le]
    · rw [max_eq_left H]
      nlinarith [a.hlam]

theorem eventually_actual_mass_mean_upper_original_q
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃B : ℝ,0 < B ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs → ∀u∈Ioc (0:ℝ) 1,
          orderedPathS (n+1) M.sweepBf M.sweepHf u ≤ B*(M.xs+u) := by
  obtain ⟨K,hK,HK⟩:=eventually_actual_B_normalized_original_q (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K+1,by positivity,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually HK] with n hn M hs hsx u hu
  have HS:=orderedPath_SK_bounds (n+1) (by omega) M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone hu
  have HB:=hn M hs hsx u hu
  have HK' : K ≤ (K+1)^2:=by nlinarith [sq_nonneg K]
  have Hmul:=mul_le_mul_of_nonneg_right HK' (sq_nonneg (M.xs+u))
  have Hpos : 0 ≤ (K+1)*(M.xs+u):=mul_nonneg (by positivity) (by linarith [M.hxs,hu.1])
  nlinarith only [HS.1,HS.2.2.1,HB,Hmul,Hpos]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

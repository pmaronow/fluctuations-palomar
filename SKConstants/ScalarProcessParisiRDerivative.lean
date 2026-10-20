module

public import SKConstants.ScalarProcessContinuationProfiles
public import SKConstants.ParisiPostEndpointLaw
public import SKConstants.Upstream.OAI.Probability.SKSupport.Regularity.TimeFields
public import SKConstants.Upstream.OAI.Probability.SKSupport.Foundations.SoftAbs
public import SKConstants.ParisiCDFPathRight
public import SKConstants.ScalarProcessGenerator
public import SKConstants.ParisiEquilibriumMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ScalarProcessParisiRDerivative_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem scalarContinuationR_eq_hiddenFieldPath_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (F : Ω → ScalarContinuousPath T) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ), F ω t=B ⟨t,t.property.1⟩ ω) :
    scalarContinuationR ν T = ∫ u,
      scalarDefect (scalarSeedHiddenFieldPath T F u ⟨T,T.coe_nonneg,le_rfl⟩)^2
        ∂scalarSeedHiddenBrownianLaw ν P := by
  have hm : Measurable (fun u : ℝ × (Bool × Ω) =>
      scalarDefect (scalarSeedHiddenFieldPath T F u ⟨T,T.coe_nonneg,le_rfl⟩)^2) :=
    (measurable_scalarDefect.comp ((ContinuousMap.measurable_eval _).comp
      (measurable_scalarSeedHiddenFieldPath T F hFm))).pow_const 2
  have hi : Integrable (fun u : ℝ × (Bool × Ω) =>
      scalarDefect (scalarSeedHiddenFieldPath T F u ⟨T,T.coe_nonneg,le_rfl⟩)^2)
      (scalarSeedHiddenBrownianLaw ν P) := Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ (fun u => norm_scalarDefect_sq_le_one _))
  rw [scalarContinuationR_eq_actualAverage ν P B hB,scalarSeedHiddenBrownianLaw,
    Measure.integral_compProd hi]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  change scalarHiddenExpectedDefectSqReal P z B ((T : ℝ).toNNReal : ℝ) =
    ∫ u, scalarDefect (scalarSeedHiddenFieldPath T F (z,u) ⟨T,T.coe_nonneg,le_rfl⟩)^2
      ∂scalarHiddenBrownianLaw z P
  simp only [Real.toNNReal_coe,scalarHiddenExpectedDefectSqReal,scalarHiddenFieldReal]
  apply integral_congr_ae
  have hf := (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hF
  filter_upwards [hf] with u hu
  dsimp only [scalarSeedHiddenFieldPath,ContinuousMap.coe_mk]
  rw [hu ⟨T,T.coe_nonneg,le_rfl⟩]
  congr 3

theorem actualParisiContinuationR_eq_full_process_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) (hv : 0 ≤ v) :
    actualParisiContinuationR W β v = ∫ w,
      scalarDefect (actualParisiFullScalarProcess W β
        (parisiEquilibriumPhysicalEndpoint β+v.toNNReal) w)^2 ∂W.law := by
  let T := v.toNNReal
  let t : Icc (0 : ℝ) (T : ℝ) := ⟨T,T.coe_nonneg,le_rfl⟩
  have hobs : Measurable (fun p : ℝ × ScalarContinuousPath T => scalarDefect (p.2 t)^2) :=
    (measurable_scalarDefect.comp ((ContinuousMap.measurable_eval t).comp measurable_snd)).pow_const 2
  have hleft : Measurable (fun w =>
      (actualParisiPreContinuationField W β (parisiEquilibriumPhysicalEndpoint β) w,
        actualParisiPostEndpointPath W β T w)) :=
    (measurable_actualParisiPreContinuationField W β _).prodMk
      (measurable_boundedDriftRestartPath W _ _ _)
  have hright : Measurable (fun u : ℝ × (Bool × Ω) =>
      (u.1,scalarSeedHiddenFieldPath T (brownianFinitePath W T) u)) :=
    measurable_fst.prodMk (measurable_scalarSeedHiddenFieldPath T _ (measurable_brownianFinitePath W T))
  have he := congrArg (fun μ : Measure (ℝ × ScalarContinuousPath T) =>
      ∫ p,scalarDefect (p.2 t)^2 ∂μ) (actualParisiEndpointSeed_post_hidden_jointLaw W β hβ T)
  rw [integral_map hleft.aemeasurable hobs.aestronglyMeasurable,
    integral_map hright.aemeasurable hobs.aestronglyMeasurable] at he
  have hr := scalarContinuationR_eq_hiddenFieldPath_moment (actualParisiEndpointSeedLaw W β)
    W.law W.B W.brownian.toIsPreBrownianReal T (brownianFinitePath W T)
    (measurable_brownianFinitePath W T) (brownianFinitePath_version W T)
  change scalarContinuationR (actualParisiEndpointSeedLaw W β) v = _
  rw [← Real.coe_toNNReal v hv,hr]
  refine he.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [actualParisiPostEndpointPath_version W β T] with w hw
  rw [hw t]
  simp only [Real.toNNReal_coe]
  congr 3

theorem boundedSmooth_scalarDefect : BoundedSmooth scalarDefect := by
  have ht : BoundedSmooth Real.tanh := by
    simpa only [one_mul] using boundedSmooth_tanh_mul 1
  have h := (BoundedSmooth.const 1).add ((ht.mul ht).const_mul (-1))
  convert h using 1
  funext x
  dsimp [scalarDefect]
  ring

theorem boundedSmooth_scalarDefect_sq : BoundedSmooth (fun x => (scalarDefect x)^2) := by
  simpa only [pow_two] using boundedSmooth_scalarDefect.mul boundedSmooth_scalarDefect

def actualParisiFullDefectSquareMoment (W : BrownianSystem Ω) (β : ℝ) (v : ℝ) : ℝ :=
  ∫ w, scalarDefect (actualParisiFullScalarProcess W β v.toNNReal w)^2 ∂W.law

def actualParisiContinuationThirdMoment (W : BrownianSystem Ω) (β : ℝ) (v : ℝ) : ℝ :=
  ∫ w, scalarDefect (actualParisiFullScalarProcess W β
    (parisiEquilibriumPhysicalEndpoint β+v.toNNReal) w)^3 ∂W.law

def scalarDefectSquareTimeField (T : ℝ) : TimeField T where
  f := fun _ x => (scalarDefect x)^2
  d := fun _ _ => 0
  smooth := by
    have hg := boundedSmooth_scalarDefect_sq
    refine ⟨hg.smooth.continuous.measurable.comp measurable_snd,fun _ => hg,?_⟩
    intro n
    obtain ⟨C,hC⟩ := hg.bounds n
    exact ⟨C,fun _ x => hC x⟩
  rate_smooth := BoundedSmoothFamily.timeConst measurable_const (C := 0) (by simp)
  continuous := boundedSmooth_scalarDefect_sq.smooth.continuous.comp continuous_snd
  rate_right := fun _ _ => continuousWithinAt_const
  time_deriv := fun _ _ _ _ => hasDerivWithinAt_const _ _ _

theorem actualParisiFullDefectSquareMoment_hasDerivWithinAt_right
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (s : ℝ≥0)
    (hs : β^2*parisiEquilibriumSupportEndpoint β ≤ (s : ℝ)) :
    HasDerivWithinAt (actualParisiFullDefectSquareMoment W β)
      (∫ w, 4*scalarDefect (actualParisiFullScalarProcess W β s w)^2-
        6*scalarDefect (actualParisiFullScalarProcess W β s w)^3 ∂W.law)
      (Ioi (s : ℝ)) s := by
  let F := scalarDefectSquareTimeField ((s : ℝ)+1)
  have hbr : ∀ᵐ w ∂W.law,
      ContinuousWithinAt (fun r => (actualParisiFullScalarDrift β).pathDrift W r w) (Ioi (s : ℝ)) s := by
    exact (finiteTemperatureCDFDrift_path_right_continuous W β _ _ _).mono (fun w hw => hw s)
  have H := F.expected_hasDerivWithinAt_right (actualParisiFullScalarDrift β) W s (by linarith) hbr
  change HasDerivWithinAt (actualParisiFullDefectSquareMoment W β) _ _ _ at H
  convert H using 1
  apply integral_congr_ae
  apply ae_of_all
  intro w
  dsimp only [F,TimeField.generator,scalarDefectSquareTimeField]
  rw [actualParisiFullScalarDrift_eq_tanh_after_support β hβ _ hs]
  simpa only [scalarGenerator,actualParisiFullScalarProcess,zero_add,add_zero,mul_comm,
    add_comm,div_eq_mul_inv,Nat.cast_ofNat,one_mul] using
    (scalarGenerator_defect_sq (actualParisiFullScalarProcess W β s w)).symm

theorem actualParisiContinuationR_eq_shifted_full_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) (hv : 0 ≤ v) :
    actualParisiContinuationR W β v = actualParisiFullDefectSquareMoment W β
      ((parisiEquilibriumPhysicalEndpoint β : ℝ)+v) := by
  rw [actualParisiContinuationR_eq_full_process_moment W β hβ v hv]
  unfold actualParisiFullDefectSquareMoment
  congr 1
  funext w
  have he : (((parisiEquilibriumPhysicalEndpoint β : ℝ)+v).toNNReal : ℝ≥0) =
      parisiEquilibriumPhysicalEndpoint β+v.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by positivity),NNReal.coe_add,Real.coe_toNNReal v hv]
  rw [he]

theorem actualParisiContinuationR_hasDerivWithinAt_right
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) (hv : 0 ≤ v) :
    HasDerivWithinAt (actualParisiContinuationR W β)
      (4*actualParisiContinuationR W β v-6*actualParisiContinuationThirdMoment W β v)
      (Ioi v) v := by
  let V := parisiEquilibriumPhysicalEndpoint β
  let s : ℝ≥0 := V+v.toNNReal
  have hscoe : (s : ℝ)=(V : ℝ)+v := by simp only [s,NNReal.coe_add,Real.coe_toNNReal v hv]
  have hs : β^2*parisiEquilibriumSupportEndpoint β ≤ (s : ℝ) := by
    rw [hscoe]
    dsimp only [V]
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
    linarith
  have H := actualParisiFullDefectSquareMoment_hasDerivWithinAt_right W β hβ s hs
  rw [hscoe] at H
  have hid : HasDerivWithinAt (fun x : ℝ => (V : ℝ)+x) 1 (Ioi v) v :=
    ((hasDerivAt_id v).const_add (V : ℝ)).hasDerivWithinAt
  have hc := H.comp v hid (by
    intro x hx
    change v < x at hx
    change (V : ℝ)+v < (V : ℝ)+x
    linarith)
  have he : (fun x : ℝ => actualParisiFullDefectSquareMoment W β ((V : ℝ)+x)) =ᶠ[nhdsWithin v (Ioi v)]
      actualParisiContinuationR W β := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (actualParisiContinuationR_eq_shifted_full_moment W β hβ x (hv.trans hx.le)).symm
  have hc' := hc.congr_of_eventuallyEq he.symm
    (actualParisiContinuationR_eq_shifted_full_moment W β hβ v hv)
  have hmeas : Measurable (fun w => scalarDefect (actualParisiFullScalarProcess W β s w)) :=
    measurable_scalarDefect.comp (measurable_actualParisiPreContinuationField W β s)
  have hi (n : ℕ) : Integrable (fun w => scalarDefect (actualParisiFullScalarProcess W β s w)^n) W.law :=
    Integrable.of_bound (hmeas.pow_const n).aestronglyMeasurable 1 (ae_of_all _ (fun w => by
      rw [norm_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (norm_scalarDefect_le_one _) n))
  have hcoeff : (∫ w,4*scalarDefect (actualParisiFullScalarProcess W β s w)^2-
        6*scalarDefect (actualParisiFullScalarProcess W β s w)^3 ∂W.law) =
      4*actualParisiContinuationR W β v-6*actualParisiContinuationThirdMoment W β v := by
    rw [integral_sub ((hi 2).const_mul 4) ((hi 3).const_mul 6),integral_const_mul,integral_const_mul,
      actualParisiContinuationR_eq_full_process_moment W β hβ v hv]
    rfl
  simpa only [hcoeff,mul_one] using hc'

theorem actualParisiContinuationR_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    actualParisiContinuationR W β 0=1/β^2 := by
  let V := parisiEquilibriumPhysicalEndpoint β
  have hV : (V : ℝ)=β^2*parisiEquilibriumSupportEndpoint β :=
    parisiEquilibriumPhysicalEndpoint_coe β hβ
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hβ0 : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  have hq : (V : ℝ)/β^2 ∈ Icc (0 : ℝ) 1 := by
    rw [hV,mul_div_cancel_left₀ _ (pow_ne_zero 2 hβ0)]
    exact ⟨hQ.1.le,hQ.2.le⟩
  let ha : ∀ z, cdf (parisiEquilibriumMeasure β : Measure ℝ) z∈Icc (0 : ℝ) 1 :=
    fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : cdf (parisiEquilibriumMeasure β : Measure ℝ) 1=1 :=
    supported_probability_cdf_one (parisiEquilibriumMeasure β) (parisiEquilibriumMeasure_upstream_spec β).1
  have H := (parisiEquilibrium_physicalBrownian_moments W β hβ ha h1
    (v := (V : ℝ)) ⟨V.coe_nonneg,hV.le⟩).2
  have HC : (∫ w,actualParisiFullCurvature β V (actualParisiFullScalarProcess W β V w)^2 ∂W.law)=1/β^2 := by
    simpa only [actualParisiFullCurvature,cdfTimeClamp_eq hq,actualParisiFullScalarProcess,
      actualParisiFullScalarDrift,finiteTemperatureCDFProcess,Real.toNNReal_coe] using H
  rw [actualParisiContinuationR_eq_full_process_moment W β hβ 0 (by simp)]
  simp only [Real.toNNReal_zero,add_zero]
  refine Eq.trans ?_ HC
  apply integral_congr_ae
  apply ae_of_all
  intro w
  change scalarDefect (actualParisiFullScalarProcess W β V w)^2 =
    actualParisiFullCurvature β (V : ℝ) (actualParisiFullScalarProcess W β V w)^2
  rw [actualParisiFullCurvature_eq_tanh_after_support β hβ _ _ hV.ge]
  rfl

end SKConstants

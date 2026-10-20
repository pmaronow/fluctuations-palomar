module
public import SKConstants.ScalarProcessParisiRDerivative
public import SKConstants.ScalarProcessParisiRho
public import SKConstants.ParisiSmoothCutoffs
public import SKConstants.ParisiFullRowSecondMoment

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullPosteriorProfile_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem scalarContinuationP_eq_hiddenFieldPath_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (F : Ω → ScalarContinuousPath T) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ), F ω t=B ⟨t,t.property.1⟩ ω) :
    scalarContinuationP ν T = ∫ u,
      scalarDefect (scalarSeedHiddenFieldPath T F u ⟨T,T.coe_nonneg,le_rfl⟩)
        ∂scalarSeedHiddenBrownianLaw ν P := by
  have hm : Measurable (fun u : ℝ × (Bool × Ω) =>
      scalarDefect (scalarSeedHiddenFieldPath T F u ⟨T,T.coe_nonneg,le_rfl⟩)) :=
    (measurable_scalarDefect.comp ((ContinuousMap.measurable_eval _).comp
      (measurable_scalarSeedHiddenFieldPath T F hFm)))
  have hi : Integrable (fun u : ℝ × (Bool × Ω) =>
      scalarDefect (scalarSeedHiddenFieldPath T F u ⟨T,T.coe_nonneg,le_rfl⟩))
      (scalarSeedHiddenBrownianLaw ν P) := Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ (fun u => norm_scalarDefect_le_one _))
  rw [scalarContinuationP_eq_actualAverage ν P B hB,scalarSeedHiddenBrownianLaw,
    Measure.integral_compProd hi]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  change scalarHiddenExpectedDefectReal P z B ((T : ℝ).toNNReal : ℝ) =
    ∫ u, scalarDefect (scalarSeedHiddenFieldPath T F (z,u) ⟨T,T.coe_nonneg,le_rfl⟩)
      ∂scalarHiddenBrownianLaw z P
  simp only [Real.toNNReal_coe,scalarHiddenExpectedDefectReal,scalarHiddenFieldReal]
  apply integral_congr_ae
  have hf := (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hF
  filter_upwards [hf] with u hu
  dsimp only [scalarSeedHiddenFieldPath,ContinuousMap.coe_mk]
  rw [hu ⟨T,T.coe_nonneg,le_rfl⟩]
  congr 3

theorem actualParisiContinuationP_eq_full_process_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) (hv : 0 ≤ v) :
    actualParisiContinuationP W β v = ∫ w,
      scalarDefect (actualParisiFullScalarProcess W β
        (parisiEquilibriumPhysicalEndpoint β+v.toNNReal) w) ∂W.law := by
  let T := v.toNNReal
  let t : Icc (0 : ℝ) (T : ℝ) := ⟨T,T.coe_nonneg,le_rfl⟩
  have hobs : Measurable (fun p : ℝ × ScalarContinuousPath T => scalarDefect (p.2 t)) :=
    (measurable_scalarDefect.comp ((ContinuousMap.measurable_eval t).comp measurable_snd))
  have hleft : Measurable (fun w =>
      (actualParisiPreContinuationField W β (parisiEquilibriumPhysicalEndpoint β) w,
        actualParisiPostEndpointPath W β T w)) :=
    (measurable_actualParisiPreContinuationField W β _).prodMk
      (measurable_boundedDriftRestartPath W _ _ _)
  have hright : Measurable (fun u : ℝ × (Bool × Ω) =>
      (u.1,scalarSeedHiddenFieldPath T (brownianFinitePath W T) u)) :=
    measurable_fst.prodMk (measurable_scalarSeedHiddenFieldPath T _ (measurable_brownianFinitePath W T))
  have he := congrArg (fun μ : Measure (ℝ × ScalarContinuousPath T) =>
      ∫ p,scalarDefect (p.2 t) ∂μ) (actualParisiEndpointSeed_post_hidden_jointLaw W β hβ T)
  rw [integral_map hleft.aemeasurable hobs.aestronglyMeasurable,
    integral_map hright.aemeasurable hobs.aestronglyMeasurable] at he
  have hr := scalarContinuationP_eq_hiddenFieldPath_moment (actualParisiEndpointSeedLaw W β)
    W.law W.B W.brownian.toIsPreBrownianReal T (brownianFinitePath W T)
    (measurable_brownianFinitePath W T) (brownianFinitePath_version W T)
  change scalarContinuationP (actualParisiEndpointSeedLaw W β) v = _
  rw [← Real.coe_toNNReal v hv,hr]
  refine he.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [actualParisiPostEndpointPath_version W β T] with w hw
  rw [hw t]
  simp only [Real.toNNReal_coe]
  congr 3

def actualParisiFullDefectMoment (W : BrownianSystem Ω) (β : ℝ) (t : ℝ) : ℝ :=
  ∫ w,scalarDefect (actualParisiFullScalarProcess W β t.toNNReal w) ∂W.law

theorem actualParisiFullDefectMoment_hasDerivWithinAt_right
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (s : ℝ≥0)
    (hs : β^2*parisiEquilibriumSupportEndpoint β ≤ (s : ℝ)) :
    HasDerivWithinAt (actualParisiFullDefectMoment W β)
      (-(∫ w,scalarDefect (actualParisiFullScalarProcess W β s w)^2 ∂W.law))
      (Ioi (s : ℝ)) s := by
  let F := staticTimeField ((s : ℝ)+1) scalarDefect boundedSmooth_scalarDefect
  have hbr : ∀ᵐ w ∂W.law,
      ContinuousWithinAt (fun r => (actualParisiFullScalarDrift β).pathDrift W r w) (Ioi (s : ℝ)) s :=
    (finiteTemperatureCDFDrift_path_right_continuous W β _ _ _).mono (fun w hw => hw s)
  have H := F.expected_hasDerivWithinAt_right (actualParisiFullScalarDrift β) W s (by linarith) hbr
  change HasDerivWithinAt (actualParisiFullDefectMoment W β) _ _ _ at H
  rw [←integral_neg]
  convert H using 1
  apply integral_congr_ae
  apply ae_of_all
  intro w
  dsimp only [F,TimeField.generator,staticTimeField]
  rw [actualParisiFullScalarDrift_eq_tanh_after_support β hβ _ hs]
  simpa only [scalarGenerator,actualParisiFullScalarProcess,zero_add,add_zero,mul_comm,
    add_comm,div_eq_mul_inv,Nat.cast_ofNat,one_mul] using
    (scalarGenerator_defect (actualParisiFullScalarProcess W β s w)).symm

theorem actualParisiContinuationP_eq_shifted_full_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) (hv : 0 ≤ v) :
    actualParisiContinuationP W β v = actualParisiFullDefectMoment W β
      ((parisiEquilibriumPhysicalEndpoint β : ℝ)+v) := by
  rw [actualParisiContinuationP_eq_full_process_moment W β hβ v hv]
  unfold actualParisiFullDefectMoment
  congr 1
  funext w
  have he : (((parisiEquilibriumPhysicalEndpoint β : ℝ)+v).toNNReal : ℝ≥0) =
      parisiEquilibriumPhysicalEndpoint β+v.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by positivity),NNReal.coe_add,Real.coe_toNNReal v hv]
  rw [he]

theorem actualParisiContinuationP_hasDerivWithinAt_right
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ) (hv : 0 ≤ v) :
    HasDerivWithinAt (actualParisiContinuationP W β) (-actualParisiContinuationR W β v)
      (Ioi v) v := by
  let V := parisiEquilibriumPhysicalEndpoint β
  let s : ℝ≥0 := V+v.toNNReal
  have hscoe : (s : ℝ)=(V : ℝ)+v := by simp only [s,NNReal.coe_add,Real.coe_toNNReal v hv]
  have hs : β^2*parisiEquilibriumSupportEndpoint β ≤ (s : ℝ) := by
    rw [hscoe,parisiEquilibriumPhysicalEndpoint_coe β hβ]
    linarith
  have H := actualParisiFullDefectMoment_hasDerivWithinAt_right W β hβ s hs
  rw [hscoe] at H
  have hid : HasDerivWithinAt (fun x : ℝ => (V : ℝ)+x) 1 (Ioi v) v :=
    ((hasDerivAt_id v).const_add (V : ℝ)).hasDerivWithinAt
  have hc := H.comp v hid (by
    intro x hx
    change v < x at hx
    change (V : ℝ)+v < (V : ℝ)+x
    linarith)
  have he : (fun x : ℝ => actualParisiFullDefectMoment W β ((V : ℝ)+x)) =ᶠ[nhdsWithin v (Ioi v)]
      actualParisiContinuationP W β := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (actualParisiContinuationP_eq_shifted_full_moment W β hβ x (hv.trans hx.le)).symm
  have hc' := hc.congr_of_eventuallyEq he.symm
    (actualParisiContinuationP_eq_shifted_full_moment W β hβ v hv)
  simpa only [actualParisiContinuationR_eq_full_process_moment W β hβ v hv,mul_one] using hc'

theorem actualParisiContinuationP_drop_ge
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) :
    actualParisiContinuationR W β T*(T-S) ≤
      actualParisiContinuationP W β S-actualParisiContinuationP W β T := by
  let p := actualParisiContinuationP W β
  let r := actualParisiContinuationR W β
  let B := fun x => p S-r T*(x-S)
  have HD : ∀ x ∈ Ico S T,HasDerivWithinAt p (-r x) (Ici x) x := fun x hx =>
    (actualParisiContinuationP_hasDerivWithinAt_right W β hβ x (hS.trans hx.1)).Ici_of_Ioi
  have HB : ∀ x ∈ Ico S T,HasDerivWithinAt B (-r T) (Ici x) x := by
    intro x hx
    have HH := ((hasDerivWithinAt_const x (Ici x) (p S)).sub
      (((hasDerivAt_id x).sub_const S).hasDerivWithinAt.const_mul (r T)))
    simp only [zero_sub,mul_one] at HH
    convert HH using 1
    funext y
    simp only [B,Pi.sub_apply,id_eq]
  have H := image_le_of_deriv_right_le_deriv_boundary
    (continuous_actualParisiContinuationP W β).continuousOn HD
    (B := B) (B' := fun _ => -r T) (by simp only [B,sub_self,mul_zero,sub_zero,p]; exact le_rfl)
    ((continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn) HB
    (fun x hx => neg_le_neg (actualParisiContinuationR_antitone W β hβ hx.2.le))
  have H' := H ⟨hST,le_rfl⟩
  dsimp [B,p,r] at H'
  linarith

theorem actualParisiContinuationP_strict_drop
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ) (hS : 0 ≤ S) (hST : S < T) :
    0 < actualParisiContinuationP W β S-actualParisiContinuationP W β T :=
  lt_of_lt_of_le (mul_pos (actualParisiContinuationR_pos W β T) (sub_pos.mpr hST))
    (actualParisiContinuationP_drop_ge W β hβ S T hS hST.le)

def actualParisiFullOverlap (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0) : ℝ :=
  ∫ w,(actualParisiMagnetizationObservable W β t w)^2 ∂W.law

theorem actualParisiFullOverlap_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) :
    actualParisiFullOverlap W β t=(t:ℝ)/β^2 := by
  have hb : 0 < β^2 := sq_pos_of_pos (zero_lt_one.trans hβ)
  have hq : (t:ℝ)/β^2 ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg t.coe_nonneg hb.le,?_⟩
    apply (div_le_iff₀ hb).mpr
    have H := NNReal.coe_le_coe.mpr ht
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ] at H
    nlinarith [(parisiEquilibriumSupportEndpoint_spec β hβ).1.2]
  let ha : ∀ z,cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1 :=
    fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1 :=
    supported_probability_cdf_one (parisiEquilibriumMeasure β) (parisiEquilibriumMeasure_upstream_spec β).1
  have hv : (t:ℝ)∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β) := by
    refine ⟨t.coe_nonneg,?_⟩
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr ht
  have H := (parisiEquilibrium_physicalBrownian_moments W β hβ ha h1 hv).1
  simpa only [actualParisiFullOverlap,actualParisiMagnetizationObservable,actualParisiFullMagnetization,
    cdfTimeClamp_eq hq,actualParisiFullScalarProcess,actualParisiFullScalarDrift,
    finiteTemperatureCDFProcess,Real.toNNReal_coe] using H

theorem actualParisiFullOverlap_post (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ≥0) :
    actualParisiFullOverlap W β (parisiEquilibriumPhysicalEndpoint β+v)=
      1-actualParisiContinuationP W β v := by
  let t := parisiEquilibriumPhysicalEndpoint β+v
  have ht : β^2*parisiEquilibriumSupportEndpoint β ≤ (t:ℝ) := by
    simp only [t,NNReal.coe_add,parisiEquilibriumPhysicalEndpoint_coe β hβ]
    exact le_add_of_nonneg_right v.coe_nonneg
  rw [actualParisiContinuationP_eq_full_process_moment W β hβ v v.coe_nonneg]
  simp only [Real.toNNReal_coe]
  have hi : Integrable (fun w => (Real.tanh (actualParisiFullScalarProcess W β t w))^2) W.law := by
    apply Integrable.of_bound
      ((measurable_scalarTanh.comp (measurable_actualParisiPreContinuationField W β t)).pow_const 2).aestronglyMeasurable
      1 (ae_of_all _ (fun w => by
        rw [norm_pow]
        simpa using pow_le_pow_left₀ (norm_nonneg _) (norm_tanh_le_one _) 2))
  have he : actualParisiMagnetizationObservable W β t=
      fun w => Real.tanh (actualParisiFullScalarProcess W β t w) := by
    funext w
    exact congrFun (actualParisiFullMagnetization_eq_tanh_after_support β hβ t ht) _
  change (∫ w,(actualParisiMagnetizationObservable W β t w)^2 ∂W.law)=_
  rw [he]
  change (∫ w,(Real.tanh (actualParisiFullScalarProcess W β t w))^2 ∂W.law)=
    1-∫ w,scalarDefect (actualParisiFullScalarProcess W β t w) ∂W.law
  simp only [scalarDefect]
  rw [integral_sub (integrable_const 1) hi,integral_const,probReal_univ,one_smul]
  ring

lemma actualParisiFullOverlap_pre_drop_ge
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0) (hST : S ≤ T)
    (hTV : T ≤ parisiEquilibriumPhysicalEndpoint β) (v : ℝ) :
    actualParisiContinuationR W β v*((T:ℝ)-(S:ℝ)) ≤
      actualParisiFullOverlap W β T-actualParisiFullOverlap W β S := by
  rw [actualParisiFullOverlap_pre W β hβ T hTV,
    actualParisiFullOverlap_pre W β hβ S (hST.trans hTV)]
  have H := mul_le_mul_of_nonneg_right
    (actualParisiContinuationR_le_inverse_beta_sq W β hβ v)
    (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hST))
  exact H.trans_eq (by ring)

lemma actualParisiFullOverlap_post_drop_ge
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0)
    (hVS : parisiEquilibriumPhysicalEndpoint β ≤ S) (hST : S ≤ T) (v : ℝ)
    (hTv : (T:ℝ)-(parisiEquilibriumPhysicalEndpoint β:ℝ) ≤ v) :
    actualParisiContinuationR W β v*((T:ℝ)-(S:ℝ)) ≤
      actualParisiFullOverlap W β T-actualParisiFullOverlap W β S := by
  let V := parisiEquilibriumPhysicalEndpoint β
  have hs : V+(S-V)=S := add_tsub_cancel_of_le hVS
  have ht : V+(T-V)=T := add_tsub_cancel_of_le (hVS.trans hST)
  have hsc : ((S-V:ℝ≥0):ℝ)=(S:ℝ)-(V:ℝ) := NNReal.coe_sub hVS
  have htc : ((T-V:ℝ≥0):ℝ)=(T:ℝ)-(V:ℝ) := NNReal.coe_sub (hVS.trans hST)
  have H := actualParisiContinuationP_drop_ge W β hβ ((S-V:ℝ≥0):ℝ) ((T-V:ℝ≥0):ℝ)
    (S-V).coe_nonneg (NNReal.coe_le_coe.mpr (tsub_le_tsub_right hST V))
  have HR := actualParisiContinuationR_antitone W β hβ
    (show ((T-V:ℝ≥0):ℝ) ≤ v by simpa only [htc] using hTv)
  have HB := mul_le_mul_of_nonneg_right HR (sub_nonneg.mpr
    (show ((S-V:ℝ≥0):ℝ) ≤ ((T-V:ℝ≥0):ℝ) from NNReal.coe_le_coe.mpr (tsub_le_tsub_right hST V)))
  rw [← hs,← ht,actualParisiFullOverlap_post W β hβ (S-V),
    actualParisiFullOverlap_post W β hβ (T-V)]
  simp only [NNReal.coe_add,hsc,htc] at HB H ⊢
  linarith

theorem actualParisiFullOverlap_drop_ge
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T H : ℝ≥0)
    (hST : S ≤ T) (hTH : T ≤ H) :
    actualParisiContinuationR W β ((H-parisiEquilibriumPhysicalEndpoint β:ℝ≥0):ℝ)*((T:ℝ)-(S:ℝ)) ≤
      actualParisiFullOverlap W β T-actualParisiFullOverlap W β S := by
  let V := parisiEquilibriumPhysicalEndpoint β
  let v : ℝ := ((H-V:ℝ≥0):ℝ)
  have hv (U : ℝ≥0) (hVU : V ≤ U) (hUH : U ≤ H) : (U:ℝ)-(V:ℝ) ≤ v := by
    dsimp only [v]
    rw [NNReal.coe_sub (hVU.trans hUH)]
    exact sub_le_sub_right (NNReal.coe_le_coe.mpr hUH) _
  by_cases hTV : T ≤ V
  · exact actualParisiFullOverlap_pre_drop_ge W β hβ S T hST hTV v
  have hVT : V ≤ T := (lt_of_not_ge hTV).le
  by_cases hVS : V ≤ S
  · exact actualParisiFullOverlap_post_drop_ge W β hβ S T hVS hST v (hv T hVT hTH)
  have hSV : S ≤ V := (lt_of_not_ge hVS).le
  have HA := actualParisiFullOverlap_pre_drop_ge W β hβ S V hSV le_rfl v
  have HB := actualParisiFullOverlap_post_drop_ge W β hβ V T le_rfl hVT v (hv T hVT hTH)
  dsimp only [v,V] at HA HB ⊢
  nlinarith

theorem actualParisiFullOverlap_strict_drop
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0) (hST : S < T) :
    0 < actualParisiFullOverlap W β T-actualParisiFullOverlap W β S := by
  exact lt_of_lt_of_le
    (mul_pos (actualParisiContinuationR_pos W β _) (sub_pos.mpr (NNReal.coe_lt_coe.mpr hST)))
    (actualParisiFullOverlap_drop_ge W β hβ S T T hST.le le_rfl)

end SKConstants

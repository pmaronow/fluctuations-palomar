module
public import SKConstants.ParisiFullRowMGF
public import SKConstants.ParisiTanhDensityContinuation

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullMartingale_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

lemma boundedDrift_observable_martingale_test
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) (a v : ℝ≥0)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfB : ∀ x, |f x| ≤ 1) (hgB : ∀ x, |g x| ≤ 1)
    (hmean : ∀ past : ScalarContinuousPath a,
      (∫ w,g (boundedDriftRestartCallback b a v (past,brownianFinitePath W v w)
        ⟨v,v.coe_nonneg,le_rfl⟩)-f (past ⟨a,a.coe_nonneg,le_rfl⟩) ∂W.law)=0)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w,F (boundedDriftPastPath W b a w)*
      (g (b.solution W.driver (a+v) w)-f (b.solution W.driver a w)) ∂W.law)=0 := by
  let H : ScalarContinuousPath a × ScalarContinuousPath v → ℝ := fun p =>
    F p.1*(g (p.2 ⟨v,v.coe_nonneg,le_rfl⟩)-f (p.1 ⟨a,a.coe_nonneg,le_rfl⟩))
  have hH : Measurable H := (hF.comp measurable_fst).mul
    ((hg.comp ((ContinuousMap.measurable_eval _).comp measurable_snd)).sub
      (hf.comp ((ContinuousMap.measurable_eval _).comp measurable_fst)))
  have hB (p : ScalarContinuousPath a × ScalarContinuousPath v) : |H p| ≤ 2*C := by
    dsimp only [H]
    rw [abs_mul]
    have hdiff : |g (p.2 ⟨v,v.coe_nonneg,le_rfl⟩)-f (p.1 ⟨a,a.coe_nonneg,le_rfl⟩)| ≤ 2 := by
      have HA := abs_le.mp (hgB (p.2 ⟨v,v.coe_nonneg,le_rfl⟩))
      have HB := abs_le.mp (hfB (p.1 ⟨a,a.coe_nonneg,le_rfl⟩))
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    nlinarith [mul_le_mul_of_nonneg_left hdiff (abs_nonneg (F p.1)),hFC p.1]
  have he := boundedDrift_restart_integral W b a v H hH _ hB
  have hv' : (∫ w,F (boundedDriftPastPath W b a w)*
      (g (b.solution W.driver (a+v) w)-f (b.solution W.driver a w)) ∂W.law)=
      ∫ w,H (boundedDriftPastPath W b a w,boundedDriftRestartPath W b a v w) ∂W.law := by
    apply integral_congr_ae
    filter_upwards [boundedDriftPastPath_version W b a,boundedDriftRestartPath_version W b a v]
      with w hp hr
    simp only [H,hp,hr]
    rfl
  rw [hv',he]
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro past
  change (∫ w,F past*(g (boundedDriftRestartCallback b a v
    (past,brownianFinitePath W v w) ⟨v,v.coe_nonneg,le_rfl⟩)-
      f (past ⟨a,a.coe_nonneg,le_rfl⟩)) ∂W.law)=0
  rw [integral_const_mul,hmean,mul_zero]

lemma actualParisiFullProcess_pre_martingale_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (hav : a+v ≤ parisiEquilibriumPhysicalEndpoint β)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w,F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*
      (actualParisiFullMagnetization β (a+v) (actualParisiFullScalarProcess W β (a+v) w)-
        actualParisiFullMagnetization β a (actualParisiFullScalarProcess W β a w)) ∂W.law)=0 := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  have ha : ∀ z,α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1=1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hb : β≠0 := (zero_lt_one.trans hβ).ne'
  let T := (parisiEquilibriumSupportEndpoint β+1)/2
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hT0 : 0≤T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T<1 := by dsimp [T]; linarith [hQ.2]
  have hQT : parisiEquilibriumSupportEndpoint β<T := by dsimp [T]; linarith [hQ.2]
  have htime : ((a:ℝ)+(v:ℝ))/β^2<T := by
    have H : ((a+v:ℝ≥0):ℝ) ≤ β^2*parisiEquilibriumSupportEndpoint β := by
      simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr hav
    have HD : ((a:ℝ)+(v:ℝ))/β^2 ≤ parisiEquilibriumSupportEndpoint β :=
      (div_le_iff₀ (sq_pos_of_ne_zero hb)).mpr (by simpa only [NNReal.coe_add,mul_comm] using H)
    exact HD.trans_lt hQT
  have haV : a ≤ parisiEquilibriumPhysicalEndpoint β := (le_add_of_nonneg_right bot_le).trans hav
  apply boundedDrift_observable_martingale_test W (actualParisiFullScalarDrift β) a v
    (actualParisiFullMagnetization β a) (actualParisiFullMagnetization β (a+v))
    ((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable
    ((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable
    (fun x => (actualParisiFullMagnetization_curvature_bounds β a x).1)
    (fun x => (actualParisiFullMagnetization_curvature_bounds β (a+v) x).1)
    _ F hF C hFC
  intro past
  have H := physicalCDFGradient_restart_integral_eq_zero W β α ha h1 hb hT0 hT1
    a a.coe_nonneg (past ⟨a,a.coe_nonneg,le_rfl⟩) v htime
  have he1 : actualParisiFullMagnetization β ((a:ℝ)+(v:ℝ)) =
      compactCDFJet β α T 0 (((a:ℝ)+(v:ℝ))/β^2) := by
    funext x
    simpa only [NNReal.coe_add] using actualParisiFullMagnetization_eq_compact_before_support
      β hβ hQT hT1.le (a+v) hav x
  have he0 : actualParisiFullMagnetization β (a:ℝ) = compactCDFJet β α T 0 ((a:ℝ)/β^2) :=
    funext (actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le a haV)
  rw [he1,he0]
  refine (integral_congr_ae ?_).trans H
  filter_upwards [boundedDriftRestartCallback_fresh_version W (actualParisiFullScalarDrift β) a v past]
    with w hw
  rw [hw]
  rfl

lemma scalarTanhPicard_endpoint_mean (W : BrownianSystem Ω) (z : ℝ) (v : ℝ≥0) :
    (∫ w,Real.tanh (scalarForwardPicardPath scalarTanhDrift v
      (z,brownianFinitePath W v w) ⟨v,v.coe_nonneg,le_rfl⟩) ∂W.law)=Real.tanh z := by
  let F := brownianFinitePath W v
  let J : ScalarContinuousPath v → ScalarContinuousPath v :=
    fun p => scalarForwardPicardPath scalarTanhDrift v (z,p)
  let H : ScalarContinuousPath v → ℝ := fun p => Real.tanh (p ⟨v,v.coe_nonneg,le_rfl⟩)
  have hJ : Measurable J := (measurable_scalarForwardPicardPath scalarTanhDrift v).comp
    (measurable_const.prodMk measurable_id)
  have hH : Measurable H := measurable_scalarTanh.comp (ContinuousMap.measurable_eval _)
  have hl := scalarForwardPicardPath_actual_hidden_field_law_joint_version W.law W.B W.brownian
    v z F (measurable_brownianFinitePath W v) (brownianFinitePath_version W v)
  have hl' : W.law.map (J ∘ F) = (scalarHiddenBrownianLaw z W.law).map
      (fun u => scalarSeedHiddenFieldPath v F (z,u)) := by
    rw [←Measure.map_map hJ (measurable_brownianFinitePath W v)]
    exact hl
  have hm : Measurable (fun u : Bool × Ω => scalarSeedHiddenFieldPath v F (z,u)) :=
    (measurable_scalarSeedHiddenFieldPath v F (measurable_brownianFinitePath W v)).comp
      (measurable_const.prodMk measurable_id)
  change (∫ w,H (J (F w)) ∂W.law)=_
  rw [show (∫ w,H (J (F w)) ∂W.law) = ∫ p,H p ∂W.law.map (J ∘ F) from
    (integral_map (hJ.comp (measurable_brownianFinitePath W v)).aemeasurable hH.aestronglyMeasurable).symm,
    hl',integral_map hm.aemeasurable hH.aestronglyMeasurable]
  have hv : (fun u : Bool × Ω => H (scalarSeedHiddenFieldPath v F (z,u))) =ᵐ[
      scalarHiddenBrownianLaw z W.law] (fun u => Real.tanh (scalarHiddenContinuousField z W.B v u)) := by
    have hf := (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := W.law)).quasiMeasurePreserving.ae
      (brownianFinitePath_version W v)
    filter_upwards [hf] with u hu
    dsimp only [H,scalarSeedHiddenFieldPath,ContinuousMap.coe_mk]
    rw [hu ⟨v,v.coe_nonneg,le_rfl⟩]
    rfl
  rw [integral_congr_ae hv]
  exact (integral_scalarHiddenContinuousField_comp W.brownian.toIsPreBrownianReal z v
    Real.tanh measurable_scalarTanh).trans (integral_tanh_scalarTransitionKernel z v)

lemma actualParisiRestartCallback_eq_tanh_after_support
    (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0) (ha : parisiEquilibriumPhysicalEndpoint β ≤ a)
    (p : ScalarContinuousPath a × ScalarContinuousPath v) :
    boundedDriftRestartCallback (actualParisiFullScalarDrift β) a v p =
      scalarForwardPicardPath scalarTanhDrift v (p.1 ⟨a,a.coe_nonneg,le_rfl⟩,p.2) := by
  ext t
  apply SKConstants.BoundedLipschitzDrift.solution_congr_nonneg_drift
  intro r hr x
  change (actualParisiFullScalarDrift β).f ((a:ℝ)+r) (0+x)=Real.tanh x
  rw [zero_add]
  apply congrFun (actualParisiFullScalarDrift_eq_tanh_after_support β hβ _ _) x
  have H := NNReal.coe_le_coe.mpr ha
  rw [parisiEquilibriumPhysicalEndpoint_coe β hβ] at H
  linarith

lemma actualParisiFullProcess_post_martingale_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (ha : parisiEquilibriumPhysicalEndpoint β ≤ a)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w,F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*
      (actualParisiFullMagnetization β (a+v) (actualParisiFullScalarProcess W β (a+v) w)-
        actualParisiFullMagnetization β a (actualParisiFullScalarProcess W β a w)) ∂W.law)=0 := by
  have hafter (t : ℝ≥0) (ht : parisiEquilibriumPhysicalEndpoint β ≤ t) :
      β^2*parisiEquilibriumSupportEndpoint β ≤ (t:ℝ) := by
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr ht
  rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ _ (hafter _ ha),
    actualParisiFullMagnetization_eq_tanh_after_support β hβ ((a:ℝ)+(v:ℝ))
      (by simpa only [NNReal.coe_add] using hafter (a+v) (ha.trans (le_add_of_nonneg_right bot_le)))]
  apply boundedDrift_observable_martingale_test W (actualParisiFullScalarDrift β) a v
    Real.tanh Real.tanh measurable_scalarTanh measurable_scalarTanh
    (fun x => (Real.abs_tanh_lt_one x).le) (fun x => (Real.abs_tanh_lt_one x).le)
    _ F hF C hFC
  intro past
  simp_rw [actualParisiRestartCallback_eq_tanh_after_support β hβ a v ha]
  have hi : Integrable (fun w => Real.tanh (scalarForwardPicardPath scalarTanhDrift v
      (past ⟨a,a.coe_nonneg,le_rfl⟩,brownianFinitePath W v w) ⟨v,v.coe_nonneg,le_rfl⟩)) W.law := by
    apply Integrable.of_bound _ 1 (ae_of_all _ (fun w => norm_tanh_le_one _))
    exact (measurable_scalarTanh.comp ((ContinuousMap.measurable_eval _).comp
      ((measurable_scalarForwardPicardPath scalarTanhDrift v).comp
        (measurable_const.prodMk (measurable_brownianFinitePath W v))))).aestronglyMeasurable
  rw [integral_sub hi (integrable_const _),scalarTanhPicard_endpoint_mean,
    integral_const,probReal_univ,one_smul,sub_self]

def scalarContinuousPathRestrict (a b : ℝ≥0) (hab : a ≤ b)
    (p : ScalarContinuousPath b) : ScalarContinuousPath a :=
  ⟨fun t => p ⟨t,t.property.1,t.property.2.trans hab⟩,
    p.continuous.comp (by fun_prop)⟩

lemma measurable_scalarContinuousPathRestrict (a b : ℝ≥0) (hab : a ≤ b) :
    Measurable (scalarContinuousPathRestrict a b hab) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ContinuousMap.measurable_eval (⟨t,t.property.1,t.property.2.trans hab⟩ : Icc (0:ℝ) (b:ℝ))

lemma boundedDriftPastPath_restrict (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (a T : ℝ≥0) (haT : a ≤ T) :
    (fun w => scalarContinuousPathRestrict a T haT (boundedDriftPastPath W b T w)) =ᵐ[W.law]
      boundedDriftPastPath W b a := by
  filter_upwards [boundedDriftPastPath_version W b T,boundedDriftPastPath_version W b a]
    with w hT ha
  ext t
  exact (hT ⟨t,t.property.1,t.property.2.trans haT⟩).trans (ha t).symm

theorem actualParisiFullProcess_martingale_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w,F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*
      (actualParisiFullMagnetization β (a+v) (actualParisiFullScalarProcess W β (a+v) w)-
        actualParisiFullMagnetization β a (actualParisiFullScalarProcess W β a w)) ∂W.law)=0 := by
  let V := parisiEquilibriumPhysicalEndpoint β
  by_cases hav : a+v ≤ V
  · exact actualParisiFullProcess_pre_martingale_test W β hβ a v hav F hF C hFC
  by_cases ha : V ≤ a
  · exact actualParisiFullProcess_post_martingale_test W β hβ a v ha F hF C hFC
  have haV : a ≤ V := (lt_of_not_ge ha).le
  have hVa : V ≤ a+v := (lt_of_not_ge hav).le
  let d := V-a
  let e := a+v-V
  have had : a+d=V := by dsimp [d]; exact add_tsub_cancel_of_le haV
  have hVe : V+e=a+v := by dsimp [e]; exact add_tsub_cancel_of_le hVa
  let b := actualParisiFullScalarDrift β
  let M : ℝ≥0 → Ω → ℝ := fun t w =>
    actualParisiFullMagnetization β t (actualParisiFullScalarProcess W β t w)
  have Hpre := actualParisiFullProcess_pre_martingale_test W β hβ a d
    (by rw [had]) F hF C hFC
  have hadr : (a:ℝ)+(d:ℝ)=(V:ℝ) := by exact_mod_cast had
  rw [had,hadr] at Hpre
  let G := F ∘ scalarContinuousPathRestrict a V haV
  have hG : Measurable G := hF.comp (measurable_scalarContinuousPathRestrict a V haV)
  have Hpost := actualParisiFullProcess_post_martingale_test W β hβ V e le_rfl
    G hG C (fun p => hFC _)
  have hVer : (V:ℝ)+(e:ℝ)=(a:ℝ)+(v:ℝ) := by exact_mod_cast hVe
  rw [hVe,hVer] at Hpost
  have Hp : (∫ w,F (boundedDriftPastPath W b a w)*(M (a+v) w-M V w) ∂W.law)=0 := by
    refine (integral_congr_ae ?_).trans Hpost
    filter_upwards [boundedDriftPastPath_restrict W b a V haV] with w hw
    dsimp only [G,Function.comp_apply]
    rw [hw]
    rfl
  have hm (t : ℝ≥0) : Measurable (M t) := by
    change Measurable (fun w => actualParisiFullMagnetization β t (actualParisiFullScalarProcess W β t w))
    exact ((continuous_actualParisiFullMagnetization β).comp
      ((continuous_const : Continuous (fun _ : ℝ => (t:ℝ))).prodMk continuous_id)).measurable.comp
        (measurable_actualParisiPreContinuationField W β t)
  have hi (x y : ℝ≥0) : Integrable (fun w => F (boundedDriftPastPath W b a w)*
      (M x w-M y w)) W.law := by
    apply Integrable.of_bound ((hF.comp (measurable_boundedDriftPastPath W b a)).mul
      ((hm x).sub (hm y))).aestronglyMeasurable (2*C)
    apply ae_of_all
    intro w
    simp only [Function.comp_def,Pi.mul_apply,Pi.sub_apply,Real.norm_eq_abs,abs_mul]
    have hA := abs_le.mp (actualParisiFullMagnetization_curvature_bounds β x (actualParisiFullScalarProcess W β x w)).1
    have hB := abs_le.mp (actualParisiFullMagnetization_curvature_bounds β y (actualParisiFullScalarProcess W β y w)).1
    have hdiff : |M x w-M y w| ≤ 2 := by
      dsimp only [M]
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    nlinarith [mul_le_mul_of_nonneg_left hdiff (abs_nonneg (F (boundedDriftPastPath W b a w))),
      hFC (boundedDriftPastPath W b a w)]
  have Hsum := integral_add (hi (a+v) V) (hi V a)
  have heq : (fun w => F (boundedDriftPastPath W b a w)*(M (a+v) w-M a w))=
      fun w => F (boundedDriftPastPath W b a w)*(M (a+v) w-M V w)+
        F (boundedDriftPastPath W b a w)*(M V w-M a w) := by
    funext w
    ring
  change (∫ w,F (boundedDriftPastPath W b a w)*(M (a+v) w-M a w) ∂W.law)=0
  rw [heq,Hsum,Hp,Hpre,add_zero]

end SKConstants

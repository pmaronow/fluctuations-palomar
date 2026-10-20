module
public import SKConstants.ParisiFullMartingale

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullConditionalMGF_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem boundedDrift_observable_predictable_mgf_test
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) (a v : ℝ≥0)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfB : ∀x,|f x|≤1) (hgB : ∀x,|g x|≤1)
    (hmgf : ∀past : ScalarContinuousPath a,∀θ : ℝ,
      (∫w,Real.exp (θ*(g (boundedDriftRestartCallback b a v (past,brownianFinitePath W v w)
        ⟨v,v.coe_nonneg,le_rfl⟩)-f (past ⟨a,a.coe_nonneg,le_rfl⟩))) ∂W.law)≤Real.exp (θ^2*(v:ℝ)/2))
    (F A : ScalarContinuousPath a → ℝ) (hF : Measurable F) (hA : Measurable A)
    (hF0 : ∀p,0≤F p) (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (hFC : ∀p,F p≤C) (hAD : ∀p,|A p|≤D) (θ : ℝ) :
    (∫w,F (boundedDriftPastPath W b a w)*Real.exp
      (θ*A (boundedDriftPastPath W b a w)*(g (b.solution W.driver (a+v) w)-f (b.solution W.driver a w))) ∂W.law)≤
      ∫w,F (boundedDriftPastPath W b a w)*Real.exp
        (θ^2*A (boundedDriftPastPath W b a w)^2*(v:ℝ)/2) ∂W.law := by
  let H : ScalarContinuousPath a × ScalarContinuousPath v → ℝ := fun p =>
    F p.1*Real.exp (θ*A p.1*(g (p.2 ⟨v,v.coe_nonneg,le_rfl⟩)-f (p.1 ⟨a,a.coe_nonneg,le_rfl⟩)))
  have hH : Measurable H := (hF.comp measurable_fst).mul
    (Real.continuous_exp.measurable.comp (((hA.comp measurable_fst).const_mul θ).mul
      ((hg.comp ((ContinuousMap.measurable_eval _).comp measurable_snd)).sub
        (hf.comp ((ContinuousMap.measurable_eval _).comp measurable_fst)))))
  have hHB (p : ScalarContinuousPath a × ScalarContinuousPath v) : |H p|≤C*Real.exp (2* |θ| *D) := by
    have hdiff : |g (p.2 ⟨v,v.coe_nonneg,le_rfl⟩)-f (p.1 ⟨a,a.coe_nonneg,le_rfl⟩)|≤2 := by
      have HA := abs_le.mp (hgB (p.2 ⟨v,v.coe_nonneg,le_rfl⟩))
      have HB := abs_le.mp (hfB (p.1 ⟨a,a.coe_nonneg,le_rfl⟩))
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    dsimp only [H]
    rw [abs_mul,abs_of_nonneg (hF0 _),abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul (hFC p.1) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC
    calc θ*A p.1*_≤|θ*A p.1*_| := le_abs_self _
      _=|θ| * |A p.1| * |_| := by rw [abs_mul,abs_mul]
      _≤|θ| *D*2 := mul_le_mul
        (mul_le_mul_of_nonneg_left (hAD _) (abs_nonneg _)) hdiff (abs_nonneg _) (by positivity)
      _=2* |θ| *D := by ring
  have he := boundedDrift_restart_integral W b a v H hH _ hHB
  have hactual : (∫w,F (boundedDriftPastPath W b a w)*Real.exp
      (θ*A (boundedDriftPastPath W b a w)*(g (b.solution W.driver (a+v) w)-f (b.solution W.driver a w))) ∂W.law)=
      ∫w,H (boundedDriftPastPath W b a w,boundedDriftRestartPath W b a v w) ∂W.law := by
    apply integral_congr_ae
    filter_upwards [boundedDriftPastPath_version W b a,boundedDriftRestartPath_version W b a v] with w hp hr
    simp only [H,hp,hr]
    rfl
  let R : ScalarContinuousPath a → ℝ := fun p => F p*Real.exp (θ^2*A p^2*(v:ℝ)/2)
  have hR : Measurable R := hF.mul (Real.continuous_exp.measurable.comp
    ((((hA.pow_const 2).const_mul (θ^2)).mul_const (v:ℝ)).div_const 2))
  have hRi : Integrable R (W.law.map (boundedDriftPastPath W b a)) := by
    apply Integrable.of_bound hR.aestronglyMeasurable (C*Real.exp (θ^2*D^2*(v:ℝ)/2))
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs,show |R p|=R p from abs_of_nonneg (mul_nonneg (hF0 p) (Real.exp_pos _).le)]
    apply mul_le_mul (hFC _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC
    have HA := abs_le.mp (hAD p)
    have HAsq : A p^2≤D^2 := by nlinarith
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HAsq (sq_nonneg θ)) v.coe_nonneg) (by positivity)
  rw [hactual,he]
  calc
    _≤∫past,R past ∂W.law.map (boundedDriftPastPath W b a) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun past => integral_nonneg (fun w => mul_nonneg (hF0 _) (Real.exp_pos _).le))
      · exact hRi
      · apply ae_of_all
        intro past
        change (∫w,F past*Real.exp (θ*A past*_) ∂W.law)≤R past
        rw [integral_const_mul]
        have Hm := hmgf past (θ*A past)
        have Hθ : (θ*A past)^2*(v:ℝ)/2=θ^2*A past^2*(v:ℝ)/2 := by ring
        rw [Hθ] at Hm
        exact mul_le_mul_of_nonneg_left Hm (hF0 past)
    _=_ := integral_map (measurable_boundedDriftPastPath W b a).aemeasurable hR.aestronglyMeasurable

lemma actualParisiFullRestart_pre_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (a v : ℝ≥0) (hav : a+v≤parisiEquilibriumPhysicalEndpoint β)
    (past : ScalarContinuousPath a) (θ : ℝ) :
    (∫w,Real.exp (θ*(actualParisiFullMagnetization β (a+v)
      (boundedDriftRestartCallback (actualParisiFullScalarDrift β) a v (past,brownianFinitePath W v w)
        ⟨v,v.coe_nonneg,le_rfl⟩)-actualParisiFullMagnetization β a (past ⟨a,a.coe_nonneg,le_rfl⟩))) ∂W.law)≤
      Real.exp (θ^2*(v:ℝ)/2) := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  have ha : ∀z,α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1=1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hb : β≠0 := (zero_lt_one.trans hβ).ne'
  let T := (parisiEquilibriumSupportEndpoint β+1)/2
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hT0 : 0≤T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T<1 := by dsimp [T]; linarith [hQ.2]
  have hQT : parisiEquilibriumSupportEndpoint β<T := by dsimp [T]; linarith [hQ.2]
  have htime : ((a:ℝ)+(v:ℝ))/β^2<T := by
    have H : ((a+v:ℝ≥0):ℝ)≤β^2*parisiEquilibriumSupportEndpoint β := by
      simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr hav
    have HD : ((a:ℝ)+(v:ℝ))/β^2≤parisiEquilibriumSupportEndpoint β :=
      (div_le_iff₀ (sq_pos_of_ne_zero hb)).mpr (by simpa only [NNReal.coe_add,mul_comm] using H)
    exact HD.trans_lt hQT
  have haV : a≤parisiEquilibriumPhysicalEndpoint β := (le_add_of_nonneg_right bot_le).trans hav
  have he1 : actualParisiFullMagnetization β ((a:ℝ)+(v:ℝ))=
      compactCDFJet β α T 0 (((a:ℝ)+(v:ℝ))/β^2) := by
    funext x
    simpa only [NNReal.coe_add] using actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le (a+v) hav x
  have he0 : actualParisiFullMagnetization β (a:ℝ)=compactCDFJet β α T 0 ((a:ℝ)/β^2) :=
    funext (actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le a haV)
  have H := physicalCDFGradient_restart_mgf W β α ha h1 hb hT0 hT1 a a.coe_nonneg
    (past ⟨a,a.coe_nonneg,le_rfl⟩) v htime θ
  rw [he1,he0]
  refine (integral_congr_ae ?_).trans_le H
  filter_upwards [boundedDriftRestartCallback_fresh_version W (actualParisiFullScalarDrift β) a v past] with w hw
  rw [hw]
  rfl

lemma actualParisiFullProcess_pre_predictable_mgf_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) (a v : ℝ≥0)
    (hav : a+v≤parisiEquilibriumPhysicalEndpoint β)
    (F A : ScalarContinuousPath a → ℝ) (hF : Measurable F) (hA : Measurable A)
    (hF0 : ∀p,0≤F p) (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (hFC : ∀p,F p≤C) (hAD : ∀p,|A p|≤D) (θ : ℝ) :
    (∫w,F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*Real.exp
      (θ*A (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*
        (actualParisiFullMagnetization β (a+v) (actualParisiFullScalarProcess W β (a+v) w)-
          actualParisiFullMagnetization β a (actualParisiFullScalarProcess W β a w))) ∂W.law)≤
      ∫w,F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)*Real.exp
        (θ^2*A (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w)^2*(v:ℝ)/2) ∂W.law := by
  apply boundedDrift_observable_predictable_mgf_test W (actualParisiFullScalarDrift β) a v
    (actualParisiFullMagnetization β a) (actualParisiFullMagnetization β (a+v))
    ((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable
    ((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable
    (fun x => (actualParisiFullMagnetization_curvature_bounds β a x).1)
    (fun x => (actualParisiFullMagnetization_curvature_bounds β (a+v) x).1)
    (actualParisiFullRestart_pre_mgf W β hβ a v hav) F A hF hA hF0 C D hC hD hFC hAD θ

end SKConstants

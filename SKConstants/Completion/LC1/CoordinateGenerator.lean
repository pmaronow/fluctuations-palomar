module

public import SKConstants.Completion.LC1.SignedFubini

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK.WeakIto
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

def actualCoordinateRate (β t y : ℝ) : ℝ :=
  actualParisiFullCurvature β t y +
    actualParisiFullMagnetization β t y * (actualParisiFullScalarDrift β).f t y

lemma measurable_actualCoordinateRate (β : ℝ) :
    Measurable (Function.uncurry (actualCoordinateRate β)) :=
  (continuous_actualParisiFullCurvature β).measurable.add
    ((continuous_actualParisiFullMagnetization β).measurable.mul (actualParisiFullScalarDrift β).measurable)

lemma actualCoordinateRate_abs_le (β t y : ℝ) : |actualCoordinateRate β t y| ≤ 2 := by
  have h := actualParisiFullMagnetization_curvature_bounds β t y
  have ha : |actualParisiFullCurvature β t y| ≤ 1 := by
    rw [abs_of_nonneg h.2.1]
    nlinarith [sq_nonneg (actualParisiFullMagnetization β t y)]
  have hb : |(actualParisiFullScalarDrift β).f t y| ≤ 1 :=
    (actualParisiFullScalarDrift β).bounded t y
  exact (abs_add_le _ _).trans (by
    rw [abs_mul]
    have hm := mul_le_mul h.1 hb (abs_nonneg _) zero_le_one
    norm_num at hm
    linarith)

lemma actualCoordinateRate_after_support (β : ℝ) (hβ : 1 < β) (t : ℝ≥0)
    (ht : parisiEquilibriumPhysicalEndpoint β ≤ t) (y : ℝ) : actualCoordinateRate β t y = 1 := by
  have ht' : β^2 * parisiEquilibriumSupportEndpoint β ≤ (t : ℝ) := by
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr ht
  rw [actualCoordinateRate, actualParisiFullCurvature_eq_tanh_after_support β hβ _ _ ht',
    actualParisiFullMagnetization_eq_tanh_after_support β hβ _ ht',
    actualParisiFullScalarDrift_eq_tanh_after_support β hβ _ ht']
  ring

def actualCoordinateResidual (β : ℝ) (a v : ℝ≥0)
    (p : ScalarContinuousPath a × ScalarContinuousPath v) : ℝ :=
  p.2 ⟨v,v.coe_nonneg,le_rfl⟩ *
      actualParisiFullMagnetization β (a+v) (p.2 ⟨v,v.coe_nonneg,le_rfl⟩) -
    p.1 ⟨a,a.coe_nonneg,le_rfl⟩ *
      actualParisiFullMagnetization β a (p.1 ⟨a,a.coe_nonneg,le_rfl⟩) -
    ∫ u in 0..(v:ℝ), actualCoordinateRate β (a+u.toNNReal)
      (IccExtend v.coe_nonneg p.2 u)

lemma measurable_actualCoordinateResidual (β : ℝ) (a v : ℝ≥0) :
    Measurable (actualCoordinateResidual β a v) := by
  have hr : Measurable (fun q : ℝ × (ScalarContinuousPath a × ScalarContinuousPath v) =>
      actualCoordinateRate β (a+q.1.toNNReal) (IccExtend v.coe_nonneg q.2.2 q.1)) := by
    have ht : Measurable (fun q : ℝ × (ScalarContinuousPath a × ScalarContinuousPath v) =>
        (a:ℝ) + (q.1.toNNReal:ℝ)) := measurable_const.add
      (measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst))
    have hx : Measurable (fun q : ℝ × (ScalarContinuousPath a × ScalarContinuousPath v) =>
        IccExtend v.coe_nonneg q.2.2 q.1) := (continuous_finitePath_extend v).measurable.comp
      ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
    simpa only [Function.comp_def, Function.uncurry_def] using
      (measurable_actualCoordinateRate β).comp (ht.prodMk hx)
  have hi := measurable_time_integral (Ω:=ScalarContinuousPath a × ScalarContinuousPath v)
    (f:=fun (u:ℝ) (p:ScalarContinuousPath a × ScalarContinuousPath v) =>
      actualCoordinateRate β (a+u.toNNReal) (IccExtend v.coe_nonneg p.2 u)) hr 0 v
  have hm (t : ℝ) : Measurable (actualParisiFullMagnetization β t) :=
    ((continuous_actualParisiFullMagnetization β).comp
      ((continuous_const : Continuous (fun _ : ℝ => t)).prodMk continuous_id)).measurable
  have hstart : Measurable (fun p : ScalarContinuousPath a × ScalarContinuousPath v =>
      p.1 ⟨a,a.coe_nonneg,le_rfl⟩) := (ContinuousMap.measurable_eval _).comp measurable_fst
  have hend : Measurable (fun p : ScalarContinuousPath a × ScalarContinuousPath v =>
      p.2 ⟨v,v.coe_nonneg,le_rfl⟩) := (ContinuousMap.measurable_eval _).comp measurable_snd
  exact ((hend.mul ((hm (a+v)).comp hend)).sub (hstart.mul ((hm a).comp hstart))).sub hi

lemma actualCoordinateResidual_fresh_version
    (W : BrownianSystem Ω) (β : ℝ) (a v : ℝ≥0) (past : ScalarContinuousPath a) :
    (fun w => actualCoordinateResidual β a v (past,
      boundedDriftRestartCallback (actualParisiFullScalarDrift β) a v
        (past,brownianFinitePath W v w))) =ᵐ[W.law]
    (fun w => actualParisiRestartField W β a (past ⟨a,a.coe_nonneg,le_rfl⟩) v w *
        actualParisiFullMagnetization β (a+v)
          (actualParisiRestartField W β a (past ⟨a,a.coe_nonneg,le_rfl⟩) v w) -
      past ⟨a,a.coe_nonneg,le_rfl⟩ * actualParisiFullMagnetization β a (past ⟨a,a.coe_nonneg,le_rfl⟩) -
      ∫ u in 0..(v:ℝ), actualCoordinateRate β (a+u.toNNReal)
        (actualParisiRestartField W β a (past ⟨a,a.coe_nonneg,le_rfl⟩) u.toNNReal w)) := by
  filter_upwards [boundedDriftRestartCallback_fresh_version W (actualParisiFullScalarDrift β) a v past]
    with w hw
  unfold actualCoordinateResidual
  rw [hw]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le v.coe_nonneg] at hu
  change actualCoordinateRate β (a+u.toNNReal)
    (boundedDriftRestartCallback (actualParisiFullScalarDrift β) a v
      (past,brownianFinitePath W v w) (projIcc 0 (v:ℝ) v.coe_nonneg u)) = _
  rw [projIcc_of_mem _ hu, hw]
  have huN : (⟨u,hu.1⟩:ℝ≥0) = u.toNNReal := by
    exact NNReal.coe_injective (Real.coe_toNNReal _ hu.1).symm
  rw [huN]
  rfl

lemma measurable_actualRestartField_real (W : BrownianSystem Ω) (β : ℝ) (a : ℝ≥0) (z : ℝ) :
    Measurable (fun p : ℝ × Ω => actualParisiRestartField W β a z p.1.toNNReal p.2) := by
  let b := SKConstants.BoundedLipschitzDrift.translated (actualParisiFullScalarDrift β) a z
  have hy : Measurable (fun p : ℝ≥0 × Ω => b.solution W.driver p.1 p.2) :=
    progressive_joint_measurable _ (b.solution_progressive _ W.driver_progressive)
  change Measurable (fun p : ℝ × Ω => z+b.solution W.driver p.1.toNNReal p.2)
  have hyReal : Measurable (fun p : ℝ × Ω => b.solution W.driver p.1.toNNReal p.2) :=
    by
      simpa only [Function.comp_def] using hy.comp
        ((measurable_real_toNNReal.comp (measurable_fst : Measurable (Prod.fst : ℝ × Ω → ℝ))).prodMk measurable_snd)
  exact measurable_const.add hyReal

lemma actualCoordinateResidual_fresh_mean
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (hside : a+v ≤ parisiEquilibriumPhysicalEndpoint β ∨ parisiEquilibriumPhysicalEndpoint β ≤ a)
    (past : ScalarContinuousPath a) :
    (∫ w, actualCoordinateResidual β a v (past,
      boundedDriftRestartCallback (actualParisiFullScalarDrift β) a v
        (past,brownianFinitePath W v w)) ∂W.law) = 0 := by
  let := W.isProbability
  let z := past ⟨a,a.coe_nonneg,le_rfl⟩
  let R := actualParisiRestartField W β a z
  have hr : Measurable (fun p : ℝ × Ω => actualCoordinateRate β (a+p.1.toNNReal) (R p.1.toNNReal p.2)) := by
    have ht : Measurable (fun p : ℝ × Ω => (a:ℝ) + (p.1.toNNReal:ℝ)) :=
      measurable_const.add (measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst))
    simpa only [Function.comp_def, Function.uncurry_def] using
      (measurable_actualCoordinateRate β).comp
        (ht.prodMk (measurable_actualRestartField_real W β a z))
  have hrBound (u : ℝ) (w : Ω) : |actualCoordinateRate β (a+u.toNNReal) (R u.toNNReal w)| ≤ (2 : ℝ≥0) :=
    actualCoordinateRate_abs_le β _ _
  have hiTime : Integrable (fun w => ∫ u in 0..(v:ℝ), actualCoordinateRate β (a+u.toNNReal) (R u.toNNReal w)) W.law := by
    apply Integrable.of_bound (measurable_time_integral (Ω:=Ω)
      (f:=fun u w => actualCoordinateRate β (a+u.toNNReal) (R u.toNNReal w)) hr 0 v).aestronglyMeasurable
      (2 * |(v:ℝ)|)
    exact ae_of_all _ (fun w => by
      simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
        (f:=fun u => actualCoordinateRate β (a+u.toNNReal) (R u.toNNReal w)) (C:=2)
        (a:=0) (b:=(v:ℝ))
        (fun u _ => by simpa only [Real.norm_eq_abs, NNReal.coe_ofNat] using hrBound u w))
  have hiR : Integrable (R v) W.law :=
    (integrable_const z).add ((SKConstants.BoundedLipschitzDrift.translated
      (actualParisiFullScalarDrift β) a z).solution_integrable W v)
  have hm : Measurable (fun w => actualParisiFullMagnetization β (a+v) (R v w)) := by
    have hR : Measurable (R v) := measurable_const.add
      ((SKConstants.BoundedLipschitzDrift.translated (actualParisiFullScalarDrift β) a z).solution_measurable W v)
    have hM : Measurable (actualParisiFullMagnetization β (a+v)) :=
      ((continuous_actualParisiFullMagnetization β).comp
        ((continuous_const : Continuous (fun _ : ℝ => ((a+v:ℝ≥0):ℝ))).prodMk continuous_id)).measurable
    exact hM.comp hR
  have hiCoord := hiR.mul_bdd hm.aestronglyMeasurable
    (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact
      (actualParisiFullMagnetization_curvature_bounds β (a+v) (R v w)).1))
  rw [integral_congr_ae (actualCoordinateResidual_fresh_version W β a v past)]
  change (∫ w, R v w * actualParisiFullMagnetization β (a+v) (R v w) -
    z * actualParisiFullMagnetization β a z -
    (∫ u in 0..(v:ℝ), actualCoordinateRate β (a+u.toNNReal) (R u.toNNReal w)) ∂W.law) = 0
  have hiSub : Integrable (fun w => R v w * actualParisiFullMagnetization β (a+v) (R v w) -
      z * actualParisiFullMagnetization β a z) W.law :=
    hiCoord.sub (integrable_const (z * actualParisiFullMagnetization β a z))
  rw [integral_sub (f:=fun w => R v w * actualParisiFullMagnetization β (a+v) (R v w) -
      z * actualParisiFullMagnetization β a z)
    (g:=fun w => ∫ u in 0..(v:ℝ), actualCoordinateRate β (a+u.toNNReal) (R u.toNNReal w)) hiSub hiTime]
  rw [integral_sub (f:=fun w => R v w * actualParisiFullMagnetization β (a+v) (R v w))
    (g:=fun _ => z * actualParisiFullMagnetization β a z) hiCoord
      (integrable_const (z * actualParisiFullMagnetization β a z)),
    integral_const, probReal_univ, one_smul,
    bounded_interval_expectation_swap W.law 0 v
      (fun u w => actualCoordinateRate β (a+u.toNNReal) (R u.toNNReal w)) hr 2 hrBound]
  have he : (∫ w, R v w * actualParisiFullMagnetization β (a+v) (R v w) ∂W.law) -
      z * actualParisiFullMagnetization β a z =
      ∫ u in 0..(v:ℝ), ∫ w, actualCoordinateRate β (a+u.toNNReal) (R u.toNNReal w) ∂W.law := by
    rcases hside with hpre | hpost
    · exact actualParisiFullProcess_pre_restartCoordinate_integral W β hβ a v hpre z
    · rw [actualParisiFullProcess_post_restartCoordinate_expectation W β hβ a v hpost z]
      have hRate : (∫ u in 0..(v:ℝ), ∫ w, actualCoordinateRate β (a+u.toNNReal) (R u.toNNReal w) ∂W.law) = (v:ℝ) := by
        calc
          _ = ∫ u in 0..(v:ℝ), (1:ℝ) := by
            apply intervalIntegral.integral_congr
            intro u hu
            apply (integral_congr_ae (ae_of_all _ (fun w =>
              actualCoordinateRate_after_support β hβ (a+u.toNNReal)
                (hpost.trans (le_add_of_nonneg_right bot_le)) (R u.toNNReal w)))).trans
            simp
          _ = _ := by simp
      exact hRate.symm
  exact sub_eq_zero.mpr he

end SKConstants.Completion.LC1

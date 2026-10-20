module

public import SKConstants.Completion.LC1.StieltjesCrossMoment

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

def boundedDriftRecoverBrownianPast (b : BoundedLipschitzDrift) (S : ℝ≥0)
    (p : ScalarContinuousPath S) (t : Iic S) : ℝ :=
  p ⟨t.1,t.1.coe_nonneg,NNReal.coe_le_coe.mpr t.2⟩ - p ⟨0,le_rfl,S.coe_nonneg⟩ -
    ∫ r in (0:ℝ)..(t.1:ℝ), b.f r.toNNReal (IccExtend S.coe_nonneg p r)

lemma measurable_boundedDriftRecoverBrownianPast (b : BoundedLipschitzDrift) (S : ℝ≥0) :
    Measurable (boundedDriftRecoverBrownianPast b S) := by
  have hr : Measurable (fun q : ℝ × ScalarContinuousPath S =>
      b.f q.1.toNNReal (IccExtend S.coe_nonneg q.2 q.1)) := by
    have ht : Measurable (fun q : ℝ × ScalarContinuousPath S => (q.1.toNNReal:ℝ)) :=
      measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst)
    have hx : Measurable (fun q : ℝ × ScalarContinuousPath S => IccExtend S.coe_nonneg q.2 q.1) :=
      (continuous_finitePath_extend S).measurable.comp (measurable_snd.prodMk measurable_fst)
    exact b.measurable.comp (ht.prodMk hx)
  apply Measurable.of_eval
  intro t
  have hi := measurable_time_integral (Ω:=ScalarContinuousPath S)
    (f:=fun r p => b.f r.toNNReal (IccExtend S.coe_nonneg p r)) hr 0 t.1
  exact ((ContinuousMap.measurable_eval _).sub (ContinuousMap.measurable_eval _)).sub hi

theorem boundedDriftRecoverBrownianPast_actual (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) (S : ℝ≥0) :
    (fun w => boundedDriftRecoverBrownianPast b S (boundedDriftPastPath W b S w)) =ᵐ[W.law]
      (fun w => fun t : Iic S => W.B t.1 w) := by
  filter_upwards [boundedDriftPastPath_version W b S,W.driver_indistinguishable,
    W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with w hp hd h0
  funext t
  unfold boundedDriftRecoverBrownianPast
  rw [hp,hp]
  have hi : (∫ r in (0:ℝ)..(t.1:ℝ), b.f r.toNNReal
      (IccExtend S.coe_nonneg (boundedDriftPastPath W b S w) r)) =
      ∫ r in (0:ℝ)..(t.1:ℝ), b.f r.toNNReal (b.solution W.driver r.toNNReal w) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le t.1.coe_nonneg] at hr
    have hrS : r ∈ Icc (0:ℝ) (S:ℝ) := ⟨hr.1,hr.2.trans (NNReal.coe_le_coe.mpr t.2)⟩
    change b.f r.toNNReal (boundedDriftPastPath W b S w (projIcc 0 (S:ℝ) S.coe_nonneg r)) = _
    rw [projIcc_of_mem _ hrS,hp]
    have hrN : (⟨r,hr.1⟩:ℝ≥0) = r.toNNReal := NNReal.coe_injective (Real.coe_toNNReal _ hr.1).symm
    rw [hrN]
  rw [hi]
  change b.solution W.driver t.1 w - b.solution W.driver 0 w -
    (∫ r in (0:ℝ)..(t.1:ℝ), b.f r.toNNReal (b.solution W.driver r.toNNReal w)) = W.B t.1 w
  rw [b.solution_eq _ W.driver_progressive t.1 w,
    b.solution_eq _ W.driver_progressive 0 w]
  simp only [NNReal.coe_zero,intervalIntegral.integral_same,add_zero]
  rw [hd,hd,h0]
  ring

theorem actualFullProcess_brownian_past_cross_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H)
    (F : (Iic S → ℝ) → ℝ) (hF : Measurable F) (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (fun t : Iic S => W.B t.1 w) * actualParisiMagnetizationObservable W β H w *
      (W.B T w-W.B S w) ∂W.law) =
    ∫ r in (S:ℝ)..(T:ℝ), ∫ w, F (fun t : Iic S => W.B t.1 w) *
      actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law := by
  let b := actualParisiFullScalarDrift β
  let G := F ∘ boundedDriftRecoverBrownianPast b S
  have hG : Measurable G := hF.comp (measurable_boundedDriftRecoverBrownianPast b S)
  have he : (fun w => G (boundedDriftPastPath W b S w)) =ᵐ[W.law]
      (fun w => F (fun t : Iic S => W.B t.1 w)) :=
    (boundedDriftRecoverBrownianPast_actual W b S).mono (fun w hw => congrArg F hw)
  have hh := actualFullProcess_terminal_brownian_cross_moment_test W β hβ S T H hST hTH G hG C (fun p => hFC _)
  refine (integral_congr_ae (he.symm.mono (fun w hw => congrArg
    (fun x : ℝ => x * actualParisiMagnetizationObservable W β H w * (W.B T w-W.B S w)) hw))).trans (hh.trans ?_)
  apply intervalIntegral.integral_congr
  intro r _
  exact integral_congr_ae (he.mono (fun w hw => congrArg (fun x : ℝ => x *
    actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w)) hw))

theorem actualFullProcess_brownian_past_stieltjes_cross_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (wgt : StieltjesFunction ℝ) (hwgt : Continuous wgt)
    (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H)
    (F : (Iic S → ℝ) → ℝ) (hF : Measurable F) (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (fun t : Iic S => W.B t.1 w) * actualParisiMagnetizationObservable W β H w *
      (scalarGlobalStieltjesWeightedProcess wgt W.driver T w -
        scalarGlobalStieltjesWeightedProcess wgt W.driver S w) ∂W.law) =
    ∫ r in (S:ℝ)..(T:ℝ), wgt r * (∫ w, F (fun t : Iic S => W.B t.1 w) *
      actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law) := by
  let b := actualParisiFullScalarDrift β
  let G := F ∘ boundedDriftRecoverBrownianPast b S
  have hG : Measurable G := hF.comp (measurable_boundedDriftRecoverBrownianPast b S)
  have he : (fun w => G (boundedDriftPastPath W b S w)) =ᵐ[W.law]
      (fun w => F (fun t : Iic S => W.B t.1 w)) :=
    (boundedDriftRecoverBrownianPast_actual W b S).mono (fun w hw => congrArg F hw)
  have hh := actualFullProcess_stieltjes_cross_moment_test W β hβ wgt hwgt S T H hST hTH G hG C (fun p => hFC _)
  refine (integral_congr_ae (he.symm.mono (fun w hw => congrArg (fun x : ℝ =>
    x * actualParisiMagnetizationObservable W β H w * (scalarGlobalStieltjesWeightedProcess wgt W.driver T w -
      scalarGlobalStieltjesWeightedProcess wgt W.driver S w)) hw))).trans (hh.trans ?_)
  apply intervalIntegral.integral_congr
  intro r _
  exact congrArg (fun x : ℝ => wgt r * x) (integral_congr_ae (he.mono (fun w hw => congrArg (fun x : ℝ => x *
    actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w)) hw)))

end SKConstants.Completion.LC1

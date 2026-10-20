module

public import SKConstants.Completion.LC1.BrownianCrossMoment

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
open SKConstantsOAI.ZeroTemperatureSK.WeakIto
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

def boundedDriftRecoveredIncrement (b : BoundedLipschitzDrift) (S T : ℝ≥0) (hST : S ≤ T)
    (p : ScalarContinuousPath T) : ℝ :=
  p ⟨T,T.coe_nonneg,le_rfl⟩ - p ⟨S,S.coe_nonneg,hST⟩ -
    ∫ r in (S:ℝ)..(T:ℝ), b.f r.toNNReal (IccExtend T.coe_nonneg p r)

lemma measurable_boundedDriftRecoveredIncrement (b : BoundedLipschitzDrift)
    (S T : ℝ≥0) (hST : S ≤ T) : Measurable (boundedDriftRecoveredIncrement b S T hST) := by
  have hg : Measurable (fun q : ℝ × ScalarContinuousPath T =>
      b.f q.1.toNNReal (IccExtend T.coe_nonneg q.2 q.1)) := by
    have ht : Measurable (fun q : ℝ × ScalarContinuousPath T => (q.1.toNNReal:ℝ)) :=
      measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst)
    have hx : Measurable (fun q : ℝ × ScalarContinuousPath T => IccExtend T.coe_nonneg q.2 q.1) :=
      (continuous_finitePath_extend T).measurable.comp (measurable_snd.prodMk measurable_fst)
    exact b.measurable.comp (ht.prodMk hx)
  have hi := measurable_time_integral (Ω:=ScalarContinuousPath T)
    (f:=fun r p => b.f r.toNNReal (IccExtend T.coe_nonneg p r)) hg S T
  exact ((ContinuousMap.measurable_eval _).sub (ContinuousMap.measurable_eval _)).sub hi

lemma boundedDriftRecoveredIncrement_actual (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (S T : ℝ≥0) (hST : S ≤ T) :
    (fun w => boundedDriftRecoveredIncrement b S T hST (boundedDriftPastPath W b T w)) =ᵐ[W.law]
      (fun w => W.B T w - W.B S w) := by
  have hsum : S+(T-S)=T := add_tsub_cancel_of_le hST
  have hsumR : (S:ℝ)+(T-S:ℝ≥0)=(T:ℝ) := by exact_mod_cast hsum
  have hinc := b.solution_increment W S (T-S)
  rw [hsum,hsumR] at hinc
  filter_upwards [boundedDriftPastPath_version W b T, hinc] with w hp hw
  unfold boundedDriftRecoveredIncrement
  rw [hp,hp]
  have hi : (∫ r in (S:ℝ)..(T:ℝ), b.f r.toNNReal
      (IccExtend T.coe_nonneg (boundedDriftPastPath W b T w) r)) = b.displacement W S T w := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (NNReal.coe_le_coe.mpr hST)] at hr
    have hr0 : 0 ≤ r := S.coe_nonneg.trans hr.1
    have hrT : r ∈ Icc (0:ℝ) (T:ℝ) := ⟨hr0,hr.2⟩
    change b.f r.toNNReal (boundedDriftPastPath W b T w (projIcc 0 (T:ℝ) T.coe_nonneg r)) = _
    rw [projIcc_of_mem _ hrT,hp]
    have hrN : (⟨r,hr0⟩:ℝ≥0) = r.toNNReal := NNReal.coe_injective (Real.coe_toNNReal _ hr0).symm
    rw [hrN]
    rfl
  rw [hi]
  change b.solution W.driver T w - b.solution W.driver S w - b.displacement W S T w = W.B T w - W.B S w
  linarith

theorem actualFullProcess_terminal_brownian_cross_moment_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T H : ℝ≥0)
    (hST : S ≤ T) (hTH : T ≤ H)
    (F : ScalarContinuousPath S → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w) *
      actualParisiMagnetizationObservable W β H w * (W.B T w - W.B S w) ∂W.law) =
    ∫ r in (S:ℝ)..(T:ℝ), ∫ w,
      F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w) *
        actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law := by
  let b := actualParisiFullScalarDrift β
  let P := boundedDriftPastPath W b S
  let G : ScalarContinuousPath T → ℝ := fun p => F (scalarContinuousPathRestrict S T hST p) *
    boundedDriftRecoveredIncrement b S T hST p
  have hG : Measurable G := (hF.comp (measurable_scalarContinuousPathRestrict S T hST)).mul
    (measurable_boundedDriftRecoveredIncrement b S T hST)
  have he : (fun w => G (boundedDriftPastPath W b T w)) =ᵐ[W.law]
      (fun w => F (P w) * (W.B T w - W.B S w)) := by
    filter_upwards [boundedDriftPastPath_restrict W b S T hST,
      boundedDriftRecoveredIncrement_actual W b S T hST] with w hr hb
    dsimp only [G]
    rw [hr,hb]
  have hi : Integrable (fun w => F (P w) * (W.B T w - W.B S w)) W.law := by
    apply ((W.brownian.integrable_eval T).sub (W.brownian.integrable_eval S)).bdd_mul
      (hF.comp (measurable_boundedDriftPastPath W b S)).aestronglyMeasurable
    exact ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hFC _)
  have hp := actualFullProcess_martingale_projection_integrable W β hβ T H hTH G hG (hi.congr he.symm)
  have hcm := actualFullProcess_brownian_cross_moment W β hβ S (T-S) F hF C hFC
  rw [add_tsub_cancel_of_le hST] at hcm
  have hEq (t : ℝ≥0) : (∫ w, F (P w) * actualParisiMagnetizationObservable W β t w *
      (W.B T w-W.B S w) ∂W.law) =
      ∫ w, G (boundedDriftPastPath W b T w) * actualParisiMagnetizationObservable W β t w ∂W.law := by
    apply integral_congr_ae
    filter_upwards [he] with w hw
    change G (boundedDriftPastPath W b T w) = F (P w) * (W.B T w-W.B S w) at hw
    rw [hw]
    ring
  exact (hEq H).trans (hp.trans ((hEq T).symm.trans hcm))

theorem actualFullProcess_terminal_brownian_cross_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T H : ℝ≥0)
    (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ w, actualParisiMagnetizationObservable W β H w * (W.B T w-W.B S w) ∂W.law) =
      ∫ r in (S:ℝ)..(T:ℝ), ∫ w, actualParisiFullCurvature β r.toNNReal
        (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law := by
  simpa only [one_mul] using actualFullProcess_terminal_brownian_cross_moment_test W β hβ S T H hST hTH
    (fun _ => (1:ℝ)) measurable_const 1 (fun _ => by norm_num)

end SKConstants.Completion.LC1

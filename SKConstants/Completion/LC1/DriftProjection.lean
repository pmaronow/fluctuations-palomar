module

public import SKConstants.Completion.LC1.CoordinateAll
public import SKConstants.Completion.LC1.MartingaleProjection

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actualFullProcess_drift_projection
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a c H : ℝ≥0)
    (hac : a ≤ c) (hcH : c ≤ H)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      (actualParisiFullScalarDrift β).f c (actualParisiFullScalarProcess W β c w) *
        actualParisiMagnetizationObservable W β H w ∂W.law) =
    ∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      (actualParisiFullScalarDrift β).f c (actualParisiFullScalarProcess W β c w) *
        actualParisiMagnetizationObservable W β c w ∂W.law := by
  let := W.isProbability
  let b := actualParisiFullScalarDrift β
  let G : ScalarContinuousPath c → ℝ := fun p => F (scalarContinuousPathRestrict a c hac p) *
    b.f c (p ⟨c,c.coe_nonneg,le_rfl⟩)
  have hd : Measurable (fun y : ℝ => b.f c y) :=
    b.measurable.comp ((measurable_const : Measurable (fun _ : ℝ => (c:ℝ))).prodMk measurable_id)
  have hG : Measurable G := (hF.comp (measurable_scalarContinuousPathRestrict a c hac)).mul
    (hd.comp (ContinuousMap.measurable_eval _))
  have hGB (p : ScalarContinuousPath c) : |G p| ≤ C := by
    have hb : |b.f c (p ⟨c,c.coe_nonneg,le_rfl⟩)| ≤ 1 := b.bounded _ _
    exact (abs_mul _ _).trans_le ((mul_le_mul (hFC _) hb (abs_nonneg _) C.coe_nonneg).trans_eq (mul_one _))
  have hGi : Integrable (fun w => G (boundedDriftPastPath W b c w)) W.law :=
    Integrable.of_bound (hG.comp (measurable_boundedDriftPastPath W b c)).aestronglyMeasurable C
      (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hGB _))
  have he : (fun w => G (boundedDriftPastPath W b c w)) =ᵐ[W.law]
      (fun w => F (boundedDriftPastPath W b a w) * b.f c (actualParisiFullScalarProcess W β c w)) := by
    filter_upwards [boundedDriftPastPath_restrict W b a c hac, boundedDriftPastPath_version W b c]
      with w hr hv
    dsimp only [G]
    rw [hr, hv]
    rfl
  have hEq (t : ℝ≥0) : (∫ w, G (boundedDriftPastPath W b c w) *
      actualParisiMagnetizationObservable W β t w ∂W.law) =
      ∫ w, F (boundedDriftPastPath W b a w) * b.f c (actualParisiFullScalarProcess W β c w) *
        actualParisiMagnetizationObservable W β t w ∂W.law :=
    integral_congr_ae (he.mono (fun w hw =>
      congrArg (fun x : ℝ => x * actualParisiMagnetizationObservable W β t w) hw))
  exact (hEq H).symm.trans ((actualFullProcess_martingale_projection_integrable W β hβ c H hcH G hG hGi).trans (hEq c))

theorem actualFullProcess_initial_coordinate_projection
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a H : ℝ≥0) (haH : a ≤ H)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      actualParisiFullScalarProcess W β a w * actualParisiMagnetizationObservable W β H w ∂W.law) =
    ∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      actualCoordinateObservable W β a w ∂W.law := by
  let b := actualParisiFullScalarDrift β
  let P := boundedDriftPastPath W b a
  let G : ScalarContinuousPath a → ℝ := fun p => F p * p ⟨a,a.coe_nonneg,le_rfl⟩
  have hG : Measurable G := hF.mul (ContinuousMap.measurable_eval _)
  have hf := hF.comp (measurable_boundedDriftPastPath W b a)
  have hi : Integrable (fun w => F (P w) * actualParisiFullScalarProcess W β a w) W.law := by
    apply (b.solution_integrable W a).bdd_mul hf.aestronglyMeasurable
    exact ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hFC _)
  have he : (fun w => G (P w)) =ᵐ[W.law]
      (fun w => F (P w) * actualParisiFullScalarProcess W β a w) := by
    filter_upwards [boundedDriftPastPath_version W b a] with w hw
    change F (P w) * _ = _
    rw [hw]
    rfl
  have hp := actualFullProcess_martingale_projection_integrable W β hβ a H haH G hG (hi.congr he.symm)
  calc
    _ = ∫ w, G (P w) * actualParisiMagnetizationObservable W β H w ∂W.law :=
      integral_congr_ae (he.symm.mono (fun w hw =>
        congrArg (fun x : ℝ => x * actualParisiMagnetizationObservable W β H w) hw))
    _ = ∫ w, G (P w) * actualParisiMagnetizationObservable W β a w ∂W.law := hp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [he] with w hw
      rw [hw]
      change F (P w) * actualParisiFullScalarProcess W β a w * actualParisiMagnetizationObservable W β a w =
        F (P w) * (actualParisiFullScalarProcess W β a w * actualParisiMagnetizationObservable W β a w)
      ring

end SKConstants.Completion.LC1
